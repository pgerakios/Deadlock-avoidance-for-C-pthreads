open Gc_stats
open Callg
open Scc
open Scc_cg
open Fstructs
open Cilinfos
open Stdutil
open Lvals
open Scope
open Fstructs
open Strutil

module D = Cildump
module PTA = Myptranal
module A = Alias
module H = Hashtbl

module E = Errormsg
module L = List
module CLV = Cil_lvals

include String

open Cil
open Printf

open Cfg
open Pretty
open Definitions
open Modsummary
open Effect_tools
open Effect_checks
open Effect_construct
open Effect_dataflow
open Trace


(******************************************************************* 
 *                      
 *									Create Function Hashes
 *	    (containing info and analysis results for every function) 
 *
 ******************************************************************)

(* Fill the functionHash (function id -> funStruct)  *)
let createFunctionHash f =
	let createFunctionHashAux global =
		match global with
		GFun (fundec, loc) ->
		let funInfo  = {
			fun_dec = ref fundec;
			funEffect = [];
			summary = [];
			has_effect = true;
      loopSet = IntSet.empty;
		  loopEffect = IntMap.empty;	
      has_malloc = false;
      fun_lock_count = SexpMap.empty;
      examined = false;
    }
		in
(* 			log "added `%s`\n" fundec.svar.vname; *)
			H.add  fun_to_funInfo (fundec.svar).vid funInfo
		| _ -> ()
	in
  dlog "Adding function hashes (info about analysis).\n";
  L.iter createFunctionHashAux f.globals


type peep_t = {
  mutable effect:bool; 
  mutable malloc:bool}  

let peep_f : peep_t ref = ref {effect=false; malloc=false;}

let resetPeep () =
    peep_f := {effect=false; malloc=false;}
    
(* Simple flow-insensitive visitor which checks if a function has an effect or
 * not. If there isn't, we avoid the dataflow (which costs more). *)
class peepEffectVisitor = object (self)
  inherit nopCilVisitor 

  method vinst (i:instr) = 
    match i with
    (* Check if this is a malloc site *)
    | Set (_,_,loc) -> 
        (if H.mem (getMalloc0 ()) loc then
          (*let _ = log "[%s] Found malloc.\n" (loc2strsmall loc) in*)
          peep_f :={effect=(!peep_f).malloc; malloc=true;});
        DoChildren
    
    | Call (lvo,e,_,loc) ->
        begin
          begin
            match e with          
            | Lval (Var vi, off) ->
                (* Found a lock/unlock operation *)
                if isFunLockOp vi.vname then
                  peep_f := {effect=true; malloc=(!peep_f).malloc;} 
            | _ -> ()
          end;
          let fids =
            match e with
            (* Direct call *)
            |	Lval(Var(callfn),_) ->
                [callfn.vid]
            (* Indirect Call *)
            | _ -> begin
                try
                  let strs = alias_map loc in
                  let vids = L.flatten (List.map (
                    fun s -> 
                      match varinfo_of_name s with
                      | Some vi -> [vi.vid]
                      | None -> []
                    ) strs)
                  in
                  dlog "[%s] PTA for `%s' returned:\n" 
                      (loc2strsmall loc) (exp2str e);
                  if L.length strs = 0 then 
                    dlog "\t<empty>\n"
                  else
                    L.iter (fun s -> dlog "\t%s\n" s) strs;
                  vids
                with Not_found -> 
                  let _ = warn "[%s] PTA resolve for `%s' returned \
                              \"Not_found\".\n"
                    (loc2strsmall loc) (exp2str e) in []
                end
          in
          let fid2peep id = 
            try 
              let fs = H.find fun_to_funInfo id in
              { effect = fs.has_effect;
                malloc = fs.has_malloc }
            with Not_found ->
            (* Not declared in the sources, we assume they don't 
             * produce effects. *)
              !peep_f
          in
          let curr =
            L.fold_left (
              fun feed p -> 
                { effect = feed.effect || p.effect;
                  malloc = feed.malloc || p.malloc; }
              ) {effect=false; malloc=false} (L.map fid2peep fids) in
          peep_f := 
            { effect = (!peep_f).effect || curr.effect;
              malloc = (!peep_f).malloc || curr.malloc; };              
          DoChildren        
        end
    | _ -> DoChildren
end

let peepEffect fn =
  resetPeep ();
  let vis = new peepEffectVisitor in 
  ignore(visitCilFunction vis fn);
  try
    let fs = H.find fun_to_funInfo fn.svar.vid in
    fs.has_malloc <- (!peep_f).malloc;
    fs.has_effect <- (!peep_f).effect;
    (*log "This function has malloc: %b, effect: %b.\n"
    fs.has_malloc fs.has_effect*)
  with Not_found -> ()



(* ceFromFundec: collects continuation effect (set of lock operations as expr) 
 * based on control flow info from function with name funName.
 *)
let ceFromFundec (fd : fundec) (funStruct : funInfoType) : unit =
  cur_fstruct := funStruct;
  peepEffect fd;

  let curSCC = getCurrSCC () in
  let isRecursive = (Callg.FSet.cardinal curSCC.scc_nodes > 1) in
  (*let (rettyp,_,_,_) = splitFunctionType fd.svar.vtype in
  log "The function returns: %s which contains lock: %b.\n"
    (typ2str rettyp) (typeContainsLock rettyp);*)
  
  (* Check a function that has effect or mallocs, or is recursive, and so
   * we need to determine if there is an effect or not. *)
  if not (hasErrors ()) && 
    (funStruct.has_effect || funStruct.has_malloc || isRecursive) then
    begin         
      log "\n%sAnalyzing function `%s' (decl.: %s) (vid:%d) \n"
        thick_line fd.svar.vname (loc2strsmall fd.svar.vdecl) fd.svar.vid; 
      log "%s" line;
      (*log "This func's scc (rec: %b) " isRecursive;
      Callg.FSet.iter (fun (k,_) -> log "%d " k) curSCC.scc_nodes;
      log "\n";*)
      (** End of Pretty printing *)

      (* Initializing the mapping from arguments to offset mappings *)
      arg_map := IntMap.empty;
      assign_off := 0;
      (* Clear message buffer *)
      clear_error_set ();
      clear_info_set ();

      (* Reset sanity check *)
      Sanity.reset ();
      
      (* Initialize Dataflow *)
      initializeDF fd.svar.vid fd;

      (* Compute the function's effect *)
      computeFunEffect ();

      (* Get the result *)
      let funSt = getOutState () in
      let funEff = funSt.outEff in

    (* Compute the assign eifect of the function. This must be done before
     * optimizations on the effect. Run in this order. *)
      let a_effect  = make_assign_effect funEff in
      (*print_assign_effect a_effect fname;*)
      let a_summary = compute_assign_state a_effect in
      (*let m_effect  = comp_mal_eff a_effect in*)

      (*print_assign_summary a_summary fd.svar.vname;*)
      (*print_malloc_map_ass ();*)
      cur_assign_eff := a_effect;
      cur_assign_sum := a_summary;
      (*cur_malloc_eff := m_effect;*)

      let remassEff = remove_assign funEff in
      let cleanedEff = fixInline remassEff in
      let backpatchedEff = backpatch cleanedEff in
      let finalEff = fixInline backpatchedEff in
      
      (*print_effect funEff;*)
      funStruct.funEffect <- finalEff;
      let f_map = fillEffMap SexpMap.empty finalEff in
      funStruct.fun_lock_count <- f_map;      
      if isRecursive && (nonEmptyEffect funStruct.funEffect) then
        warn "This is a recursive function bearing a non-empty effect.\n";
      
      Sanity.check_sanity finalEff;

  (* If this is a root function, its count should be zero. *)
      if IntSet.mem fd.svar.vid !rootFuns then
        SexpMap.iter (
          fun s n -> 
            if n > 0 then 
              err "`%s' is a root function.\n All lock count should have an \
              aggregate of zero.\n `%s' has counts: %d\n" fd.svar.vname
              (sexp2strsmall s) n
        ) f_map;
    


      (*log "%s\nOUTPUT LOCK COUNTS:\n" line;
      print_count_map f_map;*)

      let summary = summarize finalEff in

      printDotFile fd;
      funStruct.summary <- summary

    end
  else
    begin
      funStruct.funEffect <- [];
      funStruct.fun_lock_count <- SexpMap.empty
    end
