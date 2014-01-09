open Cil
open Lvals
open Modsummaryi
open Strutil
open Pretty
open Definitions
open Scope
open Callg

module CLV = Cil_lvals
module TA = Trans_alloc


(*************************************************************************** 
 *                     
 *											Mallloc analysis definitions
 *
 ***************************************************************************)

type alias_map = (Cil.location,string list) H.t
type cg_alias_map = (Cil.prog_point,string list) H.t
(* the boolean is whether it contains a lock or not *)
type malloc_map = (location, string * string *  bool * varinfo) H.t
type malloc_map_inv = (string, location * string * bool * varinfo) H.t
type malloc_bin_type = (malloc_map * malloc_map_inv * alias_map * cg_alias_map)

(* Contains the malloced global variables substituted in the context
 * of the caller function. *)
type malloc_map_assign = (ctx, (string * varinfo)) H.t
(* The integer is the index in the function's malloc effect - 
 * needed to find the correct offset in the malloc's array. *)
type malloc_map_assign_inv = (string, ctx * int) H.t

(* This will be used for malloced locks. The first is the allocation
 * and the second the deallocation (free). *)
type scope = (Cil.location * Cil.location option)

(*******************************************************)

let alias_map0  = ref (None:alias_map option)
let cg_alias_map0  = ref (None:alias_map option)

let malloc_map0 = ref (None : malloc_map option)
let malloc_map1 = ref (None : malloc_map_inv option)

let malloc_map_assign0 : malloc_map_assign = H.create 50
let malloc_map_assign1 : malloc_map_assign_inv = H.create 50

let free_map : (Cil.location, Cil.exp) H.t = H.create 50


let loadFunAlias ()  = (*should be invoked at init*)
  let fname = Filename.concat !cgDir "alias.bin" in
  let ic = open_in fname in
  (* Load hashtables with malloced variables and fp results. *)
  let (m0, m1, f, fcg) = (Marshal.from_channel ic : malloc_bin_type) in
  malloc_map0 := Some m0;
  malloc_map1 := Some m1;
  alias_map0 := Some f;
  callg_alias := fcg;
  close_in ic

let alias_map loc = 
 begin try H.find (opt2some !alias_map0) loc
 with Not_found -> [] end

let getMalloc0 () : malloc_map = 
  opt2some !malloc_map0

let getMalloc1 () : malloc_map_inv = 
  opt2some !malloc_map1

let is_malloc_global name = 
 H.mem (getMalloc1 ()) name

(* These mapping will be needed to correspond a variable that is an offset of an
 * argument of the function *)

(* we need:
 *  - Map: argument |-> Offset Mapping
 *  - Offset Mapping: offset |-> integer
 *  the last integer will be used as an offset in the locals array
 *  *)
type off_map_t = int OffMap.t
type off_map_inv_t = (offset * exp) IntMap.t
type dbl_off_map_t = off_map_t * off_map_inv_t

let arg_map : (dbl_off_map_t IntMap.t) ref = ref IntMap.empty

let assign_off : int ref = ref 0



(* Checks if the lock is passed as an argument to the function, and returns
 * the argument's index and the lock's offset in the struct. *)
let stack_index sform vi ((off, exp) : (offset * exp))  : (int * int) = 
  let rec stack_index_aux i sf : int =
    match sf with
    | [] -> begin
        error_set := StringSet.add
          ("["^(loc2strsmall !call_loc)^"] Operation on `"^(exp2str exp)
          ^"' uninstantiatted local lock.\n") !error_set;
        (-1)
      end
    | (svi::stl) -> 
      begin
        if svi.vid = vi.vid then
          i
        else if typeContainsLock svi.vtype then
        (* only count the arguments that are/contain lock handles *)
          stack_index_aux (i+1) stl
        else 
          stack_index_aux i stl
      end
  in
  let arg_ind = stack_index_aux 0 sform in
  let (this_off_map, this_off_map_inv) = 
    try IntMap.find arg_ind !arg_map 
    (*log "This is the offMap:\n";
    OffMap.iter (
      fun o i -> 
        log "%s -> %d\n" (off2str o) i) !tom;*)
    with Not_found ->
      (OffMap.empty, IntMap.empty)
  in
  let off_ind = 
    try
      OffMap.find off this_off_map
    with Not_found -> 
      begin
        let this_off_map' = OffMap.add off !assign_off this_off_map in
        let this_off_map_inv' = IntMap.add !assign_off (off, exp)
                                  this_off_map_inv in
        arg_map := IntMap.add arg_ind
          (this_off_map', this_off_map_inv') !arg_map;        
        let ret = !assign_off in
        assign_off := !assign_off + 1;
        ret        
      end
  in  
  (arg_ind, off_ind)

let getMemoryType s =

  let exp = sexp2exp s in
  let map_off_exp = (getOffset exp, exp) in
  (*let _ = log "[%s] Expression: %s , Offset %s\n"
    (loc2strsmall !call_loc)
    (exp2str exp) (off2str (fst(map_off_exp))) in*)

  let saddr (s:sexp) = 
    match s with
    | SAddrOf s'  -> 
        (*let _ = log "SAddr %s\n" (sexp2strsmall s') in*)
        (s',true)
    | _           -> (s,false)
  in
(*  
  let sderef (s:sexp) = 
    match s with
    | SDeref (s',off) ->
        let e' = sexp2exp s' in
        let t' = unrollType (Cil.typeOf e') in
        (*let _ = log "SDeref %s, off: %s, typ: %s\n" 
            (exp2str e') (off2str off) (typ2str t') in*)
        (s',t',off,true)
    | _               -> 
        let e = sexp2exp s in
        let t = unrollType (Cil.typeOf e) in
        (s,t,NoOffset,false)
  in
*)
  (** is_handle: true if the locked expression is a lock handle (not a pointer)
   *  derefed: true if dereferencing is needed
   *)
  let rec getMemoryTypeAux 
      (is_handle:bool)
      (offset:offset)
      (deref_level:int)
      (s:sexp) 
      (st:typ): mem_t =
    
    match s with
    | SVar ((fd, vi),off) ->
        (*let _ = log "SVar %s, off: %s\n" vi.vname (off2str off) in*)
        let orig_off = fst map_off_exp in        
        let (oB, w) = Cil.bitsOffset st orig_off in
        let ob = oB/8 in (* offset is in bits *)
    
        let mm1 = getMalloc1 () in
        let mm2 = malloc_map_assign1 in
        begin
          try 
            let (loc,_,_,_) = H.find mm1 vi.vname in
            Heap (ob,[loc])
          with Not_found -> begin
            try 
              let (ctx,_) = H.find mm2 vi.vname in
              Heap (ob,ctx)
            with Not_found ->
              (* we cannot use base.offset when initializing an effect
               * because base might be defined in another file. *)
              let base_lval = (Var vi, NoOffset) in
              if vi.vglob then
                (*let _ = log "Finding offset of: %s in type %s.\n" 
                  (off2str offset) (typ2str t') in*)
                if deref_level > 1 then begin
                  unimp "Only support one level of dereference.\n";
                  Stack (-1)
                end
                else
                  let t2 = 
                    if deref_level > 0 then
                      match st with 
                      | TPtr (typ,_) -> typ
                      (* Sanity check *)
                      | _ -> rs_impossible "Derefing a non pointer type."
                    else st
                  in
                  let t1 = unrollType vi.vtype in
                  let oB1 = bitsOffset t1 off in
                  let ob1 = (fst oB1)/8 in
                  let oB2 = bitsOffset t2 offset in
                  let ob2 = (fst oB2)/8 in
                  Global (base_lval,deref_level>0,is_handle,ob1,ob2)
              else
                let ind = snd(stack_index fd.sformals vi map_off_exp) in
                Stack ind
          end
        end
    | SInst   _ -> rs_impossible "getMemoryType/SInst"
    | SAddrOf _ -> rs_impossible "getMemoryType/SAddrOf"
    | SDeref (s',off) ->
        let e' = sexp2exp s' in
        let t' = unrollType (Cil.typeOf e') in
        (*let _ = log "SDeref %s, off: %s, typ: %s\n" 
            (exp2str e') (off2str off) (typ2str t') in*)
        getMemoryTypeAux is_handle off (deref_level+1) s' t'
    | SBot  _ -> rs_impossible "getMemoryType/SBot"
    | SAbsHost  _ -> rs_impossible "getMemoryType/SAbsHost"
  in
  let (s',is_handle) = saddr s in
  (*let e = sexp2exp s' in
  let _ = log "About to: %s\n" (exp2str e) in*)
  let t = unrollType (typeOfSexp s') in
  (*let _ = log "Unrolled: %s\n" (typ2str t) in*)
  (*let (s'',t,off,is_deref) = sderef s' in*)
  getMemoryTypeAux is_handle NoOffset 0  s' t


(*************************************************************************** 
 *
 *                Computation of the Assignment Effect
 *
 ***************************************************************************)

let getScopeALv (alval:Lvals.aLval) = 
  Scope.decideScopeVar !curFunc 
  (Lvals.findBaseVarinfoLval alval) 

let getScopeLv (lval:Cil.lval) = 
  getScopeALv (abs_of_lval lval)

let getScopeExp (exp:Cil.exp) (fd:Cil.fundec)=
  let bvi = CLV.findBaseVarinfoExp exp in
  Scope.decideScopeVar fd bvi

let create_ctx_str ctx =
  List.fold_right (
    fun loc f ->
      f ^ "_" ^ 
      (TA.nameFile loc.file) ^ "_" ^ (TA.nameByte loc.line)
      (*TODO : change line to byte *)
  ) ctx "_B"

let getTypFromHash ctx = 
  try
    begin
      let assign_loc = (List.hd (List.rev ctx)) in
      try
        let (_,_,_,vi) = H.find (getMalloc0 ()) assign_loc in
        vi.vtype
      with Not_found -> 
        let (_,vi) = H.find malloc_map_assign0 ctx in
        vi.vtype
    end
  with Not_found -> rs_impossible "getTypFromHash"

let get_malloced_ctx vi : ctx = 
  try
    let (loc,_,_,_) = H.find (getMalloc1 ()) vi.vname in [loc]
  with Not_found ->
    try
      fst(H.find malloc_map_assign1 vi.vname)
    with Not_found -> 
      begin
        (*log "get_malloced_ctx: `%s' not found\n" vi.vname;*)
        raise Not_found
      end
      

let rec subst_lval lv ci = 
  let (call_loc,_,de_loc,vi,el) = ci in
  (*let _ = log "Call to function: %s.\n" vi.vname in
  let _ = log "[%s] Before substLval %s\n" 
    (loc2strsmall call_loc) (lval2str lv) in*)
  let alv' = SPTA2.substLval el (Lvals.abs_of_lval lv) in
  let lv' = lval_of_abs_simple alv' in
(*  let _ = log "     After substLval %s\n" (string_of_lval alv') in*)
  match lv' with
  | (Var vi,off) ->            
      begin
      try
        let ctx = get_malloced_ctx vi in 
        (*log "subst_lval: found ctx = %s\n" (ctx2str ctx);*)
        let ctx' = call_loc::ctx in
        (* If this is a malloc expression, 
         * we need to update the name. *)
        let (_,vi') = H.find malloc_map_assign0 ctx' in
        (*log "subst_lval: Adding to malloc_map_assign0: %s -> %s\n" 
          vi.vname vi'.vname;*)
        (Var vi', off)
        (* If this is not a malloced expression,
         * we return it as is. *)
      with Not_found -> lv'
      end
  | (Mem exp, off) ->
(*PV: had made change here: lv' *)

      (*let _ = log "Mem %s, off %s\n" (exp2str exp) (off2str off) in*)
      (*let subexp = subst_exp ci (Some exp) in
      (Mem (opt2some subexp),off)*)
      lv'

and subst_exp ci (expo:Cil.exp option) : Cil.exp option =  
  (*let (loc,pp,_,vi,el) = ci in*)
  match expo with 
  | Some exp -> 
    begin
      (*let (must,elist) = 
        SPTA2.getAliasesAtExp pp (Lvals.abs_of_exp exp) in
      let is_singleton = (List.length elist = 1) in
      if must && is_singleton then
        let e = (exp_of_abs_simple (List.hd elist)) in
        let _ = log "Substing_0: %s\n" (exp2str e) in            
        try
          let se = exp_of_abs_simple
            (SPTA2.mySubstExp el (Lvals.abs_of_exp e)) in
          let _ = log "Substed: %s\n" (exp2str se) in*)
        match exp with
        | AddrOf lval ->               
            (*let _ = log "Addr\n" in*)
            Some (AddrOf (subst_lval lval ci))
        | Lval lval -> 
            (*let _ = log "Lval %s\n" (lval2str lval) in*)
            Some (Lval (subst_lval lval ci))
        | _ -> let _ = log "ERROR\n" in Some exp

        (*with 
          | Cil_lvals.SubstInvalidArg ->
            err "[%s] Trying to substitute an uninstantiated value: `%s'.\n\
              Analysis will fail.\n" (loc2strsmall loc) (exp2str exp); None
          | Failure("nth") -> 
            (*log "El: ";L.iter (fun e -> log "%s " (exp2str e)) el;log "\n";*)
            err "[%s, calling %d] Failure in matching formal with real \
                parameters while substituting expression `%s'.\n\
                Analysis will fail.\n" (loc2strsmall loc) vi.vid (exp2str e);
              None
        
      else begin
        err "[%s] Aliasing problem with expression `%s'.\n\
            Analysis will fail.\n" (exp2str exp) (loc2strsmall loc); None
      end*)
    end
  | _ -> None

   
(* Substitutes assignment done in callee function. 
 * ci: the calling context
 * a: the assigment *)
let subst_assign  ((call_loc, pp, _, _, el) as ci)
                  ((lv,sc1),(e,sc2),ctx) = 
  let new_ctx = call_loc :: ctx in
  let lv' = subst_lval lv ci in
  let sc1' = getScopeLv lv' in
  let e' = subst_exp ci e in
  match e' with 
  | Some exp ->
    let bvi = CLV.findBaseVarinfoExp exp in
    let sc2' = Scope.decideScopeVar !curFunc bvi in
        ((lv', sc1'), (e', sc2'), new_ctx)
  | _ -> ((lv', sc1'), (None, STBD), new_ctx)        



let print_ass_subst_list l ci = 
  let (loc,_,_,_,_) = ci in
  if l <> [] then begin
    log "[%s] Prior ass sum:\n" (loc2strsmall loc);
    List.iter (fun ((lv, s1),(e,s2),ctx) -> 
      log  "%s (%s) <- %s (%s) [%s]\n"
      (lval2str lv) (scope2str s1) (exp2str e)
      (scope2str s2) (ctx2str ctx)
    ) l;
    log "%s" line;
  end

(* Substitute an assignment summary into a calling context *)  
let subst_assign_sum af callinfo = 
  (* Do your best to figure out the assignment, but 
   * don't crash if something goes wrong. *)
  L.fold_left (
    fun feed a -> 
      try feed@[subst_assign callinfo a]
      with _ -> feed
  ) [] af


let print_malloc_map_ass _ = 
  log "Printing malloc map assign:\n";
  H.iter (
    fun ctx (s,vi) -> 
      log "  %s --> %s\n" (ctx2str ctx) s
  ) malloc_map_assign0;
  log "-----------------------------\n\n"


class mySummary = object (self)
  inherit Modsummaryi.absModSumm as super
  val mutable file_opt = (None : Cil.file option)
  (* hashtable that keeps summaries of functions *)
  val funsum : (int, assign_state) H.t = H.create 117
  val funeff : (int, assign_effect) H.t = H.create 117  
  val maleff : (int, malloc_effect) H.t = H.create 117
  val malmap : (int, int StringMap.t) H.t = H.create 117
  val retmap : (int, exp list) H.t = H.create 117
  
  method setFile f = file_opt <- Some f 
  method printStuff sumKey = 
   try
      let vi = Cilinfos.getVarinfo 
        (SK.fkey_of_sumKey sumKey) in
      log "mySummary object : getMods: %s => "
      (varinfo2str vi)
   with _ ->
      log "mySummary object Exception => "

  method printSummary sl = 
    if List.length sl > 0 then begin
      log "Printing summary:\n";      
      List.iter (fun (lv, sc) -> 
        log "lv: %s , scope: %s, type: %s\n" (alval2str lv) (scope2str sc)
        (typ2str (typeOfLvalUnsafe lv))
      ) sl;
      log "%s" line
    end

  method printMySummary sl = 
    if List.length sl > 0 then begin
      log "Printing MySummary:\n";      
      List.iter (fun ((lv, s1),(e,s2),ctx) -> 
        log  "%s (%s) <- %s (%s) [%s]\n"
        (lval2str lv) (scope2str s1)
        (match e with Some ex -> exp2str ex | _ -> "Top")
        (scope2str s2) (ctx2str ctx)
      ) sl;
      log "%s" line
    end

    (* inserts the summary to a function by its id *)
	method setSummary sumKey (s: assign_state) : unit =
    (* Remove STBD from summary (they cause failures later on). These
     * are mainly used for local assignments - not interested in them. *)
    let s' = (*List.filter (fun (_,sc) -> not(sc = STBD))*) s in
  	H.replace funsum (SK.fkey_of_sumKey sumKey) s'

  (* inserts the assign effect to a function by its id *)
	method setEffect sumKey (e: assign_effect) : unit =
  	H.replace funeff (SK.fkey_of_sumKey sumKey) e

  (* inserts the malloc effect to a function by its id *)
	method setMalEff sumKey (e: malloc_effect) : unit =
  	H.replace maleff (SK.fkey_of_sumKey sumKey) e

  (* inserts the malloc mapping to a function by its id *)
	method setMalMap sumKey (e: int StringMap.t) : unit =
  	H.replace malmap (SK.fkey_of_sumKey sumKey) e
   
  (* set the returing value(s) of the function - keep the list of
   * possible aliases, as we might not be interested in them 
   * finally *)
  method setRetExps sumKey (v: exp list) : unit =
    H.replace retmap (SK.fkey_of_sumKey sumKey) v


	(* return the summary for a given function id *)
	method getMods sumKey : assign_state = 
		match absFind H.find funsum (SK.fkey_of_sumKey sumKey)  with
		| Some s -> s
    | None -> []

	(* return the summary for a given function id substituted 
   * in the callinfo context *)
  method getModsCtx sumKey callinfo : assign_state = 
    let mods = self#getMods sumKey in
    subst_assign_sum mods callinfo

	(* return the effect for a given function id *)
	method getEffect sumKey : assign_effect = 
		match absFind H.find funeff (SK.fkey_of_sumKey sumKey)  with
		| Some s -> s
    | None -> []

  (* return the malloc effect for a given function id *)
  method getMalEff sumKey : malloc_effect = 
		match absFind H.find maleff (SK.fkey_of_sumKey sumKey)  with
		| Some s -> s
    | None -> []
  
  (* return a mapping from every malloc abstract location to the 
   * index of the local malloc function - used to find the 
   * correspondence with the correct entry in the hashtable 
   * at runtime.*)
	method getMalMap sumKey : int StringMap.t = 
		match absFind H.find malmap (SK.fkey_of_sumKey sumKey)  with
		| Some s -> s
    | None -> StringMap.empty

  (* returns the value that is returned by a function translated 
   * to the callers environment. *)
	method getRetExps sumKey ci : (exp option) list =
		match absFind H.find retmap (SK.fkey_of_sumKey sumKey)  with
    | Some s -> begin 
        (* Warning: will only return expressions that are/contain locks*)
        (*L.iter (fun e -> log "Reting: %s (%s)\n"
        (exp2str e) (typ2str (Cil.typeOf e))) s;*)
        let ret = (*List.filter (fun e -> typeContainsLock (Cil.typeOf e))*) s in
        let someret = List.map (fun e -> Some e ) ret in
        let sret = (*L.map (subst_exp ci) someret*)
          L.fold_left 
            (fun feed sr ->
              (* try to resolve the returning value, but don't crash if 
                * you don't *)
              try (subst_exp ci sr)::feed
              with _ -> 
                let _ = 
                  if typeContainsLock (Cil.typeOf (opt2some sr)) then
                    err "BUG.\n" in
                feed
            ) [] someret
        in
        (*log "Finished with getRetExps.\n";*)
        sret

        end
    | None -> []

end

let sum = new mySummary

(* This is a hashtable that keeps track of the order in which the malloc
 * operations appear in a function. This is necessary because the way we compute
 * the assignment effect, there is no guarantee that the mallocs are in the
 * correct order. *)
let aa_mal_hash : (string,int) H.t = H.create 30

let mall_eff : malloc_effect ref = ref []

(* Simple visitor that fills up the malloc map with the locations that are being
 * malloced, taking into consideration the context from where the malloc()
 * function is called. *)
class fillMalVisitor = object (self) inherit nopCilVisitor
val mutable counter = 0

method vinst i = 
  match i with
  | Call(lvo, e, el, loc) ->
    begin
      match e with
      (* Direct call *)
      |	Lval (Var fvi,_) -> 
          let mcs = sum#getMalEff (fvi.vid,fvi.vname) in
          let ret_eff = List.map (
            fun (vi0,_,ctx) -> 
              let ctx' = loc::ctx in
              let ctx_str = create_ctx_str ctx' in
              let vi = CLV.mkVarinfo true ctx_str vi0.vtype in
              if not ( H.mem aa_mal_hash vi.vname ) then
                begin
                  (*log "--> %d : %s\n" counter vi.vname;*)
                  H.add aa_mal_hash vi.vname counter;
                  counter <- counter + 1;
                end;
              H.replace malloc_map_assign1 ctx_str (ctx',-1);
              H.replace malloc_map_assign0 ctx' (ctx_str,vi);
              (vi,counter-1,ctx')
          ) mcs
          in
          mall_eff := !mall_eff @ ret_eff
      | _ -> ()
    end;
    DoChildren
  | Set (_,AddrOf (Var vi,_),loc) -> 
      if H.mem (getMalloc1 ()) vi.vname then begin
        if not ( H.mem aa_mal_hash vi.vname ) then
        begin
          (* We want the first occurence *)
          H.add aa_mal_hash vi.vname counter;
          mall_eff := !mall_eff @ [(vi,counter,[loc])];
          counter <- counter + 1
        end;
      end;
      DoChildren
  (* TODO : indirect calls *)
  | _ -> DoChildren  

end

let fillMallocHash fd = 
  H.clear aa_mal_hash;
  mall_eff := [];
  ignore(visitCilFunction (new fillMalVisitor) fd);
  (sum#setMalEff) (fd.svar.vid,fd.svar.vname) !mall_eff
  (*log "New Malloc Effect:\n";
  List.iter (
    fun (vi,cnt,ctx) ->
      log "  [%s] %s. %s\n" (ctx2str ctx) (string_of_int cnt) (vi.vname)
  ) !mall_eff;
  log "---------------------------------\n"*)


let cur_ret_sum = ref []
let cur_fundec_ret = ref dummyFunDec
(* Visitor that fill the return expression information for every function. *)
class returnVisitor = object (self) inherit nopCilVisitor
method vstmt s = 
  begin
    match s.skind with
    | Return (Some e, loc) ->
        let get_aliases ae = snd(SPTA2.getAliasesAtExit !cur_fundec_ret ae) in
        let aelist = get_aliases (Lvals.abs_of_exp e) in
        (*let _ = List.iter (fun aexp -> log "ret: %s, %s\n" 
          (exp2str e) (Lvals.string_of_exp aexp)) aelist in*)
        let exlist = List.concat (List.map (
          fun ae ->
            try [exp_of_abs_simple ae]
            with Lvals.IsAbstract -> []
          ) aelist) in
        cur_ret_sum := exlist @ (!cur_ret_sum)
    | _ -> ()
  end;
  DoChildren
  
end

let fillReturnSum fd = 
  let sk = (fd.svar.vid,fd.svar.vname) in
  cur_fundec_ret := fd;
  sum#setRetExps sk [];
  ignore(visitCilFunction (new returnVisitor) fd);
  sum#setRetExps sk !cur_ret_sum;
  (*if !cur_ret_sum <> [] then
    (log "Returning:\n";
    List.iter (fun e -> log "  %s\n" (exp2str e)) !cur_ret_sum);*)
  cur_ret_sum := []


let cur_assign_sum : assign_state ref = ref []
let cur_assign_eff : assign_effect ref = ref []
let cur_malloc_eff : malloc_effect ref = ref []
(*let cur_malloc_map : (int StringMap.t) ref = ref StringMap.empty*)

let d_assign_sum () (a_sum: assign_state) = 
  dprintf "%a" 
    (d_list "\n"
      (fun () ((lv,s1),(e,s2),ctx) ->
        dprintf "%s (%s) <- %s (%s) [%s]"
        (lval2str lv) (scope2str s1)
        (match e with Some ex -> exp2str ex | _ -> "Top")
        (scope2str s2) (ctx2str ctx)))
      a_sum

let asum2str = any2str d_assign_sum

let print_assign_summary (a_sum: assign_state) name = 
  if (!enable_log) then 
    if List.length a_sum > 0 then begin
      log "%sAssignment summary of function %s:\n\n" line name;
      log "%s" (asum2str a_sum);
      log "\n%s" line
    end

(* Output assign effect in terminal *)
let rec d_assignOp () (a : assign_atomic_t) : Pretty.doc =
	match a with
	| AAssign ((l,s1),(e,s2),ctx) ->
      dprintf "[%s] %s (%s) := %s(%s)" (ctx2str ctx)
      (lval2str l) (scope2str s1) 
      (match e with Some ex -> exp2str ex | _ -> "Top")
      (scope2str s2)
  | AJoin al -> dprintf "{\n  @[(%a)\n@]}"
					(d_list ") ?\n(" ( d_list "\n" d_assignOp))  al	
	| ACall ((l,_,_,vi,_), callSt) -> 
      dprintf "[%s]@[%s(...)\n%s@]" (loc2strsmall l)
        (vi.vname) (asum2str callSt)

let d_assign_effect () (e : assign_effect) = 
	Pretty.dprintf "\n%a\n\n" 
		(d_list "\n" d_assignOp) e

(* Print the assignment effect of a function. *)
let print_assign_effect (a_effect: assign_effect) name = 
  if (!enable_log) then begin
    log "%sAssignment effect of function %s:\n" line name;
  	ignore(Pretty.printf "  @[%a@]" d_assign_effect a_effect)
  end


(* Extract the asssignment effect, from a general effect. *)
let rec make_assign_effect (in_eff:effect) : assign_effect = 
  match in_eff with
  | [] -> []
  | (LockOp _) :: tl -> make_assign_effect tl
  | (Join fl) :: tl -> 
      (AJoin (List.map make_assign_effect fl)) :: (make_assign_effect tl)
  | (NCall ((loc,_,_,fvi,_) as ci, _)) :: tl ->
      let key = (fvi.vid, fvi.vname) in
      let fnSt = !SPTA2.modSumms#getModsCtx key ci in
      (*let substFnSt = List.map (subst_assign ci) fnSt in*)
      (ACall (ci,fnSt)) :: (make_assign_effect tl)
  | (RCall ((loc,_,_,_,_),_)) :: tl ->
      warn "[%s] Recursive calls with visible lock writes are not supported. \
            The assignments made in this recursive call will be ignored.\n"
            (loc2strsmall loc);
      make_assign_effect tl
  | (Assign a) :: tl -> (AAssign a) :: (make_assign_effect tl)
  | (BpLoop i) :: tl -> make_assign_effect tl
    
let eq_malloc (e1:Cil.exp) (e2:Cil.exp) : bool = 
  match (e1, e2) with 
  | (AddrOf (Var vi1, _), AddrOf (Var vi2, _)) -> 
      let mh = getMalloc1 () in
      H.mem mh vi1.vname && H.mem mh vi2.vname && 
        (Ciltools.compare_type vi1.vtype vi2.vtype == 0)
  | _ -> false

(* Mallocs of the same type are equable *)
let compare_assigns (_,((l1,s11),(e1,s12),_)) (_,((l2,s21),(e2,s22),_)) = 
    Ciltools.compare_lval l1 l2 == 0 &&
    (* Mallocs in branches are considered equable. *)
    ( match e1,e2 with
      | Some e1, Some e2 -> 
        (Ciltools.compare_exp e1 e2 == 0 ||(eq_malloc e1 e2))
      | None, None -> true
      | _,_ -> false )
    
    

let assign_map_to_list map =
  let l0 = LvalMap.fold (fun k a l -> a::l) map [] in
  List.sort (fun (i1,_) (i2,_) -> compare i1 i2) l0


let equal_lval_map  (a: (int * assign_t) LvalMap.t) 
                    (b : (int * assign_t) LvalMap.t) : bool = 
  let la = assign_map_to_list a in
  let lb = assign_map_to_list b in
  if List.length la <> List.length lb then 
    false
  else
    List.fold_left2 
    (fun f a1 a2 -> f && compare_assigns a1 a2) true la lb

let mergeMaps fromMap toMap : (int * assign_t) LvalMap.t =  
  LvalMap.fold LvalMap.add fromMap toMap

let assign_index : int ref = ref 0

let resetAIndex = assign_index := 0

let incIndex () = 
  let ret = !assign_index in 
  assign_index := ret + 1

let getIndex () = !assign_index 

let getIncIndex () = 
  let ret = !assign_index in 
  assign_index := ret + 1; ret


let rec compare_assign_list (fl:assign_effect list) 
  : (bool * (int*assign_t) LvalMap.t) = 
  match fl with
  | [] -> (true, LvalMap.empty)
  | fh::tl -> 
      let head_map = compute_assign_sum fh in
      let comp = 
        List.fold_left (
          fun b f -> 
            b && (
              let t_map = compute_assign_sum f in
              equal_lval_map head_map t_map)
        ) true tl
      in
      (comp, head_map)
(* Compute an assignment effect's summary given the assignment effect. *)
and compute_assign_sum (af:assign_effect) : (int * assign_t) LvalMap.t =
  List.fold_left (
    fun inSt aae ->
      match aae with
      | AAssign (((lv,sc1),(exp,sc2),ctx) as a) ->
          LvalMap.add lv (getIncIndex (),a) inSt
      | AJoin afl -> 
          let (b,fm) = compare_assign_list afl in
          if b then mergeMaps fm inSt else inSt
      | ACall (ci, callee_state) ->
          List.fold_left (
            fun st (((lv,_),_,_) as a) ->
              let slv = (*subst_lval ci*) lv in
              let ind = getIncIndex () in
              LvalMap.add slv (ind, a) st
          ) inSt callee_state
  ) LvalMap.empty af

(* Computes the effects assign state (respect to the assignments' order). *)
let compute_assign_state (af:assign_effect) : assign_state =
  let map = compute_assign_sum af in
  let lsort = assign_map_to_list map in
  (*let _ = List.iter (
      fun (i,((lv,s1),(e,s2),loc)) ->
        log "(%d) %s (%s) <- %s (%s) [%s]\n" i 
        (lval2str lv) (scope2str s1) (exp2str e) 
        (scope2str s2) (loc2strsmall loc)
    ) lsort;
    log "%s" line in *)
  List.map (fun (i,a) -> a) lsort


let check_assign_join (f:effect list) : unit =  
  let assign_f = L.map make_assign_effect f in
  if not (fst(compare_assign_list assign_f)) then
    let loc = get_stmtLoc (!call_stmt.skind) in
    err "[%s] Assignment mismatch at join operator.\nAssignments in each branch \
      of the join should be equal in type and sequence.\n"
    (loc2strsmall loc)


