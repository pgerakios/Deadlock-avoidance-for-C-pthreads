open Cil
open Scc
open Scc_cg
open Printf
open Pretty
open Definitions
open Modsummary
open Simple_definitions
open Simple_effect_tools
open Trans_alloc
open Cil_lvals
module H = Hashtbl
module L = List



(* Create the atomic effect based on the expression being locked. *)
let doSlockOpArg (arg : Cil.exp) (is_acquire : bool) : simple_effect=
	let calli = !call_loc in
  log "[%s] %sLocking: %s (t: %s)\n"
    (loc2strsmall !call_loc) 
    (if is_acquire then "" else "Un") (exp2str arg)
    (typ2str (unrollTypeDeep (Cil.typeOf arg)));
  Sanity.register !call_loc;
  [SLockOp(calli,is_acquire,arg)]

(* ceFromExp : Function that creates the effect from a single
 * lock operation. The effect is a list  whose length should be
 * 0 or 1 if is a simple lock or bigger if it is an inlined
 * function effect. *)
let ceFromExp  (lock_exp : Cil.exp) (ltype : bool list) : simple_effect = 
  L.flatten (L.map (doSlockOpArg lock_exp) ltype)

(* count errors of invalid effect substituteions *)
let invalid_arg_c = ref 0
let invalid_var = ref 0
let invalid_addrof = ref 0
let invalid_memvlal = ref 0
let invalid_memptr = ref 0
let invalid_expaddr = ref 0
let invalid_startof = ref 0
let invalid_align = ref 0
let inc c =  
  c := !c +1

(** Find instances of the formal within given lval, and substitute w/ 
    the given actual lval *)
let rec substActForm actual lvalWithFormal : Cil.exp =
  match lvalWithFormal with
    (Var(vi), formOff) ->
      begin
        match actual with
        | Const _ | SizeOf _ | AlignOf _
        | SizeOfE _ | SizeOfStr _ -> 
            (inc invalid_var;
            raise SubstInvalidArg)

        | StartOf lval 
        | Lval lval   -> Lval (addOffsetLval formOff lval)
        
        | AlignOfE e | UnOp (_,e,_) | BinOp (_,e,_,_) 
        | CastE (_,e) -> substActFormExp e (Lval lvalWithFormal)

        | AddrOf lval ->
            begin
              match formOff with
              | NoOffset -> actual
              | _ -> (inc invalid_addrof ; raise SubstInvalidArg)
            end            
      end

  | (Mem (Lval(Var(vi), NoOffset)), outerOff) -> begin
      (* Assume any variable encountered is the formal... To fix this,
         should actually add a var attribute to compare against *)
      try
        Lval (mkMemChecked actual outerOff)
      with 
        OffsetMismatch _
      | Errormsg.Error 
      | Failure _
      | _ ->
          (inc invalid_memvlal;
          raise SubstInvalidArg)
    end
  | (Mem(ptrExp), outerOff) ->
      try
        let newExp = substActFormExp actual ptrExp in
        Lval (mkMemChecked newExp outerOff)
      with 
        OffsetMismatch _
      | Errormsg.Error 
      | Failure _ 
      | _ ->
          (inc invalid_memptr;
          raise SubstInvalidArg)
          
        
and substActFormExp actual expWithFormal : Cil.exp =
  match expWithFormal with
    Lval(lv) -> substActForm actual lv
        
  | AddrOf (l) ->
      begin
        match substActForm actual l with
        | Lval lv -> AddrOf lv
        | _ -> 
            (inc invalid_expaddr;
            raise SubstInvalidArg)
      end

  | StartOf(l) ->
      begin
        match substActForm actual l with
        | Lval lv -> StartOf lv
        | _ -> 
            (inc invalid_startof;
            raise SubstInvalidArg)
      end

  | CastE(t, e) -> CastE (t, substActFormExp actual e)        
  | AlignOfE(e) -> AlignOfE (substActFormExp actual e)        
  | SizeOfE(e) ->  SizeOfE (substActFormExp actual e)        
  | UnOp (unop, e, t) ->
      let newExp = substActFormExp actual e in
      UnOp (unop, newExp, t)
  | BinOp (bop, e1, e2, t) ->
      (* Assume formal is (only) in the first exp for now *)
      let newExp = substActFormExp actual e1 in
      BinOp(bop, newExp, e2, t)
  | AlignOf _  | SizeOf _  | SizeOfStr _  | Const _ ->
      (inc invalid_align;
      raise SubstInvalidArg)




let rec substSEffect (forms: varinfo list) (acts: exp list) (e: simple_effect) = 
  L.map (
    function 
    | SLockOp (l,b,exp) ->
        (* Try to substitue *)
        let subexp = 
          try
            let ass_vi = findBaseVarinfoExp exp in
            let (i,vi) = 
              List_utils.findi 
              (fun i fvi -> 
                fvi.vid = ass_vi.vid) forms 
            in
            let act = L.nth acts i in
            (*let _ = log "act: %s, exp: %s\n" 
              (exp2str act) (exp2str exp) in*)
            substActFormExp act exp 
            (* but don't fail if sth goes wrong*)
          with 
          | SubstInvalidArg -> 
            begin
              (*log "InvalidSubst: %s\n" (Printexc.to_string e);*)
              invalid_arg_c := !invalid_arg_c + 1;
              exp
            end
          | _ -> exp
        in
        (*let _ = log "%s -> %s\n" (exp2str exp) (exp2str subexp) in*)
        SLockOp (l,b,subexp)
    (* the rest cases should not occur *)
    | SJoin el -> SJoin (L.map (substSEffect forms acts) el)
    | a -> a
  ) e

  
(* Handle direct calls and return their effects *)
let doDirectCall (lvo:lval option) (callfn:varinfo) : simple_effect =
  fun_loc := callfn.vdecl;
  let el = !args_e in
 
  let ltype_opt = lock_type callfn.vname  in	


  match ltype_opt, el with
  (* Lock operation *)
  | Lock , [arg] -> ceFromExp arg [true]
  (* Unlock operation *)
  | Unlock , [arg]-> ceFromExp arg [false]
  (* Condition wait operation *)
  | CondWait , [_;arg] -> ceFromExp arg [false;true]
  (* Lock operation called with wrong number of arguments *) 
  | Lock , _ | Unlock, _ | CondWait, _ -> []
  (* Call to function *)
  | NoLockOp, _-> 
      try 
        let sfs = Hashtbl.find simpleFInfoHash callfn.vid in  
        let inlineSum = sfs.summary in
        if inlineSum <> [] then
          begin
            (* Calling a function with a non empty effect recursively *)
            let curSCC = getCurrSCC () in
            if sameSCC curSCC (callfn.vid, callfn.vname) then
              inc recursive_count;
            let fd = sfs.sFundec in
            (*let _ = log "PreInlined Sum:"; print_seffect inlineSum in*)
            let subeff = substSEffect fd.sformals el inlineSum in
            (*let _ = log "Inlined Sum:"; print_seffect subeff in*)
            [SCall (!call_loc, callfn.vname,subeff)]
          end
        else []
      with Not_found -> []
  

(* Handle indirect calls - function pointers *) 
let doIndirectCall lvo cloc =
  (* XXX : check if alias_map is working *)
  let aliases = alias_map cloc in
  let alias2effect alias = 
    let cvio = Cilinfos.varinfo_of_name alias in
    match cvio with
    | Some cvi -> doDirectCall lvo cvi
    | None -> []
  in
  match  aliases with
  | [] -> []
  | [alias] -> alias2effect alias 
  | _  -> 
      [SJoin (L.fold_left (fun feed nm -> 
        (alias2effect nm)::feed) [] aliases)]

(* compInstrEffect: Processes an instruction  *)
let compInstrEffect (i : Cil.instr) : simple_effect =
  cur_instr := i;
  cur_pp := {pp_stmt = (!call_stmt).sid; pp_instr = !cur_instr_ind;};
  match  i with
  | Call(lvo, e, el, loc) ->
    begin
      call_loc := loc;
      fun_e := e;
      args_e := el;
      match e with
      |	Lval(Var(callfn),_) -> doDirectCall lvo callfn
      | _ -> doIndirectCall lvo loc
    end	
  | _ -> []
