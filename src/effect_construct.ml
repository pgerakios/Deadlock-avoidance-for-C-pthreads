open Cilinfos
open Lvals
open Scope
open Scc
open Scc_cg

module D = Cildump
module PTA = Myptranal
module H = Hashtbl

module E = Errormsg
module L = List

open Cil
open Printf

open Cfg
open Pretty
open Definitions
open Modsummary
open Effect_tools
open Effect_checks


(* Check if this is a lockhandle free:
 * this needs to be here and cannot be in trans_alloc, we have to run 
 * pointer analysis first. *)
let updateFreeMap _ : unit = 
  let loc = !call_loc in
  let e = !fun_e in
  let el = !args_e in
  match e, el with
  | Lval (Var fvi, _), [arg0] ->
      let arg = match arg0 with
        | CastE (_,arg) -> arg
        | _ -> arg0
      in
      if fvi.vname = "free" then 
        (* TODO: this is probably pointless cause free could be 
         * casted to void * *)
        if typeContainsLock (typeOf arg)  then
        let pp = {
          pp_stmt = (!call_stmt).sid;
          pp_instr = !cur_instr_ind;
          } in 
        let (must,elist) =
          SPTA2.getAliasesAtExp pp (Lvals.abs_of_exp arg) in				
        let is_singleton = match elist with _::[]->true|_->false in
        if not must || not is_singleton then begin
          (*log "must:%b is_sing:%b\n" must is_singleton;*)
          err "Trying to free a multi-aliased lock handle.\n";
          rs_impossible "updateFreeMap/0"
        end
        else 
          let aexp = (List.hd elist) in
          let expl = exp_of_abs aexp in
          begin     
            match expl with
            | [(*AddrOf (Var gvi,_) as*) exp] -> 
              (* We need to remove lock handles that have been malloced, as
               * well as structs that contain locks (pthread_mutex_t). Lock
               * handles that are part of a struct are removed by them selves
               * independently. 
               * *)
              (*if H.mem (getMalloc1 ()) gvi.vname then
                begin
                  H.add free_map loc gvi.vname;
                  log "Freeing (%s) %s (which is or contains lock).\n"
                    (loc2str loc) gvi.vname
                end*)
              begin
                H.add free_map loc exp;
                log "[%s] Freeing %s (which is or contains lock).\n"
                  (loc2strsmall loc) (exp2str exp)
              end
            | _ ->  rs_impossible "updateFreeMap/1"
          end
          
  | _ -> ()


let rec check_offset off loc = 
  match off with
  | NoOffset -> ()
  | Field (_,o) -> check_offset o loc
  | Index _ -> 
      unimp "[%s] Found the offset `%s' when (un)locking or passing as \
      argument to function.\nArrays of locks (or structs containing locks) \
      are not supported.\n" (loc2strsmall loc) (off2str off)

let check_offset_lval lval loc =
  check_offset (snd lval) loc 

let rec refuse_lock_arrays exp loc = 
  match exp with
    Const _ -> ()
  | Lval lval -> check_offset_lval lval loc
  | SizeOf _ -> ()
  | SizeOfE e -> refuse_lock_arrays e loc
  | SizeOfStr _ -> ()
  | AlignOf _ -> ()
  | AlignOfE e -> refuse_lock_arrays e loc                                     
  | UnOp (_,e,_) -> refuse_lock_arrays e loc
  | BinOp (_,e1,e2,_) -> (refuse_lock_arrays e1 loc; refuse_lock_arrays e2 loc)
  | CastE (_,e) -> refuse_lock_arrays e loc
  | AddrOf lval ->  check_offset_lval lval loc
  | StartOf lval -> check_offset_lval lval loc


let rec checkExpOffs exp loc = 
  match exp with
  | Const _ -> ()
  | Lval lval -> checkLvalOffs lval loc
  | SizeOf _ -> ()
  | SizeOfE e -> checkExpOffs e loc 
  | SizeOfStr _ -> ()
  | AlignOf _ -> ()
  | AlignOfE e -> checkExpOffs e loc
  | UnOp (_,e,_) -> checkExpOffs e loc 
  | BinOp (_,e1,e2,_) -> (checkExpOffs e1 loc ; checkExpOffs e2 loc)
  | CastE (_,e) -> checkExpOffs e loc 
  | AddrOf lval -> checkLvalOffs lval loc
  | StartOf lval -> checkLvalOffs lval loc 

and checkLvalOffs lval loc = 
  match lval with
  | (Var _,offs) -> check_offset offs loc
  | (Mem exp,offs) -> (checkExpOffs exp loc; check_offset offs loc)


exception NoAtomicEffect

(* The sexp e, given a substitution environment s, will be substituted by 
 * the result of this function. *)
let substVarinfo_sexp (call_loc:Cil.location)
    (s:subst_typ0) (e:sexp) (m:mem_t) : sexp =
  let rec do_e (e:sexp) : sexp =
    begin 
      match e with    
      | SBot -> SBot 
      | SAddrOf e' -> 
          SAddrOf (do_e e')
      | SVar((fd,vi),o) ->
          (*let _ = log "SVar %s, fn: %s\nsubst_typ:\n" 
             vi.vname fd.svar.vname in*)

          let fnd (vi',_) = vi'.vid = vi.vid in
          begin 
            (* Check if this is a parameter passed argument as to the function *)
            match absFind List.find fnd s with
            | Some (_,Some e') -> 
                (*let _ = log "[l.%d] Original vi: %s (%s)\n" 
                  call_loc.line  vi.vname (typ2str vi.vtype) in
                let _ = log "[l.%d] New vi: %s\n" 
                  call_loc.line (sexp2strsmall e') in*)
(*                  let _ =
                    if Ciltools.compare_type vi.vtype vi'.vtype <> 0 then
                      log "Diverging types in substvarinfo.\n" in
*)
                (* IMPORTANT: changed this *)
                (* SInst((fd,vi),o,[e'],call_loc)*)
                e'
            | _ -> 
              begin
                match m with
                (* Case of heap allocated lock - substitute with the
                 * correspondent global in the caller function context. *)
                | Heap (_,ctx) ->
                    let ctx' = call_loc::ctx in
                    (* look for the global "malloc" variable in the current 
                     * function context *)
                    (*let _ = log "<---> Substit: ctx: %s\n" (ctx2str ctx') in*)
                    let vi' = try
                        snd (H.find malloc_map_assign0 ctx')
                      (* FIXME *)
                      (* If the ctx' is not found in the mappings this means
                       * that the heap location does not escape the function.
                       * Perhaps this should not be included in the effect.*)
                      with Not_found ->
                        info "[%s] This abstract location does not escape \
                          the function called at `%s'.\nThis operation will \
                          not appear in the effect of a function that calls \
                          this one.\n" (ctx2str ctx)
                          (loc2strsmall call_loc);
                        raise NoAtomicEffect
                    in
                    let fd' = !(!cur_fstruct.fun_dec) in
                    SVar ((fd',vi'),o)
                | _ -> e
              end
          end
      | SDeref(e',o) ->
          SDeref (do_e e',o)
      | SAbsHost(p,o) -> e

      | SInst(x,o,e',loc) -> SInst(x,o,List.map do_e e',loc)
    end 
  in do_e e 
  
  
(* Substitute an atomic effect of a callee function into 
 * the caller function. *)
let rec substAtomicEffect (cloc:Cil.location)
  (subst:subst_typ0) (f:atomic_effect) : atomic_effect option =
	let do_f = substEffect cloc subst  in
	begin
    match f with
    |	LockOp(calli,is_acquire,sexp,m) -> 
        begin
          try
            let sexp' = substVarinfo_sexp cloc subst sexp m in
            (* After the substitution the sexp must be updated 
             * cause there might be an offset added *)
            if singleAlias sexp' then
              let exp = sexp2exp sexp' in
              let pta_sexp = opt2some (getSexp exp) in
              (* We might need to cast this expression 
               * in case it is originally passed as a 
               * void * argument. - If this is not done CIL 
               * will complain for trying to find an offset
               * in a void struct. *)
              let pta_exp = sexp2exp pta_sexp in
              let cast_exp = cast_local pta_exp in
              (*let _ = log "cast_exp: %s\n" (exp2str cast_exp) in*)
              let cast_sexp = exp2sexp cast_exp in

              let m' = getMemoryType cast_sexp in
              Some (LockOp(calli,is_acquire,cast_sexp, m'))
            else begin 
              unimp "[%s] Too many aliases while substituting effect.\n"
                (loc2strsmall cloc); Some f
            end
          with NoAtomicEffect -> None
        end
    | Join el -> Some (Join (List.map do_f el))
    | NCall(a,f_res) -> 
        let f' = must_resolved "substAtomicEffect" f_res in
        Some (NCall(a,mkresolved (do_f f')))

    | RCall(a,f_opt_ref) ->
        begin match !f_opt_ref with
        | Some f' -> Some (RCall(a,ref (Some (do_f f'))))
        | None -> raise(Impossible "substAtomicEffect/RCall") 
        end
    (* Assignments are taken care of seperately *)
    | Assign (a,b,ctx) -> Some (Assign (a,b,cloc::ctx))
    (* There should't be any BpLoops left *)
    | BpLoop _ -> None
	end

(* The updated effect to be inlined in the calling function. *)
and substEffect (cloc:Cil.location)	(subst: subst_typ0) (f:effect) : effect =
	(*List.map (substAtomicEffect cloc subst) f*)
  List.fold_left (
    fun feed aeo -> 
      match substAtomicEffect cloc subst aeo with
      | Some ae -> feed@[ae]
      | None -> feed
  ) [] f



(* Create the atomic effect based on the expression being locked. *)
let doLockOpArg (arg : Cil.exp) (is_acquire : bool) : effect=
	let calli = (!call_loc, !fun_e, arg) in
  (* Do not allow arrays of locks. *)
  refuse_lock_arrays arg !call_loc;
	let sexp_opt = getSexp arg in
	match sexp_opt with
	| Some sexp -> 
		begin	     
      
      let mem = getMemoryType sexp in
      log "[%s] %sLocking: %s (pta: %s) (mem: %s)\n" 
        (loc2strsmall !call_loc) 
        (if is_acquire then "" else "Un")
        (exp2str arg) (sexp2strsmall sexp)
        (mem2str mem);
      checkExpOffs arg !call_loc;
      let e = sexp2exp sexp in
      Sanity.register !call_loc;
      checkExpOffs e !call_loc;
      [LockOp(calli,is_acquire,sexp,mem)]
     end
  | _ -> [] 

(* ceFromExp : Function that creates the effect from a single
 * lock operation. The effect is a list  whose length should be
 * 0 or 1 if is a simple lock or bigger if it is an inlined
 * function effect. *)
let ceFromExp  (lock_exp : Cil.exp) (ltype : bool list) : effect = 
  let exp_type = Cil.typeOf lock_exp in
  if typeOfLockPtr exp_type then
    L.flatten (L.map (doLockOpArg lock_exp) ltype)
  else			
  begin
    err "Attempting to lock a variable that is not a lock handle." ; []
  end


(* This function processes a call to a function defined in the sources,
 * and returns its effect. *)
let doNormalCall (lvo:lval option) (fd:fundec) : effect = 
  let loc = !call_loc in
  let el = !args_e in
  let callfn = fd.svar in
  let pp = {pp_stmt = (!call_stmt).sid; pp_instr = !cur_instr_ind;} in 
  begin
  match lvo with
  | Some (Var vi,off) -> begin
    if typeContainsLock vi.vtype then begin
    (* functions that returns a lock handle *)
         (!cur_fstruct).has_malloc <- true
       end;
       () end             
  | _ -> ()
  end;
  let formals = fd.sformals in
  let _ = 
    if L.exists (fun f -> typeOfLock f.vtype) formals then
      err "[l.%d] Cannot pass pthread_mutex_t as argument (should use \
        pthread_mutex_t *).\n" loc.line
  in
  let alias x : Lvals.aExp option =
    let (must, al) = SPTA2.getAliasesAtExp pp x in 
    let is_singleton = match al with _::[]->true|_->false in
    let callee_has_eff : bool =
      try
        let fs = H.find fun_to_funInfo callfn.vid in
          fs.has_effect
      with Not_found -> rs_impossible "compInstrEffect/0" in
    begin
      (* safety check *)
      (* If there is a chance that the function might have an effect
       * then return the aliases. Else, return None, cause we don't 
       * care. *)
      if (callee_has_eff) && 
          (typeContainsLock (typeOf (Lvals.exp_of_abs_simple x))) then
            begin
              if (not must || not is_singleton) then begin
                err "[%s] This is a \"may\" expression (%s).\n" 
                (loc2strsmall !call_loc) (aexp2str x) ; None end
              else
                match al with
                | [a] -> Some a
                | _ -> rs_impossible "alias"
            end 
      else None (* Don't care if lock isn't passed as an argument *)
    end
  in

  let simparg arg : (sexp option) =
    let a = alias (Lvals.abs_of_exp arg) in
    match a with 
    | Some s -> Some (simplify_aExp s) 
    (* changing this in case PTA doesn't work *)
    | _ -> Some (simplify_aExp (abs_of_exp arg))
  in

  let this_funName = !(curFunc).svar.vname in
  let ci = (!call_loc, !cur_pp, !fun_loc, callfn, !args_e) in
  let curSCC = getCurrSCC () in
  (*Handle directly recursive calls *)
  if String.compare this_funName callfn.vname = 0 then begin
    warn "[%s] Does not yet support recursive calls. \
    If this function call contains effect, \
    this will be ignored.\n" (loc2strsmall loc);
    [RCall (ci, ref (Some []))]
  end
  (* Handle indirectly recursive calls (calls to funcitons in the same 
   * SCC with the calling function). *)
  else if sameSCC curSCC (callfn.vid, callfn.vname) then begin
    try 
      if (H.find fun_to_funInfo callfn.vid).examined then
        let callEff = (H.find fun_to_funInfo callfn.vid).funEffect in
        (if nonEmptyEffect callEff then
          warn "[%s] Does not yet support recursive calls (indirect):\n\
            Function `%s' has already been checked for effect, and \
            contains one.\nThis will be ignored.\n" (loc2strsmall loc)
            callfn.vname
        else
          info "[%s] Does not yet support recursive calls (indirect).\n\
            However, function `%s' has already been checked for effect, and \
            does not contain one.\n" (loc2strsmall loc) callfn.vname)
      else
        warn "[%s] Does not yet support recursive calls (indirect).\n\
            Function `%s' hasn't been checked for effect yet.\n" 
            (loc2strsmall loc) callfn.vname;
      [NCall (ci, ref (Resolved []))] 
    with Not_found -> 
      warn "[%s] Does not yet support recursive calls (indirect). \
            This really shouldn't have happened.\n" (loc2strsmall loc);
      [NCall (ci, ref (Resolved []))] 
  end
  else try
    (* Check that no argument containing lock is passed as an argument *)
    L.iter (fun e -> 
      if typeContainsLock (typeOf e) then
        checkExpOffs e !call_loc) el;
    (* Check that the number of passed arguments is acceptable *)
    let (_,_,is_vararg,_) =  splitFunctionType fd.svar.vtype in
    let compatible_arg_num =  
      L.length formals = L.length el || is_vararg in
    if compatible_arg_num then begin
      (* argSexpL is a list with elements that are the lists of every 
       * possible alias of the real parameters. *)    
      let (argSexpL : (sexp option) list ) = List.map simparg el in
      (* In case of variable arguments just combine the first which are
       * in common. *)
      let comb = List.combine formals 
                (List_utils.take (L.length formals) argSexpL) in
      (* Get the effect summary of the called function *)
      let callee_sum : effect = 
        try let fs = H.find fun_to_funInfo callfn.vid in fs.summary
        with Not_found -> rs_impossible "compInstrEffect/2" in
      (*log "%s\n" line;
      log "This is`%s' effect.\n" callfn.vname;
      print_effect callee_sum ; *)

      (* The effect that is substituted is the summary effect *)
      let subst_sum = substEffect !call_loc comb callee_sum in
      (*log "[%s] Inlining effect (%s, len: %d):\n"
        (loc2strsmall loc) callfn.vname (effect_size subst_sum);*)

      (*print_effect subst_sum;
      log "Printed effect\n";*)

      let f_map = fillEffMap SexpMap.empty subst_sum in
      set_ncall_summary loc f_map;
      if subst_sum <> [] then begin
        (*log "Registering %s\n" (loc2strsmall !call_loc);*)
        Sanity.register !call_loc
      end;

      [NCall (ci,mkresolved subst_sum)]
    end
    else begin
      warn "[%s] Real parameters are fewer than the formal.\n\
            #Typical = %d, #Real = %d\n\
            This function call's effect will be ignored.\n"
            (loc2strsmall loc) (L.length formals) (L.length el); []
    end
  with End_analysis -> exit (-1)     



(* Handle direct calls and return their effects *)
let doDirectCall (lvo:lval option) (callfn:varinfo) : effect =
  fun_loc := callfn.vdecl;
  let el = !args_e in
  let loc = !call_loc in
 
  let ltype_opt = lock_type callfn.vname  in	
  let call_fd_opt : Cil.fundec option = try
  let fs = H.find fun_to_funInfo callfn.vid in Some !(fs.fun_dec)
    with Not_found -> None in

  match ltype_opt , el, call_fd_opt with
  (* Lock operation *)
  | Lock , [arg], _ -> ceFromExp arg [true]
  (* Unlock operation *)
  | Unlock , [arg], _ -> ceFromExp arg [false]
  (* Condition wait operation *)
  | CondWait , [_;arg], _ -> ceFromExp arg [false;true]
  (* Lock operation called with wrong number of arguments *) 
  | Lock , _, _ | Unlock, _, _ | CondWait, _, _ -> 
      err "[%d] Lock function called with wrong number of arguments"
        loc.line; []
  (* Call to an external function *)
  | _, _, None -> begin
      match lvo with
      | Some (Var vi,off) -> begin
        (* Keep track of info to determine if this function 
         * calls a malloc for a lock hanlder. *)
        (* This is probably not needed as we are also looking for
         * the assigment of the global created by CIL. *)
        if typeContainsLock vi.vtype
         && List.mem callfn.vname alloc_names 
            then begin          
             (!cur_fstruct).has_malloc <- true
           end; [] end
           
      | _ -> []
    end
  (* Call to function declared in source files *)
  | _, _ , Some called_fundec ->
      if called_fundec.svar.vstorage <> Extern then
        doNormalCall lvo called_fundec
      else []
  

(* Handle indirect calls - function pointers *) 
let doIndirectCall lvo cloc =
  let proc lst x =
    match x with
    | Some vi ->
        let (t1,t2) =  (typeOf !fun_e, vi.vtype) in
        let (ts1,ts2) = (typeSig t1, typeSig t2) in
        if Util.equals ts1 ts2 then          
            (doDirectCall lvo vi)::lst    
        else lst
    | None -> lst
  in            

  let aliases = (alias_map cloc) in
  let vids_opt  = List.map varinfo_of_name aliases in
  let (el:effect list) = 
    List.fold_left proc ([]:effect list) vids_opt
  in 
  (*H.add indirect_call_map call_loc *)
  let f0 =  
    match el with 
    | [] -> [] 
    | hd::[] ->
        (*PG: no optimizations when counting locks*) 
        if !count_locks then
        begin 
          if hd = [] then [] 
          else [Join [hd]]
        end
        else
          hd
    | _ ->
        if List.for_all (fun x -> x = []) el then
          []
        else
          [Join el] 
  in           
  if f0 <> [] then
    match vids_opt with
    | [Some vi] ->
      let ci = (!call_loc,!cur_pp,locUnknown,vi, !args_e) in
      [NCall (ci,mkresolved f0)]
    | _ -> 
      (* we are using a dummy var because there is more than one *)
      let ci = (!call_loc,!cur_pp,locUnknown,dummyVar, !args_e) in
      [NCall (ci,mkresolved f0)]
  else []


let insertAssign (lval:Cil.lval) (exp:Cil.exp) loc : effect =
  let e_opt = getSexp exp in
  let sc1 = getScopeLv lval in
  match e_opt with
  | Some rsexp -> begin
      let exp' = sexp2exp rsexp in
      let sc2 = getScopeExp exp' !curFunc in
      log "[%s] Found assignment: %s (sc: %s) := %s (%s) (pp:%s)\n"
      (loc2strsmall loc) (lval2str lval) (scope2str sc1)
      (exp2str exp') (typ2str (typeOf exp')) (pp2str !cur_pp);
      (match sc2 with
      | SGlobal | SFormal _ -> 
          begin
            match exp' with
            | AddrOf (Var vi,_) ->
              (* The location of the assignment is not necessarily the 
               * location of the global we created. We need the later 
               * for the runtime. *)
                let loc' = try
                    let (l,_,_,_) = H.find (getMalloc1 ()) vi.vname in l
                  with Not_found -> loc
                in [Assign ((lval,sc1),(Some exp',sc2),[loc'])]
            | _ -> [Assign ((lval,sc1),(Some exp',sc2),[loc])]
          end
      | _ -> 
          begin
            warn "[%s] Assigning locally scoped data in this \
                  function call,\nbecause `%s' is not a global or formal \
                  parameter.\n" (loc2strsmall loc) (exp2str exp');
            (* TODO: Maybe we should take these into account *)      
            [(*Assign ((lval,sc1),(exp',sc2),[loc])*)]
          end)

      end
  | _ -> log "[%s] %s (sc: %s) := Top\n"
      (loc2strsmall loc) (lval2str lval) (scope2str sc1) ; 
      [Assign ((lval,sc1),(None,STBD),[loc])]



(* Handle assignment *)  
let rec doAssign (lval:Cil.lval) (exp : Cil.exp) (loc:Cil.location) : effect = 
  let t = typeOfLval lval in
  if typeContainsLock t then  begin
    let pp = {pp_stmt = (!call_stmt).sid; 
              pp_instr = !cur_instr_ind;} in
    let mustPt, targets = SPTA2.derefLvalAt pp lval in
    if List.length targets = 0 then begin
      let sc1 = getScopeLv lval in
      match sc1 with 
      | SFormal _ -> []
      | SGlobal -> insertAssign lval exp loc
      | STBD -> []
      | _ ->  info "[%s] This assignment is not visible outside the function.\n"
                (loc2strsmall loc) ; []
    end
    else if L.length targets = 1 then begin
      let lval' = lval_of_abs_simple (L.hd targets) in
      (*let _ = log "Deref(%s) = %s\n" (lval2str lval) (lval2str lval') in*)
      let sc1 = getScopeLv lval' in
      match sc1 with 
      | SFormal _ | SGlobal -> insertAssign lval' exp loc
      | STBD -> 
          warn "[%s] Cannot determine this assignment.\n"
                (loc2strsmall loc) ; []
      | _ -> info "[%s] This assignment is not visible outside the function.\n"
                (loc2strsmall loc) ; []
    end
    else
      begin
        err "[%s] PTA could not determine `%s'\n" 
          (loc2strsmall loc) (lval2str lval); [] 
      end
  end
  else []
            


(* compInstrEffect: Processes an instruction  *)
let compInstrEffect (i : Cil.instr) : effect =
  cur_instr := i;
  cur_pp := {pp_stmt = (!call_stmt).sid; pp_instr = !cur_instr_ind;};
  match  i with
  | Call(lvo, e, el, loc) ->
    begin
      call_loc := loc;
      fun_e := e;
      args_e := el;
      updateFreeMap ();
      match e with
      (* Direct call *)
      |	Lval(Var(callfn),_) -> 
          doDirectCall lvo callfn
      (* Indirect Call *)
(*      | Lval((Mem(Lval(Var(callfn),_)),_)) ->
          (* TODO : indirect call that returns a value. *)
          doIndirectCall lvo callfn*)
      | _ ->
          doIndirectCall lvo loc
(*          warn "[%s] Making a function call (`%s') which is \
          neither direct nor indirect.\nThis effect \
          will be ignored.\n" (loc2strsmall loc) (inst2str i); []*)
    end	
  (* Insert effect concerning modifications to variables passed
   * as parameters or globals.
   * We also care for the assignment of a global pthread_mutex_t 
   * variable (or a struct containing a lock) to an lvalue, that 
   * was assigned by CIL at trans_alloc. Looking for malloc won't
   * suffice, cause this is probably casted to void *. *)
  | Set (lv, exp , loc) ->
      begin
        match exp with
        | AddrOf(Var(vi),_) ->
            if H.mem (getMalloc1 ()) vi.vname then
              (!cur_fstruct).has_malloc <- true
        | _ -> ()
      end;
      doAssign lv exp loc
  | _ -> []

let count = ref 0

