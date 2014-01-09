open Definitions 
open Modsummary
open Effect_tools
open Strutil
open Cil
module L = List
module D = Definitions

external inc_hash :  int -> int -> int  = "inc_hash"

(* Moved from effect_tools. Requicyan by this module as well*)
(* Do I have to check the called function? 
 * changed previous will_backtrack. 
 * *)
let will_backtrack vid = 
	begin  try
		let fs = Hashtbl.find fun_to_funInfo vid in
		fs.has_effect
	with Not_found ->
		(* this is an external function - we assume there is no effect here *)
		false
	end

(* check whether there exist any top-level lock-ops 
 * or any lock ops that WILL access the stack frame
 * *)
let rec nonEmptyEffect (f:effect) : bool = 
 List.exists (function 
  | LockOp _ -> true
  | Join el -> List.exists nonEmptyEffect el
  | NCall ((_,_,_,vi,_),_) -> will_backtrack vi.vid
  | RCall _ -> false
  | Assign _ -> false  
  | BpLoop _ -> false    
 ) f 

 
(**********************************************************
 *
 *        JOIN EFFECT CHECKS
 *
 **********************************************************)
 
let wrong_counts : SexpSet.t ref = ref SexpSet.empty
let add_wrong_count s = 
  wrong_counts := SexpSet.add s !wrong_counts
let reset_wrong_counts _ = 
  wrong_counts := SexpSet.empty
let get_wrong_counts _ = 
  !wrong_counts


(* Copy the aggregates from from_hash to the to_hash. *)
let mergeMaps to_map from_map : int SexpMap.t =
  let add sexp i feed =
    let cc = (try SexpMap.find sexp feed
              with Not_found -> 0 ) in
    SexpMap.add sexp (cc+i) feed in
  SexpMap.fold add from_map to_map

(* The counts shall match. If a varinfo is missing this equals 
 * to a binding to zero (0) counts.*)
let compare_two_maps m1 m2 =
  let single_check m s i acc =
    let ch = 
      (try (if SexpMap.find s m = i then true
        else false)
      with Not_found -> (i = 0)) in
    if not ch then 
      add_wrong_count s;
    acc && ch
      
  in
  (SexpMap.fold (single_check m1) m2 true) &&
  (SexpMap.fold (single_check m2) m1 true)
      
let rec compare_mlist m mlist : bool =
  match mlist with
  | [] -> true
  | (hd :: tl) ->
      if (compare_two_maps m hd) then
        compare_mlist m tl
      else false

(** Fill the mapping m with the lock operations of f. *)
let rec fillEffMap (m : int SexpMap.t) (f:effect) : int SexpMap.t =
  L.fold_left (
    fun fm ae ->        
      match ae with
      |	LockOp ((loc,_,_), lt, sexp,_) ->
        let cc = try SexpMap.find sexp fm
            with Not_found -> 0 in
        let add = if lt then 1 else -1 in
        (*if cc < 1 && add < 0 then 
          err "%s: This might return an error:\n  \
          trying to release a lock (%s) that has zero lock count." 
          (loc2str loc) (exp2str (sexp2exp sexp));*)
        SexpMap.add sexp (cc+add) fm
      | Join flist ->
          let (_, ret_map) = check_flist flist in
          mergeMaps fm ret_map            
      | NCall ((loc,_,_, vi,_), res_ref) ->
          (*let (argSexpL : (sexp option) list ) = List.map simparg el in
          let comb = List.combine formals argSexpL  in
          let subst_eff = substEffect loc comb clean_eff in
          let filter_eff = filterEffect !call_loc subst_eff in*)
          (*let csm = get_ncall_summary loc in*)
          begin try
            let inl = must_resolved "fillEffMap"  res_ref in
            (*let cm = fillEffMap SexpMap.empty inl in
            log "Inlining eff_map from %s (%s):\n" vi.vname (loc2strsmall loc);
            print_count_map cm;*)
            let csm = fillEffMap fm inl in            
            csm
          with _ -> fm
          end
      | RCall (_, _) -> fm
      | Assign _ -> fm      
      | BpLoop _ -> fm
  ) m f

(** Examines if every effect (element) of fl has the same lock count. *)
and  check_flist (fl : effect list) : (bool * (int SexpMap.t) ) =
  let eff_to_map f : int SexpMap.t =
    fillEffMap (SexpMap.empty) f in
  let count_mlist = L.map eff_to_map fl in
  match count_mlist with
  | [] -> rs_impossible "check_flist"
  | (ch::ctl) ->
      let _ = reset_wrong_counts () in
      let status = compare_mlist ch ctl in
      (*log "Will check %d paths\n" (L.length count_hlist);*)
      let ret_map = 
        try 
          L.find (fun m -> not (SexpMap.is_empty m)) (ch::ctl) 
        with Not_found -> ch 
      in
      (status, ret_map)
  (* return the mapping that ecloses the aggregate lock operations.
   * There should be no difference which mapping we use, since the 
   * counts should be the same. *)
 
(*
exception Is_Neg of sexp

let check_join_eff f : unit = 
  (* Checks that the aggregate count for a lock 
   * is >=0 (#locks >= #unlocks) *)
  let check_map m = 
    try
      SexpMap.iter (
        fun s i -> 
          if i < 0 then 
            raise (Is_Neg s)
      ) m 
    with Is_Neg s ->
      (*print_count_map m;  *)
      D.warn "Unlocking %s more times than locking it.\n"
        (exp2str (sexp2exp s))
  in 
  (* The mapping is a summary of the effect (counts) until this point *)
  let rec check_aux (m : int SexpMap.t) rest : unit = 
    match rest with
    | [] -> ()
    | ((LockOp _) as fh )::ft -> 
        let m' = fillEffMap m [fh] in
        begin
          (* At any given time the count in the mapping m' should be 
           * positive. *)
          check_map m';
          check_aux m' ft
        end
    | ((Join fl) (*as fj*))::ft -> 
        begin
          List.iter (check_aux m) fl
        end
    (* The rest of the cases should not cause changes in the counts,
     * once the substitution has taken place. *)
    | _ -> ()
  in
  check_aux SexpMap.empty f
*)


let check_loop stmt (loopEff:effect) : unit =
  let loc = get_stmtLoc stmt.skind in
  let (status, m) = check_flist [loopEff] in
  let result =
    status && SexpMap.fold (fun s c f -> f && (c = 0)) m true in
  log "Checking loop ending at: %s:.\n" (loc2strsmall loc);
  print_effect loopEff;
  if result then begin
    dlog "Count is OK (loop).\n";
    if !detailed_log then
      print_count_map m
  end
  else begin
    let wrong_locks = 
      SexpMap.fold 
        (fun s _ str -> str ^ (exp2str (sexp2exp s) ^ "\n")) 
                      m "" 
    in      
    error_set := StringSet.add
      ("["^(loc2strsmall loc)^"] Count in loop is not OK.\n\
    Aggregate lock operations must be zero. \
    This will affect all outer loops.\n\
    Check lock operations on the following locks:\n"^
    wrong_locks^"\n") !error_set
  end

(*
let check_join (eff_list : effect list) : unit =
  (* status: the result of the check: true if the count is OK,
   * m: the mapping with the counts on every sexp *)
  let (status, m) = check_flist eff_list in
  let loc = get_stmtLoc (!call_stmt.skind) in
  if not (SexpMap.is_empty m) then begin
    if status then 
      begin 
        dlog "[%s] Count is OK, map:\n" (loc2strsmall loc);
        if !detailed_log then 
          print_count_map m 
      end
    else 
      begin
        let wrong_locks = 
          SexpSet.fold 
            (fun s str -> 
              str ^ (exp2str (sexp2exp s) ^ "\n")) 
            (get_wrong_counts ()) "" 
        in
        err "[%s] Lock count mismatch at join operator (%d effects \
        flowing in). This will affect all outer joins.\nCheck lock \
        operations on the following lock(s):\n%s\n" 
          (loc2strsmall loc) (L.length eff_list) wrong_locks
      end
  end
*)



(* PG: 
 * SECTION ---- Lock counting  
 *
 *
 *
 *)
type ctx_ci = Cil.location * Cil.varinfo
type myctx_t =
   CEmpty 
 | CCall of (ctx_ci   *  (*just for debugging purposes*)
             int      *  (* hash of byte location + file name*)
             myctx_t 
            )
 | CCons of (            (* this can be a loop,join*)
             int   *     (* hash of construct*)
             myctx_t 
            )
(* flattened effect type, only l+ *)
type seffect_t = (sexp * myctx_t) list
(*counts_t : a triplet consisting of
 * #lexically scoped locks,
 * #stack-based locks,
 *  #non-stack based locks
 *)
type count_t = (int * int * int * int)
type lcounts_t = (myctx_t * sexp * count_t) list


let effect2str = any2str d_effect 
let spf format = Printf.ksprintf (fun x ->x ) format
let pf format =  Printf.ksprintf (fun x -> 
                                    Printf.printf "%s" x ) format
let cyan    s = "\027[36m\027[1m" ^ s ^ "\027[0m" 
let red     s = "\027[31m\027[1m" ^ s ^ "\027[0m"
let magenta s = "\027[35m\027[1m" ^ s ^ "\027[0m"
let yellow  s = "\027[33m\027[1m" ^ s ^ "\027[0m"
let green   s = "\027[32m\027[1m" ^ s ^ "\027[0m"

 (*myctx2str: for debugging purposes only  *)
 let rec myctx2str (c:myctx_t) : string = 
    match c with 
      CEmpty -> "Empty" 
    | CCall((loc,vi),i,c') ->
       (myctx2str c') ^ "::" ^ 
       (spf "Call(%s,%s,%d)" vi.vname (loc2str loc) i) 
    | CCons(i,c') ->
      (myctx2str c') ^ "::Cons(" ^ (string_of_int i) ^ ")"  

 let seff2str (s:seffect_t) : string = 
   abs_list2string " ||| "
   (fun (sexp,ctx) -> (sexp2str sexp) ^ "::" ^ (myctx2str ctx))
   (List.rev s)

 let cnt2str ((a,b,c,d):count_t) = spf "(%d,%d,%d,%d)" a b c d

 let ppcnt  ((a,b,c,d):count_t) = 
    spf "\t%s: %d\n\t%s: %d\n\t%s: %d\n\t%s %d\n" 
         (red "Lexically scoped") a
         (red "Stack-based same fun") b
         (red "Stack-based diff fun") c
         (red "Unstructured") d

 (* sadd: simple add *)
 let sadd ((a0,b0,c0,d0):count_t)
          ( (a1,b1,c1,d1):count_t) :count_t = (a0+a1,b0+b1,c0+c1,d0+d1) 

 (* print specific counts: *)          
 let lcounts2str (l:lcounts_t) = 
   L.fold_left 
   (fun s (ctx,sexp,cnt) ->
      spf "%s(%s\t||\t%s)%s\n" s 
          (myctx2str ctx) (sexp2str sexp) (cnt2str cnt)
   ) "" l

(* clocks: given an effect f return counts_t *)
let clocks f : (lcounts_t * count_t) = 
 (* create a mapping from locks operations to counts*)
 let (lock_map : ((sexp * myctx_t),
                  (IntSet.t * count_t)) Hashtbl.t) = 
     Hashtbl.create 32
 in
 (*ladd : TODO 
  * *)
 let ladd loc sexp ctx a0 : unit =
   let vv = (sexp,ctx) in
   let (visited,b0) =
   	try Hashtbl.find lock_map vv
   	with Not_found -> (IntSet.empty,(0,0,0,0))
   in
   let h = Hashtbl.hash (loc.file^(string_of_int loc.byte)) in
   if (IntSet.mem h visited) = false then 
   begin
      let (a,b,c,d) = sadd a0 b0 in
      let visited = IntSet.add h visited in
      Hashtbl.replace lock_map vv
      (visited,
      (if a > 0 && (b > 0 || c >0 || d > 0) then 
         (0,a+b,c,d)
       else 
         (a,b,c,d)
      ))
   end
 in
 (* plus: given an l- within context ctx, find find thr
  *            matching l+ in a flattend effect cf
  *)
 let plus  (loc:Cil.location) (ctx : myctx_t) (s: seffect_t)
           (sexp:sexp) : seffect_t = 
   (* eq_ctx: returns true if contexts c1 and c2 are equal *)
   let rec eq_ctx c1 c2 = 
     begin match (c1,c2) with
       (CEmpty,CEmpty) -> true
     | (CCall(_,i1,c1a),CCall(_,i2,c1b)) ->
       (i1 = i2) && (eq_ctx c1a c1b)
     | (CCons(i1,c1a),CCons(i2,c2a)) ->
       (i1 = i2) && (eq_ctx c1a c2a)
     | _ ->
       false 
     end
   in
   (* eat_ccons: removes ccons from a context 
    * *)
   let rec eat_ccons  = function
       CEmpty -> CEmpty
     | CCall(cia,i1,c1a) -> CCall (cia,i1,eat_ccons c1a)
     | CCons(i1,c1a) -> eat_ccons c1a
   in
   let rec plus_aux s other_plus = 
    begin match s with                  
       [] -> 
         ((0,0,0,0),[])
     | ((sexp0,ctx0) as hd)::tl ->
       if  (compare_sexp sexp sexp0) = 0 then
            ((if other_plus then 
                (0,0,0,1) (*unstructured, not stack-based*)
             else if eq_ctx ctx ctx0 then 
                (1,0,0,0) (*lexically scoped *)
             else if eq_ctx (eat_ccons ctx) (eat_ccons ctx0) then
                (0,1,0,0) (*stack based,unstructured, same function*)
             else 
                (0,0,1,0)(*stack based,unstructured, diff function*)
             ) ,tl)
       else
         let (b,tl0) = plus_aux tl true in (b,hd::tl0)
    end 
   in
   let (t,s') = plus_aux s false in
   (* pf "COUNT###: %s\n" (cnt2str t); *)
   ladd loc sexp ctx t;
   s' 
 in
 (* makeresult: convert lock map to a more convenient format
  *             and calculate total counts
  * *)
 let makeresult () =
  let l = ref ([]:(myctx_t * sexp * count_t) list) in
  let total = ref (0,0,0,0) in
  let it (a,b) (_,c) = 
      total := sadd !total c;
      l := (b,a,c) :: !l 
   in
   Hashtbl.iter it lock_map;
   (!l,!total)
 in
 let printmap () : unit =
    let (detail,cnt) = makeresult () in 
    pf "BEGIN DEBUG:\n%s\n%s:\n%s\n\nEND DEBUG"
      (ppcnt cnt) (green "LCOUNTS") (lcounts2str detail)
 in
 (* count:  given an effect f, a stack of l+ 
  *         (simplified effect seffect_t)  and a context c
  *         determine counts_t in that effect
  *)
 let rec count (c : myctx_t) 
               (s: seffect_t)
               (f : effect)  : seffect_t =
  (* pf  "\nCOUNT :\n%s : %s\n%s: %s\n%s: %s\n" 
            (cyan "Context") (myctx2str c) 
            (cyan "Effect" ) (effect2str f)
            (cyan "Stack"  ) (seff2str s) ;*)
   match f with
      [] -> s
    | ae::ftl ->    
      begin match ae with
      |	LockOp ((loc,_,_),lt,sexp,_) ->
            (*pf "\nCOUNT: lock op %s %b" (sexp2str sexp) lt;*)
        let s' = 
           if lt then (* lk+ operation *)
             (sexp,c)::s
           else 
             plus loc c s sexp
        in
        printmap ();
        count c s' ftl
      | Join flist ->
        let count' x =
            let c' = (CCons(Hashtbl.hash ae,c)) in 
            let s' = count  c' s x in
            let _  = count  c  s' ftl in 
            ()
        in
        L.iter count' flist;
        []
      | NCall ((loc,_,_,vi,_), res_ref) ->
        let h = Hashtbl.hash (loc.file^(string_of_int loc.byte)) in
        let c1 = CCall ((loc,vi),h,c) in
        let f' = 
           match !res_ref with
            | Resolved f' -> 
              f'
            | Unresolved _ ->
              rs_impossible "Unresolved fn call - count"
        in
        let s' = count c1 s f' in
        count c s' ftl
      | RCall (_, f0) ->
        let w () = 
          ignore( warn "This is a recursive function bearing\
                a non-empty effect.\n")
        in 
        begin match !f0 with
        | Some f0' ->
            if (nonEmptyEffect f0') then w ()
        | None -> w ()
        end;               
        count c s ftl
      | Assign _ ->
        rs_impossible "Found assignment effect - count"
      | BpLoop _ -> 
        rs_impossible "Found loop placeholder - count"
    end
 in
  let _  = count CEmpty [] f in
  makeresult ()

(* doCountLocks: finds lock information for each root function
 *)
let doCountLocks (() : unit): unit =
 log "BEGIN doCountLocks\n";
 let gf vid = 
   try 
     let ht = H.find fun_to_funInfo vid in
     ht.funEffect 
   with Not_found ->
    log "Effect not found!\n";
    [] 
 in
 let total = ref (0,0,0,0) in
 IntSet.iter ( fun vid ->
   let f0 = gf vid in
   let name = (Cilinfos.getVarinfo vid).vname in
   let (detail,cnt) = clocks f0 in
   log "\n%s  %s (vid:%d).\n%s\nEffect:\n\n%s\n"
        (magenta "Root function") name vid (ppcnt cnt) (effect2str f0);
   log "\n%s:\n%s\n" (green "LCOUNTS") (lcounts2str detail);
   total := sadd !total cnt
 ) !rootFuns;
 pf "\n%s:\n%s\n\n\n"
 (green "TOTAL") (ppcnt !total);
 log "END doCountLocks\n"


(*PG: static locksets*)
type lkop_t = Cil.location * sexp * mem_t
module LkopSet = Set.Make (
  struct 
    type t = lkop_t
    let compare = 
       fun ((l1,_,_):lkop_t) ((l2,_,_):lkop_t)  -> 
          Cil.compareLoc l1 l2
  end
)
type lset_t = LkopSet.t (* list of LockOp*) 
(* A location context is simply a list of locations*)
type lctx_t = Cil.location list

module CtxMap = Map.Make (
  struct 
    type t = lctx_t
    let compare = 
        fun l1 l2 ->
          let rec iter = function
               ([],[]) -> true
             | (loc1::l1,loc2::l2) ->
               (Cil.compareLoc loc1 loc2 = 0) &&
               (iter (l1,l2))
             | _ -> false
          in 
          if iter (l1,l2) then 0 
          else 1
  end
)

(* A context map is a mapping 
 * between location contexts and locksets
 *)
type ctxmap_t = lset_t CtxMap.t 
(* Each location of a sexp is associated with a "context set"*)
type loc2ctx_t = (ctxmap_t ref) LocMap.t

(*	LockOp of  
	(* (location of call (location of instruction), 
	* function that is called,
	* argument to lock op),
	* bool flag acquire/release, 
	* (aExp = aliased formal param or allocation point or global),
  * *)
	(lockopinfo * bool * sexp * mem_t)

type lockopinfo = Cil.location * Cil.exp * Cil.exp
 * *)

(*
let doStaticLockset () : unit = 
  log "BEGIN doStaticLockset\n";
  let gf vid = 
    try 
      let ht = H.find fun_to_funInfo vid in
      ht.funEffect 
    with Not_found ->
      log "Effect not found!\n";
      []
  in
  let lmap  =  ref LocMap.empty in
  (*addmap: add a binding for loc such that 
           loc -> (ctx,lkop) *)
  let addmap ctx loc lkop : unit = 
    let ctxmap = 
      try LocMap.find loc !lmap
      with Not_found -> 
        let empty = ref CtxMap.empty in 
        lmap := LocMap.add loc empty !lmap; 
        empty
    in
    let lset =
      try CtxMap.find ctx !ctxmap
      with Not_found -> 
        let empty = ref LkopSet.empty in 
        ctxmap := CtxMap.add ctx empty !ctxmap; 
        empty
    in
    lset := LkopSet.add lkop !lset
  in
  IntSet.iter ( fun vid ->
    let f0 = gf vid in
    let vi = Cilinfos.getVarinfo vid in
    let name = vi.vname in
    () (* PG: TODO *)
  ) !rootFuns;
  log "END doStaticLockset\n"
 *)


(*PV: gather effect size and number of distinct locks for the root threads*)

(* This effect is supposed to be straigth line, because it is a summary *)
let distLocksCum (sum: effect) : int = 
  SexpSet.cardinal (L.fold_left (
    fun ss lo -> 
      match lo with
      | LockOp (_,_,s,_) -> 
          SexpSet.add s ss
      | _ -> ss
  ) SexpSet.empty sum)


let doStats () = 
  let rf = !rootFuns in
  IntSet.iter (
    fun i -> 
      try begin
        let fs = H.find fun_to_funInfo i in
      try
        let size = effect_size fs.funEffect in
        let sum = fs.summary in
        let dist_locks = distLocksCum sum in
        log "RF: %30s Effect size: \
            %3d, #distinct locks: %3d.\n"
            !(fs.fun_dec).svar.vname size dist_locks
      with _ -> print_effect fs.funEffect
      end
      with
      | Not_found -> ()
  ) rf
