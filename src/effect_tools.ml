open Cil
open Symex_types
open Symex
open Definitions
open Modsummary
open Strutil
module LV = Lvals
module L = List
module DF = Dataflow
module H = Hashtbl


(*************************************************************************** 
 *
 *                    Effect Operations
 *
 ***************************************************************************)

(** Function that compares two lock operations based 
 * on their location on the input file. *)
let rec compare_lockops (a : atomic_effect) (b : atomic_effect) : bool =
  match a,b with
  (* This is the only case we need to check.
   * The check is done before Compl's are created. *)
  | LockOp ((l1,_,_), _ ,_,_) , LockOp ((l2,_,_), _ ,_,_) ->
        Cil.compareLoc l1 l2 = 0
        
  | Join fl1 , Join fl2 ->
  (* This assumes that the effects are in the same order of traversal,
   * which is reasonable. *)
    let rec list_comp f1 f2 = 
      match (f1, f2) with
      | ([], []) -> true
      | ([], _) -> false
      | (_,[]) -> false
      | ((f1::f1s), (f2::f2s)) ->
        if compare_effects f1 f2 then list_comp f1s f2s
        else false
    in
      list_comp fl1 fl2
  | NCall ((l1,_, _, _,_), _), NCall ((l2,_, _, _,_), _)   ->
    Cil.compareLoc l1 l2 = 0
  | RCall ((l1,_, _, _,_), _), RCall ((l2,_, _, _,_), _)   ->
    Cil.compareLoc l1 l2 = 0
  | Assign (_,_,c1), Assign (_,_,c2) -> compareCtx c1 c2
  | BpLoop i1, BpLoop i2 -> i1 == i2
  | _ -> false

and
(* Function that compares two effects. *)
compare_effects (f1 : effect) (f2 : effect) : bool =
  match (f1, f2) with
  | ([], [])	-> true
  | ([], _)	-> false
  | (_, [])	-> false
  | (l1 :: f1s , l2 :: f2s ) ->
    if compare_lockops l1 l2 then compare_effects f1s f2s
    else false

(* Checks if ae exists in e *)
let rec existInEffect ae e : bool = 
  match e with
  | (Join el)::tl ->  
      if not (L.exists (existInEffect ae) el) then
        existInEffect ae tl
      else true
  | hd :: tl -> 
      if not (compare_lockops hd ae) then 
        existInEffect ae tl
      else true
  | [] -> false


(* Return the location of an atomic effect *)
let get_location ae = 
  match ae with
  | LockOp ((l,_,_),_,_,_)
  | NCall ((l,_,_,_,_),_)
  | RCall ((l,_,_,_,_),_)
  | Assign (_,_,(l::_)) -> l 
  | _ -> locUnknown


(* Checks if ae is the last element in e - deep search in Join *)
let rec lastElement ae e : bool = 
  match e with
  | [Join el] -> L.exists (lastElement ae) el
  | [se] -> compare_lockops se ae
  | _ :: tl -> lastElement ae tl
  | [] -> false

(* Traverse effect and apply function f in each atomic operator *)
let rec effectUTraversal (func:atomic_effect->unit) (f:effect) : unit =
  L.iter (
    fun ae ->
      match ae with
      | Join fl -> L.iter (effectUTraversal func) fl
      | _ -> func ae
  ) f

(* Checks if all elements of effect f comply with pred *)
let rec effectTraversal (pred:atomic_effect->bool) (f:effect) : bool =
  if f = [] then false
  else
    L.for_all (
      fun ae ->
        match ae with
        | Join fl -> L.for_all (effectTraversal pred) fl
        | _ -> pred ae
    ) f
  
(* Iteratively apply transform to effect, until measure remains the same.*)
let rec fixFunc (measure:'a -> 'b) (transform:'a->'a) (effect:'a) = 
  let old_measure = measure effect in
  let effect' = transform effect in
  let new_measure = measure effect' in
  if Pervasives.compare old_measure new_measure <> 0 then 
    fixFunc measure transform effect'
  else
    effect'


(* Find the common predicate of two effects e1 and e2. Also return the rest of
 * each effect *)
let rec common_pred e1 e2 = 
  match e1,e2 with
  | [],_ -> ([],[],e2)
  | _,[] -> ([],e1,[])
  | h1::t1,h2::t2 -> 
      if compare_lockops h1 h2 then
        let (cp,r1,r2) = common_pred t1 t2 in
        (h1::cp,r1,r2)
      else ([],e1,e2)

let subEffect e1 e2 =
  match e1,e2 with
  | [], _ -> true
  | _, [] -> false  
  | _, _ -> effectTraversal (fun ae -> existInEffect ae e2) e1


(* Returns true if e1 is a prefix effect of e2. Empty effect is not considered a
 * prefix of anything, cause it would not preserve () ? f. *)
let rec prefixEffect first_time e1 e2 =
  match e1, e2 with
  | [], _ -> not first_time
  | _, [] -> false
  | (x::xs), (y::ys) when compare_lockops x y -> prefixEffect false xs ys
  | _, _ -> false

(* Returns true if e1 is a subset effect of e2 (all elements of e1 
 * are also in e2). Empty effect is not considered a subset of anything,
 * cause it would not preserve () ? f. *)
let rec subsetEffect e1 e2 =
  match e1, e2 with
  | [], _ -> false
  | _, [] -> false
  | _, _ -> effectTraversal (fun ae -> existInEffect ae e2) e1

(* Optimization that removes from a list of effects the effects that are 
 * represented by another super-effect *)
(* Using subsetEffect (and not prefix effect), to include cases where part of 
 * an effect is subsumed in a path of the super-effect. *)
let rec prefixEffectOpt el : effect list =
  match el with
  | (e::tl) ->
      let tl' = 
        List_utils.remove_if 
          (fun s -> subsetEffect s e) tl in
      if L.exists (fun t -> subsetEffect e t) tl' then 
        prefixEffectOpt tl' 
      else 
        e::(prefixEffectOpt tl')      
  | l -> l

 
(*************************************************************************** 
 *
 *                Effect comparisons / count checks
 *
 ***************************************************************************)

let wrong_counts : SexpSet.t ref = ref SexpSet.empty
let add_wrong_count s = 
  wrong_counts := SexpSet.add s !wrong_counts
let reset_wrong_counts _ = 
  wrong_counts := SexpSet.empty
let get_wrong_counts _ = 
  !wrong_counts


(* Find the number of unmatch lock/unlock operations for an effect f,
 * given a history of unmatcehd ops in m. typ determines if we are
 * looking for lock or unlock operations. *)
let rec eff2Map typ (m:int SexpMap.t) (f:effect) : int SexpMap.t = 
  L.fold_left (
  fun fm ae ->
    match ae with
    |	LockOp ((loc,_,_), lt, s,_) ->          
        if typ == lt then
          let cc = try SexpMap.find s fm with Not_found -> 0 in
          SexpMap.add s (cc+1) fm  
        else
          (try
            let cc = SexpMap.find s fm in
            let n = Pervasives.max (cc-1) 0 in
            SexpMap.add s n fm
          with Not_found -> fm)
          
    | Join fl ->          
        let fl' = if typ then fl else L.map L.rev fl in
        let mapL = L.map (eff2Map typ fm (*SexpMap.empty*)) fl' in
        (*let _ = L.iter (SexpMap.iter 
                        (fun s i -> log "| %b | %s -> %d\n" typ 
                                    (sexp2strsmall s) i))
                        mapL in
        let _ = log "----\n" in*)
        L.fold_left (
          fun feed mp  -> 
            SexpMap.fold (
              fun s i f ->
                if not (SexpMap.mem s f) then
                  SexpMap.add s i f 
                else f
            ) mp feed
        ) SexpMap.empty mapL
    | NCall ((loc,_,_, vi,_), rr) -> 
        begin try
          let ce = must_resolved "eff2Map" rr in
          let ce' = if typ then ce else L.rev ce in
          eff2Map typ fm ce'
        with _ -> fm
        end
    | _ -> fm (* rest cases unimportant for now *)
) m f

(* Compare two effect maps *)
let compSumMaps a b = 
  let single_check m s i acc =
    let ch = 
      (try (if SexpMap.find s m = i then true
        else false)
      with Not_found -> (i = 0)) in
    if not ch then 
      add_wrong_count s;
    acc && ch      
  in
  (SexpMap.fold (single_check a) b true) &&
  (SexpMap.fold (single_check b) a true)

let rec compSumMapList mlist : bool =
  match mlist with
  | [ ] -> true
  | [_] -> true
  | (m :: tl) -> L.for_all (compSumMaps m) tl

  
(* Function that checks if an effect has unmatched lock or 
 * unlock operations. *)
let has_unmatched_aux (typ:bool) (f:effect) : bool = 
  let m = 
    if typ then
      eff2Map true SexpMap.empty f
    else
      eff2Map false SexpMap.empty (L.rev f)
  in
  let chmap m = 
    SexpMap.fold (fun s i f -> (i!=0) || f) m false in
  chmap m

let has_unmatchedL (f:effect) : bool = 
  has_unmatched_aux true f

let has_unmatchedU (f:effect) : bool = 
  has_unmatched_aux false f

let has_unmatched (f:effect) : bool =
  has_unmatchedL f || has_unmatchedU f
 

(*************************************************************************** 
 *
 *                    Effect Simplifications
 *
 ***************************************************************************)

(* is_garbage : returns true if an effect does not contain any LockOps *)
let rec is_garbage (f:effect) : bool = 
	try
  List.iter 
  ( fun a -> 
      match a with 
      | LockOp _ -> 
        raise Not_found
      | Join el ->
        if List.exists (fun x -> not (is_garbage x)) el
        then raise Not_found
      | NCall (ci,res) -> 
           let f' = must_resolved "is_garbage" res in
           if not (is_garbage f') then raise Not_found
      | RCall _ ->
      (* assuming that recursive calls have no effect *)
      (* changed this because it gave an error *)
           (*rs_not_implemented "is_garbage/RCall"*) ()
      | Assign _ -> raise Not_found
      | BpLoop _ -> raise Not_found
  ) f; 
  true
 with 
  | Not_found ->  false


(* sgarbage: Remove garbage nodes from effect. *)
let sgarbage (f:effect) : effect =
  let rec sgarbage0 (f0:effect) : effect =
    List.fold_left (
      fun f' a  ->
        f' @
        match a with 
        | LockOp _ -> [a]
        | Join el ->
            (* See if all elements of the Join are empty*)
            let non_empty = L.exists (fun e -> not (is_garbage e)) el in
            if non_empty then
              begin
                (* Are there any empty effects in the list? *)
                let has_empty = L.exists is_garbage el in
                let has_unm = L.exists has_unmatched el in
                let is_summary = L.exists (effectTraversal 
                  (fun ae -> (get_location ae).line =  -2)) el in
                (* Filter the empty ones *)
                let l' = List.filter (fun x -> not (is_garbage x)) el in
                (* And if there were (one or more) empty, just insert one.*)
                let l'' = 
                  if has_empty && (has_unm || is_summary) then 
                    []::l' else l' 
                in
                match l'' with
                | []  -> []
                | [[]] -> []
                | [a] -> a
                |  _  -> [Join (L.map sgarbage0 l'')]
              end
            else
              []
        | NCall ((_,_,_,vi,_) as ci,res) -> 
            begin try
              let f' = must_resolved "sgarbage0" res in
              if is_garbage f' then []
              else [NCall (ci,mkresolved (sgarbage0 f'))]
            with _ -> []
            end
            (* The case of recursive call should have been taken care of. *)
        | RCall _ -> [] (*rs_not_implemented "sgarbage0/RCall"*)
        | Assign _ -> [a]
        | BpLoop _ -> [a]
    ) [] f0

  in sgarbage0 f



(* Remove the locations from the effect *)
let rec removeLocations (f:effect) : effect = 
  L.map (function
    | LockOp ((_,a,b),c,d,e) -> LockOp ((locUnknown,a,b),c,d,e)
    | Join el -> Join (L.map removeLocations el)
    | NCall (ci,res) -> 
        NCall (ci, 
        mkresolved 
          (removeLocations (must_resolved "removeLocations" res)))
    | _ as a -> a) f


(* Effect list transformation:
   [{e1 ? e2 ? ... ? en} ; f1 ; ... ; fm] -> 
   [e1 ; e2 ; ... ; en ; f1 ; ... fm]
*)
let rec inlineEL el = 
  let getJoinList ae =  
    match ae with 
    (* Inline the contents of a join, with recursive call*)
    | [Join l] -> L.map inlineEff l 
    | [a] -> [[a]]
    (* Recursive call *)
    | elist -> [inlineEff elist]
  in
  let jl = L.map getJoinList el in
  let cjl = L.concat jl in
  let cjl' = prefixEffectOpt cjl in
  cjl'

and inlineEff e = 
  L.fold_left (
    fun f ae -> 
      match ae with
      | Join el -> begin
          let el' = inlineEL el in
  (*let _ = L.iter (fun s -> log "Before inlineEL:"; print_effect s) el in
  let _ = L.iter (fun s -> log "After inlineEL:"; print_effect s) el in
  let _ = log "===================\n" in*)
          match el' with
          | [e] -> f @ e
          | _   -> f @ [Join el']
        end
      | ae -> f @ [ae]
  ) [] e

(* This effect is supposed to be straigth line, because it is a summary *)
let rec distLocksInEff (f: effect) = 
  L.fold_left (
    fun ss lo -> 
      match lo with
      | LockOp (_,_,s,_) -> 
          SexpSet.add s ss
      | Join el -> 
          L.fold_left 
            (fun m eff -> 
              SexpSet.union m (distLocksInEff eff))
            ss el
      | NCall (_,rr) -> 
          SexpSet.union ss (distLocksInEff (must_resolved "distLocksInEff" rr))
      | _ -> ss
  ) SexpSet.empty f

let numDistLocksInEff ss = 
  SexpSet.cardinal (distLocksInEff ss)

(* simplify calls:	( for code generation )
   *
   * removes NCall nodes and inlines their effects
   * except for the top-level ones
   * that are currently required as markers when translating
   * type-level effects to run-time effects
   *
   * TODO: RCall  
 *)

let scall (f:effect) : effect =
let rec scall0 level (f:effect) : effect =
  List.fold_left (
    fun f' elt -> 
      f' @
      match elt with 
      | NCall (ci,res) ->
          let f'' = must_resolved "scall0/NCall" res in
          if level = 0 then begin
            let (_,_,_,vi,_) = ci in
            dlog "SCall: Adding a NCall(%s,[])\n" vi.vname ; 
            (scall0 (level+1) f'') @ [NCall (ci,mkresolved [])]
          end
          else
            (scall0 (level+1) f'')
      | Join el ->
          ((Join (List.map (scall0 level) el))::[])
      | RCall _ ->
          raise (Not_implemented "scall/Recursive_call")
      | LockOp _ | Assign _ -> [elt]
      | BpLoop _ -> [elt]
    ) [] f
in
scall0 0 f

 
(* How long will the __effect_** array be ? *)
let rec effect_size (f:effect) : int =
  let len = List.length f in
  if len = 0 then 0
  else 
    let inner_sz =  List.fold_left (fun sz a ->
      sz+ 
      match a with
      | LockOp _ -> 1
      | Join el -> 
        List.fold_left (fun sz f0-> sz + (effect_size f0)) 1 el
      (* the effect has been inlined *)
      | NCall (_,res_f) -> 
        let f' = must_resolved "effect_size" res_f in
        1 + (effect_size f') 
      | RCall _ -> 1
      | Assign _ -> rs_impossible "effect_size/Assign"
      | BpLoop _ -> 1
      ) 0 f  
    in
    inner_sz + (if len = 1 then 0 else len)



(*************************************************************************** 
 *
 *                    Effect Optimizations
 *
 ***************************************************************************)

let rec common_prefix_opt (pre : effect) (rest : effect list) : 
  (effect * effect list) =
  match rest with
  | [] -> (pre, [])
  | [e] -> (pre @ e, [])
  | (x::xs) ->
    let pred a =
      try (compare_lockops (L.hd a) (L.hd x))
      with Failure("hd") -> false		
    in
    if (L.for_all pred xs) then
      common_prefix_opt (pre @ [L.hd x]) (L.map (L.tl) rest)
    else
      (pre,rest)

let plusMap f = eff2Map true SexpMap.empty f
let minusMap f = eff2Map false SexpMap.empty (L.rev f)


let effect_count_check (fl:effect list) : unit = 
  let _ = reset_wrong_counts () in
  let pmapL = L.map plusMap fl in
  let mmapL = L.map minusMap fl in
  if not ((compSumMapList pmapL) && (compSumMapList mmapL)) then
    let loc = get_stmtLoc (!call_stmt.skind) in
    let wrong_locks = 
      SexpSet.fold 
        (fun s str -> str ^ (exp2str (sexp2exp s) ^ "\n")) 
                      (get_wrong_counts ()) "" 
    in      
    error_set := StringSet.add
      ("["^(loc2strsmall loc)^"] The number of unmatched (un)lock operations\n\
      doesn't match in each path. This will affect all outer joins.\nCheck lock \
      operations on the following lock(s):\n"^wrong_locks^"\n")
      !error_set

     
let enable_checks = ref true
(*
(* Helpful function that takes effect and returns it optimized *)
let rec cp_effect (f : effect) : effect = 
  let rec cp_opt_aux (eff : effect) (acc : effect) = 
    match eff with
    | []            -> acc
    | (Join fl)::fs -> cp_opt_aux fs (acc @ (cp_effect_list_nocheck fl))
    | f::fs         -> cp_opt_aux fs (acc @ [f])
  in
  cp_opt_aux f []

and cp_effect_list_nocheck fl = 
  cp_effect_list false fl

and cp_effect_list_check fl = 
  cp_effect_list true fl

and cp_effect_list (check:bool) (fl: effect list) : (effect) =
  let fl' = L.map cp_effect fl in
  let _ = 
    if check then 
      begin
        (*log "%s\n" line; 
        L.iter (fun f -> print_effect f) fl';*)
        effect_count_check fl'
      end
  in
  let pre,fl'' = common_prefix_opt [] fl' in
  match fl'' with
  | [ ] -> pre
  | [_] -> pre @ (L.hd fl'')
  |  _  -> 
      if L.exists has_unmatched fl'' then
        pre @ [Join fl'']
      else
        pre @ (sgarbage [Join (L.filter (fun x -> not (is_garbage x)) fl'')])
*)
       
module AtomicEffectMap = Mapset.Make (
       struct
         type t = atomic_effect
         let compare = Pervasives.compare
       end)

(* experimental more aggressive common prefix optimization *)
let rec cp_effect_list (check: bool) (fl: effect list) : effect =
  let _ = if check then 
    begin
      (*log "%s\n" line; 
      L.iter (fun f -> print_effect f) fl';*)
      effect_count_check fl
    end
  in
  (* Returns a mapping from the first element to a list with the rest of the
   * effect, and a bool telling if we found an empty effect in the list. *)
  let effList2map (fl: effect list): ((effect list) AtomicEffectMap.t * bool) =
    L.fold_left (
      fun (accmap,b) eff ->
        try 
          let hd = L.hd eff in
          let tl = L.tl eff in
          try
            let l = AtomicEffectMap.find hd accmap in
            (AtomicEffectMap.add hd (tl::l) accmap,b)
          with Not_found ->
            (AtomicEffectMap.add hd [tl] accmap,b)
        (* This finds empty effects in the list *)
        with Failure("hd") ->
          (accmap,true)
    ) (AtomicEffectMap.empty,false) fl
  in
  
  let map2eff ((m,b):((effect list) AtomicEffectMap.t * bool)) :
      effect = 
    match AtomicEffectMap.cardinal m with
    | 0 -> []
    | 1 -> 
        (* Mapset.choose returns the sole element *)
        let (hd,tl) = AtomicEffectMap.choose  m in
        let cpl = cp_effect_list_nocheck tl in
        if b then [Join [ [] ; hd::cpl]]
        else hd::cpl
    | _ -> 
        let ll = AtomicEffectMap.fold (
            fun hd tl eff ->
              let cpl = cp_effect_list_nocheck tl in
              (hd::cpl) :: eff)
            m [] in
        if b then [Join ([]::ll)]
        else [Join ll]

  in
  let (m,b) = effList2map fl in
  map2eff (m,b)

and cp_effect (f : effect) : effect = 
  let rec cp_opt_aux (eff : effect) (acc : effect) = 
    match eff with
    | []            -> acc
    | (Join fl)::fs -> cp_opt_aux fs (acc @ (cp_effect_list_nocheck fl))
    | f::fs         -> cp_opt_aux fs (acc @ [f])
  in
  cp_opt_aux f []

and cp_effect_list_nocheck fl = 
  cp_effect_list false fl

and cp_effect_list_check fl = 
  cp_effect_list true fl


        
let fixInline = 
  fixFunc effect_size (fun e -> sgarbage (cp_effect (inlineEff e)))
   


(***************************************************************************
 *
 *                Post-computation effect operations
 *
***************************************************************************)

let rec remove_assign (f:effect) : effect =
  match f with
  | (Assign _::tl) -> remove_assign tl
  | (Join fl)::tl -> (Join (L.map remove_assign fl))::(remove_assign tl)
  | (NCall (ci, e)) ::tl -> begin
      match !e with
      | Resolved res ->
          let res' = remove_assign res in
          (NCall (ci, ref (Resolved res'))) :: remove_assign tl
      | _ -> (NCall (ci, e)) :: (remove_assign tl)
    end
  | hd::tl -> hd::(remove_assign tl)
  | [] -> []
 

let rec filterBp i effect = 
  L.fold_left (
    fun feed ae ->
      match ae with
      | BpLoop j -> 
          if i <> j then feed @ [ae]
          else feed
      | Join el -> 
          feed @ [Join (L.map (filterBp i) el)]
      | _ -> 
          feed @ [ae]
  ) [] effect


(** Effect summaries - 
 * This summary is for optimizing the inlined effect. *)
let summarize (f:effect) : effect = 
  let plusM = eff2Map true SexpMap.empty f in
  let minusM = eff2Map false SexpMap.empty (L.rev f) in
  (*let _ = SexpMap.iter (fun s i -> log "| + | %s -> %d\n"
                (sexp2strsmall s) i) plusM in
  let _ = SexpMap.iter (fun s i -> log "| - | %s -> %d\n" 
                (sexp2strsmall s) i) minusM in*)
  let mkl se = LockOp(summaryLI, true,se,getMemoryType se) in
  let mku se = LockOp(summaryLI,false,se,getMemoryType se) in
  let rec mktm n acc a = 
    if n > 0 then mktm (n-1) (a::acc) a else acc in
  let lmap2eff m sum =
    SexpMap.fold (
      fun se l (p,z,s) ->
        if l == 0 then 
          (p,(mkl se)::(mku se)::z, s)
        else
          ((mktm l [] (mkl se)) @ p, z,s)
      ) m sum in
  let ulmap2eff m sum =
    SexpMap.fold
      (fun se u (p,z,s) -> (p,z, (mktm u [] (mku se)) @ s))
      m sum in
  
  let lsum = lmap2eff plusM ([],[],[]) in
  let ulsum = ulmap2eff minusM lsum in
  let (p,z,s) = ulsum in p @ z @ s


(* Hash ref that points to the hashtable that contains the loop effects for the
 * current function. *)
let loopHashRef = ref (H.create 10)


let is_empty_effect f =
  match f with [] -> true | _ -> false

(* Create an effect list from a mapping of effect inputs. 
 * Empty effects are inserted only once. *)
let fmap2flist fm =
  snd(IntMap.fold (
    fun i f (hasblank,feed) ->
      if f = [] && hasblank then (true,feed)
      else (is_empty_effect f, f::feed)
  ) fm (false,[]))

(*
(* Backpatch the effect of the loops in the BpLoop atomic effects *)
let rec backpatch (f : effect) =
  let rec bp_aux f acc = 
    match f with 
    | (BpLoop (i) :: fun_rem ) ->
        let inj = try 
          let meff = H.find !loopHashRef i in
          let leff = fmap2flist meff in
          let sg = sgarbage (cp_effect_list_check leff) in
          sg
          with Not_found -> 
            (warn "Backpatching went wrong.\n"; [])
            (*rs_impossible "backpatch/0"*) in
        (* Hack needed to avoid eternal recursion - filtering must be deep *)
        let inj1 =  (sgarbage (filterBp i inj)) in
        let inj2 =  (sgarbage ((*backpatch*) inj1)) in
        let fun_rem1 = sgarbage ((*backpatch*) fun_rem) in
        (* f1 : effect that will be executed at least once
         * f2 : effect that might not be executed
         * f3 : effect of the rest of the function *)
        let (f1,f2,f3) = common_pred inj2 fun_rem1 in
        let (f1,f2,f3) = (backpatch f1, backpatch f2,backpatch f3) in
        let must = acc @ f1 in
        let remaining = f3 in
        (* Also, in case of a 'while', we need to re-examine
         * the loops effect, that's why we append slooping' 
         * after the loops effect. *)
        (* This is only needed when the loop has unmatched 
         * lock or unlock operations. *)
        let looping' = 
          let lf = f1 @ f2 in
          if has_unmatched lf && numDistLocksInEff lf > 1 then
            (*let _ = log "###Loop %d, has unmatched.\n" i in*)
            let looping = sgarbage (f2 @ f1) in
            (*let _ = print_effect looping in*)
            let slooping' = [Join [[];summarize looping]] in
            sgarbage ( [Join [[];(looping @ slooping')]])
          else
            f2
        in
        (*PG: The loop can be executed zero 
         * or more times. Hence, we use Join. *)
        let total = must @ looping' in
        bp_aux remaining total
    | (Join el) :: tl ->
        let elt = Join (L.map backpatch el) in
        bp_aux tl (acc @ [elt])
    | ae :: tl  -> 
        bp_aux tl (acc @ [ae])
    | [] -> 
        acc
  in
  bp_aux f []
  
 *)

let next_effect e = 
  match e with
  | [Join el] -> el
  | [] -> []
  | _  -> [e]

(* Check if effect e is associated with one of the effects in el. If yes 
 * return true, the relevant effect from el, and el without it. *)
let associated_with e el : bool * effect * effect list = 
  match e with
  | [] -> (false,[],el)
  (* Try to find and distinguish from the rest, the part of the main effect
   * list that has a common part with the looping effect we are examining. *)
  | hd::tl -> try (true, 
                    L.find (fun eff -> 
                            (L.exists (compare_lockops hd) eff)) el,
                    L.filter (fun eff -> 
                        not (L.exists (compare_lockops hd) eff)) el)
              with Not_found -> (false,[],el)


(* Backpatch the effect of the loops in the BpLoop atomic effects *)
let rec backpatch (f : effect) =
  (* If the loop's and the function's effects are in a Join, we need something
   * deeper in order to inline the loop effect in the main. This function 
   * returns the new main effect list and the loop list that remains. *)
  let rec bp_list (loop_l: effect list) (main_l: effect list)  =
    L.fold_left (    
      fun (ml,ll) bpeff ->
        let (is_assoc,relevant,ml') = associated_with bpeff ml in
        if is_assoc then
          let (common,loop_rem,main_rem) = 
            common_pred bpeff relevant in
          begin
            if main_rem <> [] then (main_rem::ml',bpeff::ll)
            else (ml',bpeff::ll)
          end
            else
              (ml,bpeff::ll)
    ) (main_l,[]) loop_l

  (* Find the common predicate of two effects e1 and e2. 
   * Also return the rest of each effect *)
 and common_pred loop main =
    match loop,main with
    | [],_ -> ([],[],main)
    | _,[] -> ([],loop,[])
    | h1::t1,h2::t2 -> 
        if compare_lockops h1 h2 then
          let (cp,r1,r2) = common_pred t1 t2 in
          (h1::cp,r1,r2)        
        else
          begin
            (* try to handle the case where the effect we are trying to unify 
             * is in a path of a join *)
            match h1,h2 with
            | _,Join main_l ->
                let (ml,ll) =
                  (* 1st case: The loop effect is directly part of the 
                   * main effect in which we are trying to inline it.
                   * 2nd case: We have to unfold the loop effect in order 
                   * to inline it. 
                   * This is the best we can do for now. *)
                  let direct = L.exists (L.exists (compare_lockops h1)) main_l in
                  if direct then
                    bp_list [loop] main_l
                  else 
                    bp_list (next_effect loop) main_l
                in
                ([],[Join ll],(Join ml)::t2)
            
            | Join el, _  -> 
                (* Keep the remaining loop effects ([SJoin ll])
                 * The main effect was passed on its whole to to 
                 * bp_list, so don't insert t2 as before. *)
                let loop_l = L.map (fun e -> fixInline (e@t1)) el in
                let (ml,ll) = bp_list loop_l [main] in
                ([],[Join ll],[Join ml])
                
            (* we cannot do anything better for this case *)
            | _ -> 
                ([],loop,main)
          end
         
  (* The actual inlining of the loop effect at the placeholder. *)
  and inline inj fun_rem acc = 
    (* f1 : simple_effect that will be executed at least once
     * f2 : simple_effect that might not be executed
     * f3 : simple_effect of the rest of the function *)
    let (f1,f2,f3) = common_pred inj fun_rem in
    let (f1,f2,f3) = (fixInline f1, fixInline f2, fixInline f3) in
    (*let _ = 
      if !curFunc.svar.vid = 9151 then
        ((if f1 <> [] then (log "f1:"; print_effect f1));
        (if f2 <> [] then (log "f2:"; print_effect f2));
        (if f3 <> [] then (log "f3:"; print_effect f3))) in*)
    let must = acc @ f1 in
    let remaining = f3 in
    (* Also, in case of a 'while', we need to re-examine
     * the loops effect, that's why we append slooping' 
     * after the loops effect. *)
    (* This is only needed when the loop has unmatched 
     * lock or unlock operations. *)
    let looping' =
      let lf = f1 @ f2 in
      if (has_unmatched f1 || has_unmatched f2) && 
          numDistLocksInEff lf > 1 then
        let looping = f2 @ f1 in
        (* CAUTION: summarizing the looping makes it vulnerable
         * for sgarbage to remove the "() ?" *)
        let slooping' = [Join [[];summarize looping]] in            
        [Join [[];(looping @ slooping')]]
      else
        (* For the sake of counts, we have to append f1 to the loop
         * effect. If the backedge does not have an effect, don't 
         * append anything. *)
        begin if f2 = [] then [] else f2 @ f1 end
    in
    (*PG: The loop can be executed zero 
     * or more times. Hence, we use Join. *)
    let total = must @ looping' in
    bp_aux remaining total
  
  and bp_aux f acc = 
    match f with 
    | (BpLoop (i) :: fun_rem ) ->
        begin
          try 
            let inj = 
              let meff = H.find !loopHashRef i in
              let injl = fmap2flist meff in
              let fl = cp_effect_list_check injl in
              let _ = if L.length (fixInline (filterBp i fl)) = 0 then
                raise Not_found in
              fl
            in
            (* Hack needed to avoid eternal recursion - filtering must be deep *)
            let inj1 = fixInline (backpatch (filterBp i inj)) in
            let fun_rem1 = fixInline (backpatch fun_rem) in
            let result = inline inj1 fun_rem1 acc in 
            (*let _ = 
              if !curFunc.svar.vid = 9151 then
                (log "Backpatching %d:" i; print_effect inj1;
                log "Into:"; print_effect fun_rem1;
                log "Acc:"; print_effect acc;
                log "Result:"; print_effect (fixInline result))
            in*)
            result
          with Not_found ->  
            bp_aux fun_rem acc          
            (*rs_impossible "backpatch/0"*) 
        end

    | (Join el) :: tl ->
        let elt = Join (L.map backpatch el) in
        bp_aux tl (acc @ [elt])
    | ae :: tl  -> 
        bp_aux tl (acc @ [ae])
    | [] -> 
        acc
  in
  bp_aux f []
  
 

module LocSet = Set.Make (
       struct
         type t = location
         let compare = Cil.compareLoc
       end)

exception LocationMissing of location 

module Sanity = struct

  let locSet : LocSet.t ref = ref LocSet.empty

  let register (loc:Cil.location) = 
    locSet := LocSet.add loc !locSet

  let remove loc = 
    locSet := LocSet.remove loc !locSet
  
  let reset () = 
    locSet := LocSet.empty

  let check_sanity (f:effect) =
    let check_atomic ae = 
      match ae with
      | LockOp ((loc,_,_),_,_,_) 
      | NCall ((loc,_,_,_,_),_) ->           
          remove loc
      | _ -> ()
    in
    effectUTraversal check_atomic f;
    LocSet.iter (
      fun l -> 
      err "Lock at %s was not included in the funciton's effect. This means \
      that there is a bug or that the lock operation is unreachable.\n"
      (loc2strsmall l)) !locSet

  end
  
