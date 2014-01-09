open Cil
open Ciltools
open Definitions
open Simple_definitions
module L = List
module H = Hashtbl


(*************************************************************************** 
 *
 *                    Effect Operations
 *
 ***************************************************************************)

(* How long will the __effect_** array be ? *)
let rec effect_size (f:simple_effect) : int =
  let size = List.fold_left (fun sz a ->
      sz+ 
      match a with
      | SLockOp _ -> 1
      | SJoin el -> 
          (* add the PATH *)
          List.fold_left (fun sz f0 -> sz + (effect_size f0)) 1 el
      | SCall (_,_,sum) -> 1 + effect_size sum
      (* this shouldn't be here *)
      | SBpLoop _ -> 0
    ) 0 f in
  let len = List.length f in
  if len = 0 then 0
  else if len = 1 then size
  (* add the SEQ *)
  else 1 + size



let rec effect_size_WO_inline (f:simple_effect) : int =
  let len = List.length f in
  if len = 0 then 0
  else 
    List.fold_left (fun sz a ->
      sz+ 
      match a with
      | SLockOp _ -> 1
      | SJoin el -> 
          List.fold_left (fun sz f0 -> sz + (effect_size f0)) 1 el
      | SCall _ -> 1
      (* this shouldn't be here *)
      | SBpLoop _ -> 0
      ) 0 f  

(** Function that compares two lock operations based 
 * on their location on the input file. *)
let rec compare_slockops
  (a : simple_atomic_effect)
  (b : simple_atomic_effect) : bool =
  match a,b with
  (* This is the only case we need to check.
   * The check is done before Compl's are created. *)
  | SLockOp (l1,_,_) , SLockOp (l2,_,_) ->
        Cil.compareLoc l1 l2 = 0        
  | SJoin fl1 , SJoin fl2 ->
  (* This assumes that the effects are in the same order of traversal,
   * which is reasonable. *)
    let rec list_comp f1 f2 = 
      match (f1, f2) with
      | ([], []) -> true
      | ([], _) -> false
      | (_,[]) -> false
      | ((f1::f1s), (f2::f2s)) ->
        if compare_seffects f1 f2 then list_comp f1s f2s
        else false
    in
      list_comp fl1 fl2
  | SCall (l1,_,_), SCall (l2,_,_) ->  Cil.compareLoc l1 l2 = 0
  | SBpLoop i1, SBpLoop i2 -> i1 == i2
  | _ -> false

and
(* Function that compares two effects. *)
compare_seffects (f1 : simple_effect) (f2 : simple_effect) : bool =
  match (f1, f2) with
  | ([], [])	-> true
  | ([], _)	-> false
  | (_, [])	-> false
  | (l1 :: f1s , l2 :: f2s ) ->
    if compare_slockops l1 l2 then compare_seffects f1s f2s
    else false

(* Checks if ae exists in e *)
let rec existInEffect ae e : bool = 
  match e with
  | (SJoin el)::tl ->  
      if not (L.exists (existInEffect ae) el) then
        existInEffect ae tl
      else true
  | hd :: tl -> 
      if not (compare_slockops hd ae) then 
        existInEffect ae tl
      else true
  | [] -> false



(* Return the location of an atomic effect *)
let get_location ae = 
  match ae with
  | SLockOp (l,_,_) -> l
  | SCall (l,_,_) -> l
  | _ -> locUnknown



(* Checks if ae is the last element in e - deep search in Join *)
let rec lastElement ae e : bool = 
  match e with
  | [SJoin el] -> L.exists (lastElement ae) el
  | [se] -> compare_slockops se ae
  | _ :: tl -> lastElement ae tl
  | [] -> false

(* Traverse effect and apply function f in each atomic operator *)
let rec effectUTraversal (func:simple_atomic_effect->unit) (f:simple_effect) : unit =
  L.iter (
    fun ae ->
      match ae with
      | SJoin fl -> L.iter (effectUTraversal func) fl
      | _ -> func ae
  ) f

(* Checks if all elements of effect f comply with pred *)
let rec effectTraversal (pred:simple_atomic_effect->bool) (f:simple_effect) : bool =
  if f = [] then false
  else
    L.for_all (
      fun ae ->
        match ae with
        | SJoin fl -> L.for_all (effectTraversal pred) fl
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


let subEffect e1 e2 =
  match e1,e2 with
  | [], _ -> true
  | _, [] -> false  
  | _, _ -> effectTraversal (fun ae -> existInEffect ae e2) e1


(* Returns true if e1 is a prefix effect of e2. Empty effect is not considered a
 * prefix of anything, cause it would not preserve () ? f. *)
let rec prefixEffect first_time e1 e2 =
  match e1, e2 with
  | [], _ -> if first_time then false else true
  | _, [] -> false
  | (x::xs), (y::ys) when compare_slockops x y -> prefixEffect false xs ys
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
let rec prefixEffectOpt el : simple_effect list =
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


let rec reverse_effect f = 
  let rec re_aux rest acc = 
    match rest with
    | [] -> acc
    | (SJoin el) :: tl -> re_aux tl ((SJoin (L.map reverse_effect el))::acc)
    | (SCall (l,i,f)):: tl -> re_aux tl ((SCall (l,i,reverse_effect f))::acc)
    | a :: tl -> re_aux tl (a::acc)
  in
  re_aux f []



(*************************************************************************** 
 *
 *                    Effect Simplifications
 *
 ***************************************************************************)

let wrong_counts : ExpSet.t ref = ref ExpSet.empty
let add_wrong_count s = 
  wrong_counts := ExpSet.add s !wrong_counts
let reset_wrg_counts _ = 
  wrong_counts := ExpSet.empty
let get_wrong_counts _ = 
  !wrong_counts


(* Find the number of unmatch lock/unlock operations for an effect f,
 * given a history of unmatcehd ops in m. typ determines if we are
 * looking for lock or unlock operations. *)
let rec eff2Map typ (m:int ExpMap.t) (f:simple_effect) : int ExpMap.t = 
  L.fold_left (
  fun fm ae ->
    match ae with
    |	SLockOp (_,lt,e) ->
        if typ == lt then
          let cc = try ExpMap.find e fm with Not_found -> 0 in
          ExpMap.add e (cc+1) fm
        else
          (try
            let cc = ExpMap.find e fm in
            let n = Pervasives.max (cc-1) 0 in
            ExpMap.add e n fm
          with Not_found -> fm)
          
    | SJoin fl ->
        let fl' = if typ then fl else L.map L.rev fl in
        let mapL = L.map (eff2Map typ fm) fl' in
        L.fold_left (
          fun feed mp  -> 
            ExpMap.fold (
              fun s i f ->
                if not (ExpMap.mem s f) then
                  ExpMap.add s i f 
                else f
            ) mp feed
        ) ExpMap.empty mapL
    | SCall (_,_,sf) -> 
        let ce' = if typ then sf else reverse_effect sf in
        eff2Map typ fm ce'
    | _ -> fm (* rest cases unimportant for now *)
) m f

(* Compare two effect maps *)
let compSumMaps a b = 
  let single_check m s i acc =
    let ch = 
      (try (if ExpMap.find s m = i then true
        else false)
      with Not_found -> (i = 0)) in
    if not ch then 
      add_wrong_count s;
    acc && ch      
  in
  (ExpMap.fold (single_check a) b true) &&
  (ExpMap.fold (single_check b) a true)

let rec compSumMapList mlist : bool =
  match mlist with
  | [ ] -> true
  | [_] -> true
  | (m :: tl) -> L.for_all (compSumMaps m) tl

  
(* Function that checks if an effect has unmatched lock or 
 * unlock operations. *)
let has_unmatched_aux (typ:bool) (f:simple_effect) : bool = 
  let m = 
    if typ then
      eff2Map true ExpMap.empty f
    else
      eff2Map false ExpMap.empty (L.rev f)
  in
  let chmap m = 
    ExpMap.fold (fun s i f -> (i!=0) || f) m false in
  chmap m

let has_unmatchedL (f:simple_effect) : bool = 
  has_unmatched_aux true f

let has_unmatchedU (f:simple_effect) : bool = 
  has_unmatched_aux false f

let has_unmatched (f:simple_effect) : bool =
  has_unmatchedL f || has_unmatchedU f



(* is_garbage : returns true if an effect does not contain any LockOps *)
let rec is_garbage (f:simple_effect) : bool = 
	try
  List.iter 
  ( fun a -> 
      match a with 
      | SLockOp _ -> raise Not_found
      | SJoin el ->
        if List.exists (fun x -> not (is_garbage x)) el
        then raise Not_found
      | SCall (_,_,_) -> raise Not_found
      | SBpLoop _ -> raise Not_found
  ) f; 
  true
 with 
  | Not_found ->  false


(* sgarbage: Remove garbage nodes from effect. *)
let sgarbage (f:simple_effect) : simple_effect =
let rec sgarbage0 (f0:simple_effect) : simple_effect =
  List.fold_left (
    fun f' a  ->
      f' @
      match a with 
      | SLockOp _ -> [a]
      | SJoin el ->
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
                if has_empty && ((*has_unm ||*) is_summary) then 
                  []::l' else l' 
              in
              match l'' with
              | []  -> []
              | [[]] -> []
              | [a] -> a
              |  _  -> [SJoin (L.map sgarbage0 l'')]
            end
          else
            []
      | SCall _ -> [a]
      | SBpLoop _ -> [a]
  ) [] f0

in sgarbage0 f


(* Remove the locations from the effect *)
let rec removeLocations (f:simple_effect) : simple_effect = 
  L.map (function
    | SLockOp (a,b,c) -> SLockOp (locUnknown,b,c)
    | SJoin el -> SJoin (L.map removeLocations el)
    | _ as a -> a) f


(* Effect list transformation:
   [{e1 ? e2 ? ... ? en} ; f1 ; ... ; fm] -> 
   [e1 ; e2 ; ... ; en ; f1 ; ... fm]
*)
let rec inlineEL el = 
  let getJoinList ae =  
    match ae with 
    (* Inline the contents of a join, with recursive call*)
    | [SJoin l] -> L.map inlineEff l 
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
      | SJoin el -> begin
          let el' = inlineEL el in
  (*let _ = L.iter (fun s -> log "Before inlineEL:"; print_seffect s) el in
  let _ = L.iter (fun s -> log "After inlineEL:"; print_seffect s) el in
  let _ = log "===================\n" in*)
          match el' with
          | [e] -> f @ e
          | _   -> f @ [SJoin el']
        end
      | ae -> f @ [ae]
  ) [] e

(*flaten optimization: = common prefix + inline_effect
  * {()?{ () ? effect }} -> {() ? effect}
  *)
(* Flatten an effect's empty paths and return true if the effect is a 
 * concatenation of Joins where there exists an empty path in each one.
 * Empty effects return false by default. *)
(*
let rec flattenEff (f:simple_effect) : (simple_effect * bool) =
  if L.length f = 0 then ([],false)
  else
    let (ael, bl) = L.split (L.map flattenAE f) in
    (sgarbage ael, L.for_all (fun a -> a) bl)

and flattenAE (ae : simple_atomic_effect) : simple_atomic_effect * bool =
    match ae with
    | SJoin el ->
        let (el',bl) = L.split (L.map flattenEff el) in
        let fel = el' in
        let empty_path = L.exists (function [] -> true | _ -> false) fel in
        let one_path_empty = L.exists (fun a -> a) bl in
        if one_path_empty then
          (SJoin (List.filter (fun x -> not (is_garbage x)) fel), true)
        else if empty_path then
          (SJoin ([]::(List.filter (fun x -> not (is_garbage x)) fel)), true)
        else
          (SJoin fel, false)
    | a -> (a, false) 

let flatten (f:simple_effect) : simple_effect = 
  fst(flattenEff f)
*)

(* This effect is supposed to be straigth line, because it is a summary *)
let rec distLocksInEff (f: simple_effect) = 
  L.fold_left (
    fun ss lo -> 
      match lo with
      | SLockOp (_,_,e) -> 
          ExpSet.add e ss
      | SJoin el -> 
          L.fold_left 
            (fun m eff ->
              ExpSet.union m (distLocksInEff eff))
            ss el
      | _ -> ss
  ) ExpSet.empty f

let numDistLocksInEff ss = 
  ExpSet.cardinal (distLocksInEff ss)


(*************************************************************************** 
 *
 *                Effect comparisons / count checks
 *
 ***************************************************************************)

let rec common_prefix_opt (pre : simple_effect) (rest : simple_effect list) :
  (simple_effect * simple_effect list) =
  let urest = List_utils.unique ~cmp:compare_seffects rest in 
  match urest with
  | [] -> (pre, [])
  | [e] -> (pre @ e, [])
  | (x::xs) ->
    let pred a =
      try (compare_slockops (L.hd a) (L.hd x))
      with Failure("hd") -> false		
    in
    if (L.for_all pred xs) then
      common_prefix_opt (pre @ [L.hd x]) (L.map (L.tl) urest)
    else
      (pre,urest)

let plusMap f = eff2Map true ExpMap.empty f
let minusMap f = eff2Map false ExpMap.empty (L.rev f)


(* Helpful function that takes effect and returns it optimized *)
(* IMPORTANT Optimization: Join { () ? f } can be substituted by f, if
 * there are no unmatched lock/unlock operations in f. *)
let rec cp_effect (f : simple_effect) : simple_effect = 
  let rec cp_opt_aux (eff : simple_effect) (acc : simple_effect) = 
    match eff with
    | []            -> acc
    | (SJoin fl)::fs -> cp_opt_aux fs (acc @ (cp_effect_list fl))
    | f::fs         -> cp_opt_aux fs (acc @ [f])
  in
  cp_opt_aux f []

and cp_effect_list (fl: simple_effect list) : simple_effect =
  let fl' = L.map cp_effect fl in
  let pre,fl'' = common_prefix_opt [] fl' in
  match fl'' with
  | [ ] -> pre
  | [eff] -> pre @ eff
  |  _  ->
      pre @ [SJoin fl'']


      
module SAtomicEffectMap = Mapset.Make (
       struct
         type t = simple_atomic_effect
         let compare = Pervasives.compare
       end)

(* experimental more aggressive common prefix optimization *)
let rec cp_effect_list_2 (fl: simple_effect list) : simple_effect = 
  (* Returns a mapping from the first element to a list with the rest of the
   * effect, and a bool telling if we found an empty effect in the list. *)
  let effList2map (fl: simple_effect list) :
      ((simple_effect list) SAtomicEffectMap.t * bool) =
    L.fold_left (
      fun (accmap,b) eff ->
        try 
          let hd = L.hd eff in
          let tl = L.tl eff in
          try
            let l = SAtomicEffectMap.find hd accmap in
            (SAtomicEffectMap.add hd (tl::l) accmap,b)
          with Not_found ->
            (SAtomicEffectMap.add hd [tl] accmap,b)
        (* This finds empty effects in the list *)
        with Failure("hd") ->
          (accmap,true)
    ) (SAtomicEffectMap.empty,false) fl
  in
  
  let map2eff ((m,b):((simple_effect list) SAtomicEffectMap.t * bool)) :
      simple_effect = 
    match SAtomicEffectMap.cardinal m with
    | 0 -> []
    | 1 -> 
        (* Mapset.choose returns the sole element *)
        let (hd,tl) = SAtomicEffectMap.choose  m in
        let cpl = cp_effect_list_2 tl in
        if b then [SJoin [ [] ; hd::cpl]]
        else hd::cpl
    | _ -> 
        let ll = SAtomicEffectMap.fold (
            fun hd tl eff ->
              let cpl = cp_effect_list_2 tl in
              (hd::cpl) :: eff)
            m [] in
        if b then [SJoin ([]::ll)]
        else [SJoin ll]

  in
  let (m,b) = effList2map fl in
  map2eff (m,b)

let cp_effect_2 (f : simple_effect) : simple_effect = 
  let rec cp_opt_aux (eff : simple_effect) (acc : simple_effect) = 
    match eff with
    | []            -> acc
    | (SJoin fl)::fs -> cp_opt_aux fs (acc @ (cp_effect_list_2 fl))
    | f::fs         -> cp_opt_aux fs (acc @ [f])
  in
  cp_opt_aux f []


        
let fixInline = 
  fixFunc effect_size (fun e -> sgarbage (cp_effect_2 (inlineEff e)))


(***************************************************************************
 *
 *                Post-computation effect operations
 *
***************************************************************************)


let rec filterBp i effect = 
  L.fold_left (
    fun feed ae ->
      match ae with
      | SBpLoop j -> 
          if i <> j then feed @ [ae]
          else feed
      | SJoin el -> 
          feed @ [SJoin (L.map (filterBp i) el)]
      | _ -> 
          feed @ [ae]
  ) [] effect


let distinctExps f = 
  let rec eff2expset es f = 
    L.fold_left (
      fun feed ae ->
        match ae with
        | SLockOp (_,_,e) -> ExpSet.add e feed
        | SJoin el -> L.fold_left eff2expset feed el
        | SCall (_,_,ef) -> eff2expset feed ef
        | _ -> feed
    ) es f
  in
  let es = eff2expset ExpSet.empty f in
  ExpSet.iter 
    (fun e -> log "  %s (len: %d)\n" 
      (exp2str e) (String.length (exp2str e))
    ) es
    


(*
 (*
 *
 * TOO COMPLICATED
 *
 * *)
exception Found of (int * int list)

(* Find the sequence in which a lock operation appears in an effect. 
 * typ: the type of lock operation *)  
let rankInEffect typ exp eff = 
  (* count: the current position
   * ranks: the possible ranks of the lock operation *)
  let rec rie_aux typ exp eff count ranks : (int * int list) = 
    let eff' = if typ then L.rev eff else eff in
    try
      L.fold_left (
        fun (cc,rnks) ae ->
          if L.length rnks > 0 then 
            raise (Found (cc,rnks))
          else
            match ae with
            | SLockOp (_,t,e) when t = typ ->
                if Ciltools.compare_exp exp e = 0 then
                  (cc+1,cc::rnks)
                else (cc + 1,rnks)
            (* in different paths, there maybe many different ranks,
             * so we keep all distinct ones. *)
            | SJoin el ->
                let (ccs,ranks) = L.split (L.map
                  (fun pf -> rie_aux typ exp pf cc ranks) el) in
                (L.hd ccs, L.concat ranks)
            | SCall (_,_,sf) -> 
                rie_aux typ exp sf cc ranks               
            | _ -> (cc,rnks)
      ) (count,ranks) eff'
      (* In the top level this is supposed to end with an exception, 
       * if not the function will return with an empty list of ranks *)
    with Found ccrnk -> ccrnk
  in
  snd (rie_aux typ exp eff 0 [])

let mklop typ e = SLockOp(summaryLocation,typ,e)
let rec mktm n acc a = 
  if n > 0 then mktm (n-1) (a::acc) a else acc


let map2EffectWithRanks typ m eff : simple_effect = 

  let rec lmap2eff_aux m (cc:int) : simple_effect =
    (* Check if the mapping is empty *)
    if ExpMap.is_empty m then []
    else
      let _ = 
        if cc > 20 then rs_impossible "map2EffectWithRanks" in
      let _ = log "Checking rank: %d.\n" cc in
      (* get all the exps for rank cc *)
      let ranks e = rankInEffect typ e eff in
      let exps = 
        ExpMap.fold (
          fun e cnts expl ->
            let rnks = ranks e in
            (*let _ = begin
                log "cc: %d : exp: %s " cc (exp2str e);
                L.iter (fun i -> log "%d " i) rnks;
                log "\n"
            end in*)
            if L.exists (fun i -> i == cc ) (ranks e) then
              (e,cnts)::expl
            else 
              expl
        ) m []
      in
      let len = L.length exps in
      let _ = log "Found %d exps in this rank (empty map: %b) .\n" 
        len (ExpMap.is_empty m) in

      if len > 1 then 
        [SJoin (L.map (
          fun (e,c) -> 
            (mktm c [] (mklop typ e)) @ 
            (lmap2eff_aux (ExpMap.remove e m) (cc))) exps)]
      else if len = 1 then
        let (e,c) = L.hd exps in
        (mktm c [] (mklop typ e)) @
        (lmap2eff_aux (ExpMap.remove e m) (cc+1))
      else        
        lmap2eff_aux m (cc+1)
  in
  let sum = lmap2eff_aux m 0 in
  if typ then reverse_effect sum else sum    
*)


exception Found of int

(* Find the sequence in which a lock operation appears in an effect. 
 * typ: the type of lock operation *) 
let rankInEffect typ exp eff = 
  (* count: the current position
   * ranks: the possible ranks of the lock operation *)
  let rec rie_aux eff cc = 
    match eff with      
    | [] -> cc
    | (SLockOp (loc,t,e)) :: tl  when t == typ -> 
        if Ciltools.compare_exp e exp = 0 then cc
        else rie_aux tl (cc + 1)

    | (SJoin el) :: tl  ->
        let flat = (L.concat el) @  tl in
        rie_aux flat cc
        
    | (SCall (_,_,sf)) :: tl -> 
        let flat = sf @ tl in
        rie_aux flat cc

    | _ :: tl  ->
        rie_aux tl cc
  in

  let eff' = if typ then reverse_effect eff else eff in
  rie_aux eff' 0

let mklop typ e = SLockOp(summaryLocation,typ,e)
let rec mktm n acc a = 
  if n > 0 then mktm (n-1) (a::acc) a else acc


let map2EffectWithRanks typ m eff : simple_effect = 
  let sz = effect_size eff in
  let rec lmap2eff_aux m (cc:int) : simple_effect =
    (* Check if the mapping is empty *)
    if ExpMap.is_empty m then []
    else
      let _ = 
        if cc > sz then rs_impossible "map2EffectWithRanks" in
      (*let _ = log "Checking rank: %d.\n" cc in*)
      (* get all the exps for rank cc *)
      let rank e = rankInEffect typ e eff in
      let exps = 
        ExpMap.fold (
          fun e cnts expl ->
            if rank e == cc then 
              (*let _ = log "  -> %s\n" (exp2str e) in*)
              (e,cnts)::expl
            else expl
        ) m []
      in
      let len = L.length exps in
      (*let _ = log "Found %d exps in this rank (empty map: %b) .\n" 
        len (ExpMap.is_empty m) in*)

      if len > 1 then 
        (*let _ = log "%s"  "more than 1 exps.\n" in*)
        [SJoin (L.map (
          fun (e,c) -> 
            (mktm c [] (mklop typ e)) @ 
            (lmap2eff_aux (ExpMap.remove e m) (cc + 1))) exps)]
      else if len = 1 then
        let (e,c) = L.hd exps in
        (mktm c [] (mklop typ e)) @
        (lmap2eff_aux (ExpMap.remove e m) (cc+1))
      else        
        lmap2eff_aux m (cc+1)
  in
  let sum = lmap2eff_aux m 0 in
  if typ then reverse_effect sum else sum    



(** Effect summaries - 
 * This summary is for optimizing the inlined effect. *)
let summarize (f:simple_effect) : simple_effect = 
  let plusM = eff2Map true ExpMap.empty f in
  let minusM = eff2Map false ExpMap.empty (L.rev f) in
  let mkl e = SLockOp(summaryLocation, true,e) in
  let mku e = SLockOp(summaryLocation,false,e) in
  let rec mktm n acc a = 
    if n > 0 then mktm (n-1) (a::acc) a else acc in
  (*let lmap2eff m sum =
    ExpMap.fold (
      fun se l (p,z,s) ->
        if l == 0 then 
          (p,(mkl se)::(mku se)::z, s)
        else
          ((mktm l [] (mkl se)) @ p, z,s)
      ) m sum in
  let ulmap2eff m sum =
    ExpMap.fold
      (fun se u (p,z,s) -> (p,z, (mktm u [] (mku se)) @ s))
      m sum in*)  
  (* Zero (middle) part - we can afford it if this is [] *)
  let z = [] 
    (*ExpMap.fold (
      fun se l z ->
        if l == 0 then (mkl se)::(mku se)::z
        else z
    ) plusM []*) in
  
  (* remove the zero's from plusM *)
  let plusM = ExpMap.fold (fun e i m ->
    if i > 0 then ExpMap.add e i m
    else m) plusM ExpMap.empty
  in
  (* remove the zero's from minusM *)
  let minusM = ExpMap.fold (fun e i m ->
    if i > 0 then ExpMap.add e i m
    else m) minusM ExpMap.empty
  in

  (* Print - debug *)
  (*let _ = begin
    log "plusM:\n";
    ExpMap.iter (
      fun exp counts -> 
        log "%s (cc:%d) "  (exp2str exp) counts;
        (*L.iter (fun i -> log "%d " i) (rankInEffect true exp f);*)
        log "%d " (rankInEffect true exp f);
        log "\n"
    ) plusM;
    log "minusM:\n";
    ExpMap.iter (
      fun exp counts -> 
        log "%s (cc:%d) "  (exp2str exp) counts;
        (*L.iter (fun i -> log "%d " i) (rankInEffect false  exp f);*)
        log "%d " (rankInEffect true exp f);
        log "\n"
    ) minusM;
  end in*)
  
  
  let p = map2EffectWithRanks true plusM f in
  (*log "Did plus.\n";*)
  let s = map2EffectWithRanks false minusM f in
  (*log "Did minus.\n";*)

  (*let lsum = lmap2eff plusM ([],[],[]) in
  let ulsum = ulmap2eff minusM lsum in
  let (p,z,s) = ulsum in *)
  
  let res = p @ z @ s in
  (*print_seffect res ; *)
  res


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


let next_effect e = 
  match e with
  | [SJoin el] -> el
  | [] -> []
  | _  -> [e]

(* Check if effect e is associated with one of the effects in el. If yes 
 * return true, the relevant effect from el, and el without it. *)
let associated_with e el : bool * simple_effect * simple_effect list = 
  match e with
  | [] -> (false,[],el)
  (* Try to find and distinguish from the rest, the part of the main effect
   * list that has a common part with the looping effect we are examining. *)
  | hd::tl -> try (true, 
                    L.find (fun eff -> 
                            (L.exists (compare_slockops hd) eff)) el,
                    L.filter (fun eff -> 
                        not (L.exists (compare_slockops hd) eff)) el)
              with Not_found -> (false,[],el)


(* Backpatch the effect of the loops in the BpLoop atomic effects *)
let rec backpatch (f : simple_effect) =
  (* If the loop's and the function's effects are in a Join, we need something
   * deeper in order to inline the loop effect in the main. This function 
   * returns the new main effect list and the loop list that remains. *)
  let rec bp_list (loop_l: simple_effect list) (main_l: simple_effect list)  =
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
        if compare_slockops h1 h2 then
          let (cp,r1,r2) = common_pred t1 t2 in
          (h1::cp,r1,r2)        
        else
          begin
            (* try to handle the case where the effect we are trying to unify 
             * is in a path of a join *)
            match h1,h2 with
            | _,SJoin main_l ->
                let (ml,ll) =
                  (* 1st case: The loop effect is directly part of the 
                   * main effect in which we are trying to inline it.
                   * 2nd case: We have to unfold the loop effect in order 
                   * to inline it. 
                   * This is the best we can do for now. *)
                  let direct = L.exists (L.exists (compare_slockops h1)) main_l in
                  if direct then
                    bp_list [loop] main_l
                  else 
                    bp_list (next_effect loop) main_l
                in
                ([],[SJoin ll],(SJoin ml)::t2)
            
            | SJoin el, _  -> 
                (* Keep the remaining loop effects ([SJoin ll])
                 * The main effect was passed on its whole to to 
                 * bp_list, so don't insert t2 as before. *)
                let loop_l = L.map (fun e -> fixInline (e@t1)) el in
                let (ml,ll) = bp_list loop_l [main] in
                ([],[SJoin ll],[SJoin ml])
                
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
        ((if f1 <> [] then (log "f1:"; print_seffect f1));
        (if f2 <> [] then (log "f2:"; print_seffect f2));
        (if f3 <> [] then (log "f3:"; print_seffect f3))) in*)
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
        let slooping' = [SJoin [[];summarize looping]] in            
        [SJoin [[];(looping @ slooping')]]
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
    | (SBpLoop (i) :: fun_rem ) ->
        begin
          try 
            let inj = 
              let meff = H.find !loopHashRef i in
              let injl = fmap2flist meff in
              let fl = cp_effect_list_2 injl in
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
                (log "Backpatching %d:" i; print_seffect inj1;
                log "Into:"; print_seffect fun_rem1;
                log "Acc:"; print_seffect acc;
                log "Result:"; print_seffect (fixInline result))
            in*)

            result
          with Not_found ->  
            let _ = if !curFunc.svar.vid = 1014 then 
                log "####DIDN'T FIND IT\n" in
            bp_aux fun_rem acc          
            (*rs_impossible "backpatch/0"*) 
        end

    | (SJoin el) :: tl ->
        let elt = SJoin (L.map backpatch el) in
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


module Sanity = struct

  let locSet : LocSet.t ref = ref LocSet.empty

  let register (loc:Cil.location) = 
    locSet := LocSet.add loc !locSet

  let remove loc = 
    locSet := LocSet.remove loc !locSet
  
  let reset () = 
    locSet := LocSet.empty

  let check_sanity (f:simple_effect) =
    let check_atomic ae = 
      match ae with
      | SLockOp (loc,_,_) 
      | SCall (loc,_,_) ->
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
  
