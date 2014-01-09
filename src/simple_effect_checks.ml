open Definitions 
open Simple_definitions
open Modsummary
open Effect_tools
open Strutil
open Cil
open Ciltools
module L = List
module D = Definitions

external inc_hash :  int -> int -> int  = "inc_hash"

(* Moved from effect_tools. Requicyan by this module as well*)
(* Do I have to check the called function? 
 * changed previous will_backtrack. 
 * *)
let will_backtrack vid = 
	begin  try
		let fs = Hashtbl.find simpleFInfoHash vid in
		fs.has_effect
	with Not_found ->
		(* this is an external function - we assume there is no effect here *)
		false
	end

(* check whether there exist any top-level lock-ops 
 * or any lock ops that WILL access the stack frame
 * *)
let rec nonEmptyEffect (f:simple_effect) : bool = 
 List.exists (function 
  | SLockOp _ -> true
  | SJoin el -> List.exists nonEmptyEffect el
  | SCall (_,_,_) -> false
  | SBpLoop _ -> false
 ) f 



(* PG: 
 * SECTION ---- Lock counting  
 *
 *
 *
 *)


type ctx_ci = Cil.location * string (* func name *)
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

let rec equal_myctx a b = 
  match a,b with
  | CEmpty, CEmpty -> true
  | CCall ((l1,s1),i1,mc1), CCall ((l2,s2),i2,mc2) ->
      (compareLoc l1 l2 = 0) && (s1 = s2) &&
      (i1 = i2) && (equal_myctx mc1 mc2)
  | CCons (i1,mc1), CCons (i2,mc2) ->
      (i1 = i2) && (equal_myctx mc1 mc2)
  | _ -> false

(* flattened effect type, only l+ *)
type seffect_t = (exp * myctx_t) list
(*counts_t : a triplet consisting of
 * #lexically scoped locks,
 * #stack-based locks,
 * #non-stack based locks
 *)
type count_t = (int * int * int * int)
  type lcounts_t = (myctx_t * exp * count_t) list


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
      | CCall((loc,nm),i,c') ->
         (myctx2str c') ^ "::" ^ 
         (spf "Call(%s,%s,%d)" nm (loc2strsmall loc) i) 
      | CCons(i,c') ->
        (myctx2str c') ^ "::Cons(" ^ (string_of_int i) ^ ")"  

   let seff2str (s:seffect_t) : string = 
     abs_list2string " ||| "
     (fun (exp,ctx) -> (exp2str exp) ^ "::" ^ (myctx2str ctx))
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
     (fun s (ctx,exp,cnt) ->
        spf "%s(%s\t||\t%s)%s\n" s 
            (myctx2str ctx) (exp2str exp) (cnt2str cnt)
     ) "" l

    (* print specific counts: *)          
    let lcounts2strsmall (l:lcounts_t) = 
     L.fold_left 
     (fun s (ctx,exp,cnt) ->
        spf "%s(%s\t||\t%s)\n" s 
            (myctx2str ctx) (exp2str exp)
     ) "" l


  (* PV changed this *)
  module ExpHashtbl = Hashtbl.Make (
         struct
           type t = (exp * myctx_t)
         let equal (e1,mc1) (e2,mc2) = 
           (Ciltools.compare_exp e1 e2 = 0)  &&
           (equal_myctx mc1 mc2)
         let hash (a,_) = Ciltools.hash_exp a
       end)


(* clocks: given an effect f return counts_t *)
let clocks f : (lcounts_t * count_t) = 
 (* create a mapping from locks operations to counts*)
 let (lock_map : (IntSet.t * count_t) ExpHashtbl.t) = 
     ExpHashtbl.create 32
 (*let (lock_map : ((exp * myctx_t), (IntSet.t * count_t)) Hashtbl.t) = 
     Hashtbl.create 32*)
 in
 (*ladd : TODO 
  * *)
 let ladd loc exp ctx a0 : unit =
   let vv = (exp,ctx) in
   let (visited,b0) =
   	try ExpHashtbl.find lock_map vv
   	with Not_found -> (IntSet.empty,(0,0,0,0))
   in
   let h = Hashtbl.hash (loc.file^(string_of_int loc.byte)) in
   if (IntSet.mem h visited) = false then 
   begin
      let (a,b,c,d) = sadd a0 b0 in
      let visited = IntSet.add h visited in
      ExpHashtbl.replace lock_map vv
      (visited,
      (if a > 0 && (b > 0 || c >0 || d > 0) then 
         (0,a+b,c,d)
       else 
         (a,b,c,d)
      ))
   end
 in
 (* plus: given an l- within context ctx, find the
  *            matching l+ in a flattend effect cf
  *)
 let plus  (loc:Cil.location) (ctx : myctx_t) (s: seffect_t)
           (exp:exp) : seffect_t = 
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
     | ((exp0,ctx0) as hd)::tl ->
       if  (compare_exp exp exp0) = 0 then
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
   ladd loc exp ctx t;
   s' 
 in
 (* makeresult: convert lock map to a more convenient format
  *             and calculate total counts
  * *)
 let makeresult () =
  let l = ref ([]:(myctx_t * exp * count_t) list) in
  let total = ref (0,0,0,0) in
  let it (a,b) (_,c) = 
      total := sadd !total c;
      l := (b,a,c) :: !l 
   in
   ExpHashtbl.iter it lock_map;
   (!l,!total)
 in
 (*let printmap () : unit =
    let (detail,cnt) = makeresult () in 
    pf "BEGIN DEBUG:\n%s\n%s:\n%s\n\nEND DEBUG"
      (ppcnt cnt) (green "LCOUNTS") (lcounts2str detail)
 in*)
 (* count:  given an effect f, a stack of l+ 
  *         (simplified effect seffect_t)  and a context c
  *         determine counts_t in that effect
  *)
 let rec count (c : myctx_t) 
               (s: seffect_t)
               (f : simple_effect)  : seffect_t =
  (* pf  "\nCOUNT :\n%s : %s\n%s: %s\n%s: %s\n" 
            (cyan "Context") (myctx2str c) 
            (cyan "Effect" ) (effect2str f)
            (cyan "Stack"  ) (seff2str s) ;*)
   match f with
      [] -> s
    | ae::ftl ->    
      begin match ae with
      |	SLockOp (loc,lt,exp) ->
            (*pf "\nCOUNT: lock op %s %b" (sexp2str sexp) lt;*)
        let s' = 
          if lt then (* lk+ operation *)
            (exp,c)::s
          else 
            plus loc c s exp
        in
       (* printmap ();*)
        count c s' ftl
      | SJoin flist ->
        let count' x =
            let c' = (CCons(Hashtbl.hash ae,c)) in 
            let s' = count  c' s x in
            let _  = count  c  s' ftl in 
            ()
        in
        L.iter count' flist;
        []
      | SCall (loc,nm,eff) ->
        let h = Hashtbl.hash (loc.file^(string_of_int loc.byte)) in
        let c1 = CCall ((loc,nm),h,c) in
        let s' = count c1 s eff in
        count c1 s' ftl
      | SBpLoop _ -> 
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
      let ht = H.find simpleFInfoHash vid in
      ht.sEffect
    with Not_found ->
      log "Effect not found!\n";
      [] 
  in
  let total = ref (0,0,0,0) in
  D.IntSet.iter ( fun vid ->
    let f0 = gf vid in
    let name = (Cilinfos.getVarinfo vid).vname in
    let (detail,cnt) = clocks f0 in
    log "\n%s  %s (vid:%d).\n%s\nEffect:\n\n%s\n"
      (magenta "Root function") name vid (ppcnt cnt) (effect2str f0);
      log "\n%s:\n%s\n" (green "LCOUNTS") (lcounts2str detail);
    total := sadd !total cnt
  ) !D.rootFuns;
  pf "\n%s:\n%s\n\n\n"
  (green "TOTAL") (ppcnt !total);
  log "END doCountLocks\n"


let total = ref (0,0,0,0) 

let initCountLocks () = 
  total := (0,0,0,0)
  
let doFuncCountLocks (seff:simple_effect) : unit =
  let (detail,cnt) = clocks seff in
  total := sadd !total cnt;
  (*let name = !curFunc.svar.vname in
  let vid = !curFunc.svar.vid in*)
  log "\nLock structure:\n\n%s\nEffect:\n%s" (ppcnt cnt) (effect2str seff)
  ;log "\n%s:\n%s\n" (green "LCOUNTS") (lcounts2str detail)

let aggregateCountLocks () = 
  pf "\n%s:\n%s\n" (green "TOTAL") (ppcnt !total)


