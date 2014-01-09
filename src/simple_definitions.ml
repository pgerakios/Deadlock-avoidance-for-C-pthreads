open Cil
open Ciltools 
open Pretty 
open Definitions
module H = Hashtbl

type simple_atomic_effect = 
  | SLockOp  of (location * bool * exp)
  | SJoin    of simple_effect list  
  | SCall    of (location * string * simple_effect)
  | SBpLoop  of int

and simple_effect = simple_atomic_effect list 

module ExpMap = Map.Make (
  struct 
    type t = exp
    let compare a b = 
      String.compare (exp2str a) (exp2str b)
      (*compare_exp*)
  end
)

module ExpSet = Set.Make (
  struct 
    type t = exp
    (*This is too simple, but it didn't work well before *)
    (*let compare = compare_exp*)
    let compare a b = 
      String.compare (exp2str a) (exp2str b)
  end
)
	
module Int = struct
  type t = int
  let compare = Pervasives.compare
end
module IntSet = Set.Make(Int)
module IntMap = Map.Make (Int)

(** ********************************** *)

type simpleFunInfo_t = {
  mutable sFundec : Cil.fundec ;
	(* This the entire effect of the function.*)
	mutable sEffect : simple_effect ;	
	(* The function's effect summary *)
	mutable summary : simple_effect ;
  (* Set containing all the loop nodes. *)
  mutable loopSet : IntSet.t;
  (* Mapping from loop nodes to their effect. *)
  mutable loopEffect : simple_effect IntMap.t;
	(* True if the function has lock opreations or function calls
   * that matter to our analysis, else false. *)
	mutable has_effect : bool;
  (* Summary of the lock counts *)
  mutable fun_lock_count : int ExpMap.t;
  (* Have we examined this function yet? *)
  mutable examined : bool;
}

let simpleFInfoHash : (int, simpleFunInfo_t) H.t =
   H.create 3000

let mkDummySFstruct () = {
  sFundec = dummyFunDec;
  sEffect = [];
  has_effect = false;
  summary = [];
  loopSet = IntSet.empty;
  loopEffect = IntMap.empty;
  fun_lock_count = ExpMap.empty;
  examined = false;
}

let cur_sfstruct : simpleFunInfo_t ref = ref (mkDummySFstruct ()) 


(* for output in terminal *)
let rec d_lockOp' () (lo : simple_atomic_effect) : Pretty.doc =
	match lo with
	| SLockOp (loc,t,exp) ->
      let lt = if t then "+" else "-" in
      let str = exp2str exp in
      dprintf "%s %s(l.%s)" lt str (loc2strsmall loc)
	| SJoin el -> 
          dprintf "{  (@[%a)@]\n}"
					(d_list ") ?\n(" ( d_list "\n" d_lockOp'))  el
	| SCall (loc,str,e) -> 
      dprintf "  @[[[  @[%a@]]]\n@]call %s (l.%d)" 
      (d_list "\n" d_lockOp') e  str loc.line
  | SBpLoop i -> dprintf "[loop:%d]" i


let d_effect () (e : simple_effect) = 
  if e = [] then
	  Pretty.dprintf "\n<empty effect>\n\n"
  else
    Pretty.dprintf "\n%a\n\n" (d_list "\n" d_lockOp' ) e

let seffect2str = any2str d_effect

let print_seffect e =
  ignore(Pretty.printf "  @[%a@]" d_effect e)


(* Fill the functionHash (function id -> funStruct)  *)
let createSFunctionHash f =
	let createSFunctionHashAux global =
		match global with
    | GFun (fundec, loc) ->
        let funInfo  = {
          sFundec = fundec;
          sEffect = [];
          summary = [];
          has_effect = true;
          loopSet = IntSet.empty;
          loopEffect = IntMap.empty;	
          fun_lock_count = ExpMap.empty;
          examined = false;
          }
        in
        H.add simpleFInfoHash (fundec.svar).vid funInfo
		| _ -> ()
	in
  dlog "Adding function hashes (info about analysis).\n";
  L.iter createSFunctionHashAux f.globals



let recursive_count = ref 0
let funWeffect_count = ref 0
let total_effect_size : int list ref= ref []

(*
type alias_map = (Cil.location,string list) Hashtbl.t
type cg_alias_map = (Cil.prog_point,string list) Hashtbl.t

type alias_bin_type = (alias_map * cg_alias_map)
let alias_map0  = ref (None:alias_map option)
let cg_alias_map0  = ref (None:cg_alias_map option)

let loadFunAlias ()  =
  let fname = Filename.concat !cgDir "alias.bin" in
  let ic = open_in fname in
  (* Load hashtables with malloced variables and fp results. *)
  let (f, fcg) = (Marshal.from_channel ic : alias_bin_type) in
  alias_map0 := Some f;
  cg_alias_map0 := Some fcg;
  close_in ic

let alias_map loc = 
 begin try H.find (opt2some !alias_map0) loc
 with Not_found -> [] end
*)
