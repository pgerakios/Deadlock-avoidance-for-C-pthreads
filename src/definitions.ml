open Gc_stats
open Callg
(*open Readcalls*)
open Scc
open Scc_cg
open Fstructs
open Cilinfos
open Stdutil
open Strutil
open Lvals
open Scope
open Fstructs
open Modsummaryi

module E = Errormsg
module D = Cildump
module PTA = Myptranal
module A = Alias
module AT = Alias_types
module SPTA2 = Symex
module FC = Filecache
module TA = Trans_alloc
module BS = Backed_summary
module SK = Summary_keys
module H = Hashtbl

open Cil 
open Printf
open Pretty
module L = List
module U = Uref
module P = Pretty


(*************************************************************************** 
 *                     
 *											CIL/Ocaml extension
 *
 ***************************************************************************)

let static_lockset = ref false
let count_locks = ref false

(** directory containing pre-processed call graph info *)
let cgDir = ref ""

(* (void * ) 0 *)
let void_ptr_0 = CastE (voidPtrType, integer 0)
let char_ptr_0 = CastE (charPtrType, integer 0)

let charPtrPtrType = TPtr (charPtrType,[])
let char_ptr_ptr_0 = CastE (charPtrPtrType, integer 0)

let thick_line  = "\n===================================\
                    ===================================\n"
let line        = "-----------------------------------\
                     -----------------------------------\n"

(* printf or logging wrapper *)
let info format =  Printf.ksprintf (fun x ->
  Printf.printf "\027[36m\027[1mInfo:\027[0m %s" x) format

let enable_log = ref false
let log format =  Printf.ksprintf 
                  (fun x ->
                   if !enable_log then 
                    begin
                       Printf.printf "%s" x;
                       flush stdout
                    end) format

let detailed_log = ref false 

let dlog format = Printf.ksprintf 
                  (fun x ->
                   if !detailed_log then 
                    begin
                       Printf.printf "%s" x;
                       flush stdout
                    end) format  

let found_errors = ref false 
let hasErrors () = !found_errors
let err format = 
  found_errors:=true;
  Printf.ksprintf 
    (fun x -> Printf.fprintf stderr "\027[31m\027[1mError:\027[0m %s" x; 
    flush stderr) format
let warn format = 
  Printf.ksprintf
    (fun x -> Printf.fprintf stderr "\027[33m\027[1mWarning:\027[0m %s" x; 
    flush stderr) format

let unimp format = 
  found_errors:=true;
  Printf.ksprintf 
    (fun x -> Printf.fprintf stderr "\027[31m\027[1mUnimplemented:\027[0m %s" x; 
    flush stderr) format

let dbg format = 
  Printf.ksprintf (
    fun x ->Printf.printf "Debug: %s" x; 
    flush stdout) format



let error_set = ref StringSet.empty
let clear_error_set () = 
  error_set := StringSet.empty

let info_set = ref StringSet.empty
let clear_info_set () = 
  info_set := StringSet.empty

exception Not_implemented of string 
let rs_not_implemented format =
	Printf.ksprintf (fun x -> raise (Not_implemented x)) format
exception Impossible of string
let rs_impossible format =
	Printf.ksprintf (fun x -> raise (Impossible x)) format

exception End_analysis  

let getLocLine loc : int =	
	loc.line

let alloc_names = [
  "malloc";
  "calloc";
  "realloc";
  "xmalloc";
  "__builtin_alloca";
  "alloca";
  "kmalloc"
]
	
let is_alloc_fun e = 
	match e with
   | Lval (lh, o) ->
      if isFunctionType (typeOfLval (lh, o)) then
        match lh with
            Var v -> List.mem v.vname alloc_names
          | _ -> false
      else false 
  | _ -> false


let myLockT = 
  let ti = {
    tname = "mypthread_mutex_t";
    ttype = TVoid [];
    treferenced = true;
        }
  in
  TNamed (ti, [])

let myLockPtrT = TPtr (myLockT, [])

(* is the type : `mypthread_mutex` ? *)
let typeOfLock typ = 
	match typ with
	| TComp (ci, _) ->
		ci.cname = "mypthread_mutex"
	| TNamed (t, _) -> 
		t.tname = "mypthread_mutex_t"
	| _ -> false

(* is the type : `mypthread_mutex_t *` ? *)
let typeOfLockPtr typ = 
	match typ with
	| TPtr (a, _) -> typeOfLock a
	| _ -> false

(* decides whether this a type containing a lock *)
let typeContainsLock inType : bool = 
  let decide (t:typ) : existsAction = 
    if typeOfLock t || typeOfLockPtr t then
      ExistsTrue
    else 
      ExistsMaybe
  in
  typeOfLock inType || typeOfLockPtr inType ||
  Cil.existsType decide inType


(* Function that decides whether this type is a void ( * )* *)
let rec isVoidPtrStar (t:typ) : bool = 
  match t with
    | TVoid [] -> true 
    | TPtr (t1, []) -> isVoidPtrStar t1
    | _ -> false

(* Function that resolves the base type of a *) 
let resolve_base_type (e:Cil.exp) : typ = 
  (* This is a function formal so it should be an lval or ptr to lval *)
  let rec procLval lv = 
    match lv with
    | Var vi, _ -> vi.vtype
    | Mem e, _ -> 
        let res = procExp e in
          TPtr(res, [])
  and
  procExp ex = match ex with
    | Lval lv -> procLval lv 
    | AddrOf lv -> procLval lv
    | _ -> rs_impossible "resolve_base_type"
  in
  procExp e


let lvalIsLockHandle lval = 
	typeOfLockPtr (typeOfLval lval)	

let expIsLockHandle exp = 
	match exp with
	| Lval lval -> lvalIsLockHandle lval
	| _ -> false
		
	
module Int = struct
  type t = int
  let compare = Pervasives.compare
end
module IntSet = Set.Make(Int)
module IntMap = Map.Make (Int)

module LocMap = Map.Make (
       struct
         type t = location
         let compare = Cil.compareLoc
       end
      )

module StringMap = Map.Make (String)

let str_map_len sm : int = 
  StringMap.fold (fun _ _ i -> i+1) sm 0

let rec getOffset (exp:exp) : offset = 
  match exp with
  | Lval (Var _,off) -> off
  | Lval (Mem e' ,off) -> addOffset off (getOffset e') 
  | CastE (_, e') -> getOffset e'
  | AddrOf (_,off) -> off
  | _ -> NoOffset

(* Pretty naive offset mapping based on the field (not index) *)
module OffMap = Map.Make (
  struct 
    type t = offset
    let compare = Ciltools.compare_offset
  end
)
        
let getIntMap m key = 
	try IntMap.find key m 
			with Not_found -> 0

let updateIntMap m key = 
	let c = getIntMap m key in
	IntMap.add key (c+1) m

let create_map_copy (m : 'a IntMap.t) : 'a IntMap.t  = 
	IntMap.fold IntMap.add m IntMap.empty

let create_hash_copy (h : ('a, 'b) H.t) : ('a, 'b) H.t  = 
	let new_copy = H.create 20 in
	H.iter (H.add new_copy) h;
	new_copy
	
let overwrite_hash (h1 : ('a, 'b) H.t) (h2 : ('a, 'b) H.t) 
  : unit = 
	H.clear h1;
	H.iter (H.add h1) h2



(*************************************************************************** 
 *                    
 *                    Data definitions
 *
 ***************************************************************************)

type sum_typ =  (Lvals.aLval * Scope.scope) list
type vinfo = Cil.fundec * Cil.varinfo 

type sexp = (* simplified abstract expression*)
  | SBot
  | SAddrOf of sexp 
  | SVar of (vinfo * Cil.offset)
  | SDeref of (sexp * Cil.offset)
  | SAbsHost of (AT.ptaNode * Cil.offset)
  (* instantiation of a variable with a list of
   * possible expressions at a specific location *)
  | SInst of (vinfo * Cil.offset * sexp list * Cil.location ) 


(*************************************************************************** 
 *                    
 *                    Effect definitions
 *
 ***************************************************************************)


(* location of call 
 * function expr 
 * arg expr (single arg) *)
type lockopinfo = Cil.location * Cil.exp * Cil.exp

(* When using a summary, put this as location *)
let summaryLocation  = { line = -2; 
		   file = ""; 
		   byte = -1;}

let summaryLI = (summaryLocation,integer 0,integer 0)

type assign_atomic_t = 
    AAssign of assign_t
  | AJoin of assign_effect list
  (* assign_state is a summary of the assignments made in the 
   * called function *)
  | ACall of callinfo * assign_state

and assign_effect = assign_atomic_t list

(* type of memory of each lock handle
 * - Global
 *      lval: base lvalue
 *      bool: deref YES/NO
 *      bool: HANDLE/POINTER
 *      int: offset before dereference
 *      int: offset after dereference
 * - Heap
 *      int: offset
 *      ctx: call locations from the creation of the lock (bottomup)
 * - Stack
 *      int: index of the locals array *)
type mem_t =
  | Global of lval * bool * bool * int * int
  | Heap of (int * ctx)
  | Stack of int

type resolved = 
	| Resolved of effect
	| Unresolved of int (* function vid. For mutually rec funs *)
and 

atomic_effect = 
	LockOp of  
	(* (location of call (location of instruction), 
	* function that is called,
	* argument to lock op),
	* bool flag acquire/release, 
	* (aExp = aliased formal param or allocation point or global),
  * *)
	(lockopinfo * bool * sexp * mem_t)
	 
 | Join  of effect list 
 
 (* call info and a reference to a resolved type
 *  - the reference allows us to perform in-place
 *    updates when resolving an effect
 * **)
 | NCall of (callinfo * (resolved ref))
 (* recursive call
 * similarly to NCall, the reference is None
 * when the recursive effect has not been 
 * computed, otherwise it is Some (summarized effect)
 * *)
 | RCall of (callinfo * (effect option ref))

 (* Inserting assignments in effect to track visible modifications from 
  * functions that are being called. The first pair is the left hand side
  * and the second the right. 
  * The values should be translated to terms of the calling function. *)
 | Assign of assign_t

 (* This is used as a placeholder for the loop effect. It is to be removed after
  * the complete function's effect has been computed. *)
 | BpLoop of int


and effect = atomic_effect list 



(**************************************************************************
 *                      
 *                          Time functions
 *
 **************************************************************************)
let t_start = ref (Sys.time())
let t_sum = ref !t_start

let string_of_time (r: float) : string =
  let t = int_of_float (r *. 100.0) in
  let point = t mod 100 in
  let t = t / 100 in
  let s = t mod 60 in
  let m = (t mod 3600) / 60 in
  let h = t / 3600 in
  Printf.sprintf "%02d:%02d:%02d.%02d" h m s point
 
let start_time s = 
   log "Start time : %s\n" s; 
   t_start := Sys.time () 


let end_time s = 
  let t = (Sys.time()) -. !t_start in
  log "End time : %s  time = %s\n" s (string_of_time t);
  t_sum := !t_sum +. t

let sum_time () = 
  log "Total time: %s\n" (string_of_time !t_sum);

type time_t = {  mutable t_start : float ;
                 mutable t_sum   : float ;
              }

let rstart_new s = 
   log "Start time : %s\n" s; 
  {t_start = Sys.time () ; t_sum = 0.0 }

let rend_time s r =
 let t' = Sys.time () -. r.t_start in
 let t'' = r.t_sum +. t' in
 log "End time : %s  time=%s total=%s\n" s
 (string_of_time t') (string_of_time t'');
 r.t_start <-  Sys.time ();
 r.t_sum <-  t''

let print_mb s =
 begin
 let word_size = (Cil.bitsSizeOf (TPtr(TVoid [], [])))/8 in
 log "HEAP (MB): %d @@ %s\n"  
 (((Gc.stat ()).Gc.live_words * word_size) / 1048576 ) s
 end


(*************************************************************************** 
 *                     
 *											  Useful Functions
 *											    Printing etc.
 *
 ***************************************************************************)

(* convert exception to option*)
let absFind find_fn data_struct what =
    try Some (find_fn data_struct what)                  
    with Not_found -> None

let absHTprint key2str val2str ht =
  H.iter 
  (fun key val_ -> 
     Printf.printf "%s\n%s\n" 
     (key2str key)
     (val2str val_)
  )  ht
(* far from perfect but does the thing*)
let abs_list2string sep val2str ls =
 match ls with
  | [] -> ""
  | hd::[] -> val2str hd
  | hd::tl ->
    (val2str hd) ^ 
    List.fold_left 
    (fun a b -> a ^ sep ^ (val2str b )) ""  tl

let loc2strsmall loc = 
  let (file,line) = (loc.file, loc.line) in
  let li = 
    try String.rindex file '/' 
    with Not_found -> -1
  in
  let only_name = String.sub file (li+1) ((String.length file) - li -1) in
  only_name^":"^(string_of_int line)


exception Opt2some

let any2str f e  = (sprint 80 (dprintf "%a" f e))
let exp2str     = any2str d_exp 
let stmt2str    = any2str d_stmt 
let inst2str		= any2str d_instr
let typ2str     = any2str d_type
let lval2str = any2str d_lval
let loc2str loc =  any2str Cil.d_loc loc
let pp2str      = any2str d_pp
let stor2str    = any2str d_storage
let attrl2str   = any2str d_attrlist

let d_ctx ctx = 
  d_list "::" (fun _ s -> dprintf "%s" (loc2strsmall s)) ctx 

let ctx2str = any2str d_ctx


let mem2str m = 
  let deref2str b = if b then "deref" else "noderef" in
  let handle2str b = if b then "handle" else "pointer" in
  match m with
  | Stack i -> "S_" ^ (string_of_int i)
  | Heap (o,c) -> "H"^"(off:"^ (string_of_int o) ^ 
                        ",ctx: "^ (ctx2str c) ^ ")"
  | Global (b_lv,d,h,o1,o2) -> "GL:"^(deref2str d)^":"^(handle2str h)^":"^
      (lval2str b_lv)^
      ":off1_"^(string_of_int o1)^
      ":off2_"^(string_of_int o2)


let off2str = any2str (Cil.d_offset (text "<base>"))

let opt2bool = function Some _ -> true | _ -> false 
let opt2some = function Some x -> x | _ -> raise Opt2some

let str2varinfo s = opt2some (varinfo_of_name s)
let fundec2loc f = f.svar.vdecl
let varinfo2loc vi = vi.vdecl
let varinfo2str vi = vi.vname 
let fundec2str f = f.svar.vname
let aexp2str x = any2str Lvals.d_aexp x
let alval2str x = any2str Lvals.d_alval x
let scope2str (s : Scope.scope) = 
   match s with 
    SFormal i  -> Printf.sprintf "SFormal(%d)" i
  | SGlobal -> "SGlobal"
  | SFunc -> "SFunc" 
  | STBD  -> "STBD"

let vid2str vid = (varinfo2str (Cilinfos.getVarinfo vid))

let rec forallStmts (todo) (fd : fundec) =
    fasBlock todo fd.sbody;

and fasBlock (todo) (b : block) =
  L.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    ignore(todo s);
    match s.skind with
      | Block b -> fasBlock todo b
      | If (_, tb, fb, _) -> (fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
      | Loop (b, _, _, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> E.s (E.unimp "try/except/finally")
  end
;;


let rec detail_sexp (e :sexp) : string = 
  let po (o:Cil.offset) = any2str (Cil.d_offset (text "")) o in
  begin
    match e with 
    | SBot -> "SBot" 
    | SAddrOf e' -> "SAddrOf(" ^ (detail_sexp e') ^ ")"
    | SVar ((fd,vi),o) -> 
      "SVar(" ^ (fundec2str fd) ^ ","   ^ 
      (varinfo2str vi) ^","^(po o) ^")"
    | SDeref (e',o) -> 
      "SDeref(" ^ (detail_sexp e') ^ "," ^ 
      (po o) ^   ")"
    | SAbsHost (n,o) -> "SAbsHost(" ^
      (A.Abs.string_of n) ^ "," ^ (po o) ^ ")" 
        (* instantiation of a variable with a list of
         * possible expressions *)
    | SInst ((fd,vi),o,el,loc) ->
      "SInst(" ^ (fundec2str fd) ^ ","   ^ 
      (varinfo2str vi) ^ "," ^  (po o) ^
      "@line:" ^ (string_of_int loc.line)
      ^" ,{"^
      (abs_list2string "," detail_sexp el) ^ "})"
  end 

let rec sexp2str (e :sexp) : string = 
let po (o:Cil.offset) = any2str (Cil.d_offset (text "")) o in
begin match e with 
 | SBot -> "bot" 
 | SAddrOf e' -> "& " ^ (sexp2str e')  
 | SVar ((fd,vi),o) -> 
       "("^(fundec2str fd) ^"::" ^(loc2str vi.vdecl)^ ") " ^ 
        (varinfo2str vi)  ^(po o) 
 | SDeref (e',o) -> 
     "*(" ^ (sexp2str e') ^ ")"^  (po o) 
 | SAbsHost (n,o) -> "#(" ^
    (A.Abs.string_of n) 
    ^ "," ^ (po o) ^ ")" 
 (*instantiation of a variable with a list of
  * possible expressions *)
 | SInst ((fd,vi),o,el,loc) ->
     "$(" ^ (fundec2str fd) ^ "::"   ^ 
     (varinfo2str vi)  ^(po o)^ "@line:" ^ 
     (string_of_int loc.line)   ^ ",{" ^
     (abs_list2string "," sexp2str el) ^ "})"
end 

let sexp2exp (e:sexp) : exp = 
  let rec sexp2exp0 (e:sexp) (oo :offset) : exp = 
    let rs s = raise (Impossible ("sexp2exp/" ^ s))  in
    begin
      match e with    
      | SBot -> rs "SBot"
      | SAbsHost _  -> rs "SAbsHost"
      | SAddrOf e' ->
          begin  match sexp2exp0 e' oo with
          | Lval l ->  mkAddrOf l
          | _ -> rs "AddrOf not Lval"
          end         
      | SVar ((fd,vi),o) -> Lval (Var vi,addOffset o oo)
      | SDeref(e',o) -> Lval (mkMem (sexp2exp0 e' oo) o)
      | SInst(_,o,e'::[],_) -> sexp2exp0 e' (addOffset o oo)
      | SInst(_,o,_,_) -> rs "SInst"
    end
  in
  sexp2exp0 e NoOffset

let sexp2strsmall (sexp:sexp) = 
  exp2str (sexp2exp sexp)

let rec typeOfSexp sexp = 
  match sexp with
  | SBot -> rs_impossible "Sbot"
  | SAbsHost _  -> rs_impossible "SAbsHost"
  | SAddrOf s -> TPtr (typeOfSexp s, [])
  | SVar ((_,vi),o) -> 
      (*let _ = log "Trying to get offset: %s from %s.\n" 
        (off2str o) (typ2str (unrollTypeDeep  vi.vtype)) in*)
      Cil.typeOffset vi.vtype o
  | SDeref (s,o) -> begin
      match unrollTypeDeep (typeOfSexp s) with
      | TPtr (t,_) -> Cil.typeOffset t o
      | _ -> rs_impossible "derefing a non-pointer type"
    end
  | SInst _ -> rs_impossible "SInst"

let compare_sexp s1 s2 = 
  Ciltools.compare_exp (sexp2exp s1) (sexp2exp s2)

module SexpMap = Map.Make (
  struct 
    type t = sexp
    let compare = compare_sexp
  end
)

module SexpSet = Set.Make (
  struct 
    type t = sexp
    let compare = compare_sexp
  end
)

(* Context comparison *)
let compareCtx c1 c2 = 
  try 
    List.for_all2 (
      fun (loc1) (loc2) ->
        Cil.compareLoc loc1 loc2 = 0
    ) c1 c2
  with Invalid_argument _ -> false
     


(* NCall mapping *)
let ncall_summary : ((int SexpMap.t) LocMap.t) ref = ref LocMap.empty

let get_ncall_summary loc : int SexpMap.t = 
  try LocMap.find loc !ncall_summary
  with Not_found -> 
    rs_impossible "get_ncall_summary"

let set_ncall_summary loc c_map : unit = 
  let new_ncs = LocMap.add loc c_map !ncall_summary in
  ncall_summary := new_ncs


let print_count_map m =
  if not (SexpMap.is_empty m) then
    begin
      log "Lock count summary:\n";
      let pr sexp i = log "  %20s:%20d\n" (exp2str (sexp2exp sexp)) i in
      SexpMap.iter pr m;
      log "\n"
    end

let rec strstr haystack needle offset =
  if ((String.length needle) + offset) >
     (String.length haystack) then  -1
  else if (String.sub haystack offset
      (String.length needle)) = needle then offset
  else if (String.contains_from haystack (offset+1) 
      (String.get needle 0)) then
    strstr haystack needle
      (String.index_from haystack (offset+1)
      (String.get needle 0))
  else -1


let cur_ast : Cil.file ref = ref dummyFile
let call_stmt : Cil.stmt ref = ref Cil.dummyStmt
let cur_instr : Cil.instr ref = ref Cil.dummyInstr
let cur_instr_ind : int ref = ref 0
let cur_pp : prog_point ref = ref ppUnknown
let call_loc : Cil.location ref = ref locUnknown
let fun_e   : Cil.exp ref = ref (SizeOfStr "") 
let args_e : Cil.exp list ref  = ref []
let curFunc : Cil.fundec ref =  ref dummyFunDec
let fun_loc : Cil.location ref = ref locUnknown
let currSCC : (scc option) ref = ref None

let getCurrSCC () : scc = 
	match !currSCC with
	| None -> rs_impossible "getCurrSCC"
	| Some sccr -> sccr
	
let sameSCC scc vid : bool=
	FSet.mem vid scc.scc_nodes


type subst_typ0 = (Cil.varinfo * sexp option) list 


let rec singleAlias (e : sexp ) : bool = 
  begin 
    match e with    
    | SBot -> true
    | SAddrOf e' -> singleAlias e' 
    | SVar _ -> true
    | SDeref(e',_) -> singleAlias e' 
    | SAbsHost _  -> true 
    | SInst(_,_,e',_) -> (List.length e') < 2 
  end 

let rec vi_of_sexp (e:sexp): varinfo = 
	begin 
    match e with    
    | SBot ->  rs_impossible "SBot"
    | SAbsHost (pta,o)  -> 
        rs_impossible "vi_of_sexp/AbsHost: %s"
        (abs_list2string ","
        (fun x -> exp2str (Lval  (addOffsetLval o (x))))
        (A.Abs.represents pta))
    | SAddrOf e' -> vi_of_sexp e' 
    | SVar ((fd,vi),_) -> vi
    | SDeref(e',_) -> vi_of_sexp e' 
    | SInst(_,_,e'::[],_) -> vi_of_sexp e'
    | _ -> rs_impossible "vi_of_sexp/SInst"  
  end 

let vid_of_sexp (e:sexp): int = 
  begin 
    try (vi_of_sexp e).vid
    with 
    | e0 ->
        log "Exn from vid_of_sexp : %s\n" (sexp2str e);
        raise e0
  end

let rec simplify_aExp (e: Lvals.aExp) : sexp = 
	let do_l ((h,o): Lvals.aLval) : sexp = 
    begin 
      match h with 
      | CVar (OrigVar id ) -> SVar ((!curFunc, getVarinfo id), o )
      | CVar (CreatedVar vi) -> SVar ((!curFunc, vi), o)
      | CMem e -> SDeref (simplify_aExp e,o)
      | AbsHost a -> SAbsHost (a,o)
    end in
  begin 
    match e with 
    | CConst  _  
    | CAlignOf  _  
    | CSizeOfStr _
    | CSizeOfE _
    | CAlignOfE _
    | CUnOp _  
    | CBinOp _ 
    | CSizeOf   _ -> SBot
    
    | CCastE (_,e') -> simplify_aExp e'
    | CStartOf l -> do_l l 
    | CAddrOf l ->  SAddrOf (do_l l)
    | CLval l -> do_l l 
  end


let ptrType t = 
  TPtr (t,[])

let derefType t = 
  match t with
  | TPtr (t',_) -> t'
  | _ -> rs_impossible "dereferencing a non-pointer"

let do_if_some f a = 
  match a with 
  | Some b -> Some (f b)
  | None -> None

let rec exp2sexp (*?(cast_type:Cil.typ option = None)*)
  (e:Cil.exp) : sexp =

  let rec do_lval (ctyp: typ option) lv =
    match lv with
    | (Var vi, off) ->
        let _ = 
          match ctyp with
          | Some t -> vi.vtype <- t
          | _ -> ()
        in
        (*let _ = log "do_lval: Var %s, %s\n" vi.vname (typ2str vi.vtype) in*)
        SVar((!curFunc, vi), off)
    | (Mem exp, NoOffset) -> 
        (*let _ = log "do_lval: Mem %s, NoOffset\n" (exp2str exp) in*)
        SDeref (do_exp (do_if_some ptrType ctyp)  exp, NoOffset)
    | (Mem exp, off) -> 
        (*let _ = log "do_lval: Mem %s, %s\n" (exp2str exp) (off2str off) in*)
        SDeref (do_exp None exp, off)

  and do_exp (ctyp: typ option) e = 
    match e with
    
    | AddrOf lv -> 
        SAddrOf (do_lval (do_if_some derefType ctyp) lv)
    
    | Lval lv | StartOf lv ->
        (*let _ = log "do_exp: Lval %s\n" (lval2str lv) in*)
        do_lval ctyp lv
    
    | CastE (t,exp) -> 
        (*let _ = log "do_exp: Cast %s,  %s\n" (typ2str t) (exp2str exp) in*)
        do_exp (Some t) exp
    | _ -> SBot

  in
  do_exp None e
    


(* Get sexp from expression. Involves pointer analysis. *)  
let getSexp (arg : Cil.exp) : (sexp option) =
  let pp = {pp_stmt = (!call_stmt).sid;pp_instr = !cur_instr_ind;} in  
	let (must,elist) = 
				SPTA2.getAliasesAtExp pp (Lvals.abs_of_exp arg) in
	(*L.iter (fun ae -> log "%s: %s " 
		(loc2str (get_instrLoc !cur_instr)) (aexp2str ae)) elist; log "\n";*)				
	let is_singleton = match elist with _::[]->true|_->false in
	if not must || not is_singleton then begin
    if elist = [] then begin
      warn "[%s] Pointer analysis could not resolve `%s'.\n"
      (loc2strsmall !call_loc) (exp2str arg); None
    end
    else
      let aliases = 
        L.fold_left (fun f aexp -> f^"\t"^(string_of_exp aexp)^"\n") "" elist in
      err "[%s] `%s` is an aliased expression. This is usually the case \
        for recursive stucts. Possible aliases are:\n%s\
        Analysis will fail.\n\n" (loc2strsmall !call_loc) (exp2str arg) aliases;
      let cs = (List.hd elist) in
      let s = simplify_aExp cs in
      Some s
	end else begin
  (* Everything went fine *)
		let  cs = (List.hd elist) in
    (*FIXME*)
		let s = simplify_aExp cs in
    Some s
	end




(* Filter the effect from operations on locks that do not exist yet. *)
let rec isFuture_sexp (e:sexp) : bool = 
begin match e with 
 | SBot -> false 
 | SAddrOf e' -> isFuture_sexp e' 
 | SVar ((fd,vi),o) -> not vi.vglob
 | SDeref (e',o) ->  isFuture_sexp e'
 | SAbsHost (n,o) -> false 
 | SInst ((fd,vi),_,el,_) -> false
end 

(* Returned effect of resolved function. *)
let must_resolved (msg:string) (f: resolved ref) : effect=
	begin match !f with 
	| Resolved f' -> f'
	| Unresolved vid -> 
		raise (Impossible (msg  ^ " : Function " ^
						(varinfo2str (Cilinfos.getVarinfo vid)) ^
						" has not been resolved"))
	end 
let mkresolved (f:effect) = ref (Resolved f)



(*************************************************************************** 
 *
 *									    Control flow annotation
 *
 ***************************************************************************)

type funInfoType = {
	(* Reference to the declaration of the function. *)
	fun_dec : fundec ref;	
	(* This the entire effect of the function.*)
	mutable funEffect : effect ;	
	(* The function's effect summary *)
	mutable summary : effect ;
  (* Set containing all the loop nodes. *)
  mutable loopSet : IntSet.t;
  (* Mapping from loop nodes to their effect. *)
  mutable loopEffect : effect IntMap.t;
	(* True if the function has lock opreations or function calls
   * that matter to our analysis, else false. *)
	mutable has_effect : bool;
  (* Are there any lock mallocs? *)
  mutable has_malloc : bool;
  (* Summary of the lock counts *)
  mutable fun_lock_count : int SexpMap.t;
  (* Have we examined this function yet? *)
  mutable examined : bool;
}


let mkDummyFstruct () = {
  fun_dec = ref Cil.dummyFunDec;
  funEffect = [];
  has_effect = false;
  summary = [];
  loopSet = IntSet.empty;
  loopEffect = IntMap.empty;
  has_malloc = false;
  fun_lock_count = SexpMap.empty;
  examined = false;
}

type lock_op_t = Lock | Unlock | CondWait | NoLockOp

(* Check if we have a lock or unlock operation. *)
let lock_type x : lock_op_t =
  match x with
    "mypthread_mutex_lock" -> Lock
  (*| "mypthread_mutex_trylock" -> Lock*)
  | "mypthread_mutex_unlock" -> Unlock
  | "mypthread_cond_wait" -> CondWait
  | _       -> NoLockOp 

let isFunLockOp fname = 
  match lock_type fname with
  | Lock | Unlock | CondWait -> true
  | _ -> false


(* ********************************************************************* *)
(*  fun vid ->  functionInfo *)
let fun_to_funInfo : (int, funInfoType) H.t =
   H.create 500

let cur_fstruct : funInfoType ref = ref (mkDummyFstruct ()) 


(* printing the control flow graph *)

let d_cfgnodename () (s : stmt) =
	dprintf "%d" s.sid

let skind2str kind =
  let loc = string_of_int (get_stmtLoc kind).line in
  (match kind with
    | If (e, _, _, loc)  -> "if"
    | Loop _ -> "loop"
    | Break _ -> "break"
    | Continue _ -> "continue"
    | Goto _ -> "goto"
    | Instr _ -> "instr"
    | Switch _ -> "switch"
    | Block _ -> "block"
    | Return _ -> "return"
    | TryExcept _ -> "try-except"
    | TryFinally _ -> "try-finally")^"_"^loc

let d_cfgedge src () dest =
  dprintf "%a -> %a"
  d_cfgnodename src
  d_cfgnodename dest

let d_cfgnode lockHash (s : stmt)  =
    dprintf "%a [label=\"%d. %s\"]\n\t%a"
    d_cfgnodename s
    s.sid (skind2str s.skind)
    (d_list "\n\t" (d_cfgedge s)) s.succs


(** print control flow graph (in dot form) for fundec to channel *)
let printCfgChannel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%a\n" d_cfgnode s  in
    begin
      ignore (fprintf chan "digraph CFG_%s {\n" fd.svar.vname);
      forallStmts pnode fd;
      ignore(fprintf chan  "}\n");
    end

(** Print control flow graph (in dot form) for fundec to file *)
let printCfgFilename (filename : string) (fd : fundec) =
  let chan = open_out filename in
    begin
      printCfgChannel chan fd;
      close_out chan;
    end

let printDotFile fd =
  let fname = fd.svar.vname in
  let idstr = string_of_int fd.svar.vid in
  let dir = "" in
  let filename = String.concat ""  [dir ; "dot/"; fname; idstr; "_graph.dot"] in
  ignore(printCfgFilename filename fd)


(* for output in dot file *)      
let rec d_lockOp () (lo : atomic_effect) : Pretty.doc =
	match lo with
	(*| NoOp -> dprintf ""*)
	| LockOp ((loc, e1, e2), t, sexp, _) ->
		let lt = if t then "+" else "-" in		
		(*let str = sexp2str sexp in*)
		let str = exp2str (sexp2exp sexp) in    
		(*sprint 10 (printExp defaultCilPrinter () exp)*)
		dprintf "%s %s (l.%d)" lt str loc.line

	| Join el -> dprintf "{\\n(%a)\\n}"
					(d_list ")\\n||\\n(" ( d_list "\\n" d_lockOp))  el
	
	| NCall ((loc1,_, loc2, vi,_), res) -> 
			dprintf "call %s (l.%d,len:%d)" vi.vname loc1.line 
        (List.length (must_resolved "d_lockop" res))
	| RCall ((loc1,_, loc2, vi,_), op_eff)	-> 	
			dprintf "rcall (l.%d)" loc1.line
  | Assign ((l,sc1), (e,sc2), ctx) -> 
      dprintf "[assign:%s] %s := %s" (ctx2str ctx) 
      (lval2str l)
      (match e with Some ex -> exp2str ex | _ -> "Top")
  | BpLoop i -> dprintf "[loop:%d]" i 


(* for output in terminal *)      
let rec d_lockOp' () (lo : atomic_effect) : Pretty.doc =
	match lo with
	| LockOp ((loc, e1, e2), t, sexp, m) ->
		let lt = if t then "+" else "-" in		
		(*let str = sexp2str sexp in*)
    let called = match sexp with
                  | SInst _ -> "(ext)"
                  | _ -> ""
    in
		let str = exp2str (sexp2exp sexp) in    
    dprintf "%s %s %s(l.%d) [%s]" lt called str loc.line (mem2str m)

	| Join el -> dprintf "{  (@[%a)@]\n}"
					(d_list ") ?\n(" ( d_list "\n" d_lockOp'))  el
	
	| NCall ((loc1,_,loc2, vi,_), res) -> 
			dprintf "call %s (l.%d,len:%d)" vi.vname loc1.line
        (List.length (must_resolved "d_lockop" res))      
        
	| RCall ((loc1,_, loc2, vi,_), op_eff)	-> 	
			dprintf "rcall (l.%d)" loc1.line
  | Assign ((l,sc1), (e,sc2), ctx) -> 
      dprintf "[assign:%s] %s := %s" (ctx2str ctx) 
      (lval2str l) 
      (match e with Some ex -> exp2str ex | _ -> "Top")
  | BpLoop i -> dprintf "[loop:%d]" i 


let d_effect () (e : effect) = 
  if e = [] then
	  Pretty.dprintf "\n<empty effect>\n\n"
  else
    Pretty.dprintf "\n%a\n\n" 
    (d_list "\n" d_lockOp' ) e
		
let print_effect e = 
  if (!enable_log) then
  	ignore(Pretty.printf "  @[%a@]" d_effect e)


(* print effect with the inlined function call effect *)
let rec d_complete_effect () (e : effect) = 
	Pretty.dprintf "\n%a\n\n" d_c_eff e

and d_c_eff () e = 
	Pretty.dprintf "%a"  
		(d_list "\n" d_complete_lockOp ) e

and d_complete_lockOp () (lo : atomic_effect) : Pretty.doc =
	match lo with
	| LockOp ((loc, e1, e2), t, sexp, m) ->
		let lt = if t then "+" else "-" in		
		let str = sexp2str sexp in
		(*sprint 10 (printExp defaultCilPrinter () exp)*)
    dprintf "%s%s(l.%d)[%s]" lt str loc.line (mem2str m)

	| Join el -> dprintf "{  ( @[%a)@]\n}"
					(d_list ") ?\n(" ( d_list "\n" d_complete_lockOp))  el
	
	| NCall ((loc1,_, loc2, vi,_), f) -> begin
		match !f with 
		| Resolved eff ->
				dprintf "(Ncall) [\n  @[%a@]\n]" d_c_eff eff
		| _ -> dprintf "ncall %s (l.%d)" vi.vname loc1.line
		end
	| RCall ((loc1,_, loc2, vi,_), op_eff)	-> 	
			dprintf "rcall (l.%d)" loc1.line
  | Assign ((l,sc1), (e,sc2), ctx) -> 
      dprintf "[assign:%s] %s := %s" (ctx2str ctx) 
      (lval2str l) 
      (match e with Some ex -> exp2str ex | _ -> "Top")
  | BpLoop i -> dprintf "[loop:%d]" i 

let printWithBars printer =
  log "===================================\n" ;
  printer ();
  log "===================================\n" 



(*************************************************************************** 
 *                     
 *											  Cil file stuff
 *
 ***************************************************************************)

let mkpath  = Filename.concat 
let split_path f = 
   (Filename.dirname f, Filename.basename f)

 (* A set of functions for retrieving the current 
  * Cil.file *)
let cilfiles = ref (StringMap.empty : Cil.file StringMap.t)
let (cilfile: Cil.file option ref) = ref  (None : Cil.file option)
(*
let cilFileExists (file:Cil.file) : bool = 
	List.exists (* add once*)
			(fun f-> f.fileName = file.fileName) !cilfiles
*)
let cilFileNameExists (fileName:string) : bool = 
	StringMap.mem (snd(split_path fileName)) !cilfiles
  
let cilFileExists (file:Cil.file) : bool = 
	StringMap.mem (snd(split_path file.fileName)) !cilfiles

let cilFileGet (fileName:string) : Cil.file = 
	StringMap.find (snd(split_path fileName)) !cilfiles

(*
let setCilFile (file:Cil.file) : unit =
  cilfiles := List_utils.remove_if 
    (fun f -> f.fileName = file.fileName) !cilfiles;
  (* The previous version didn't work sometimes.*)
  (*if not (cilFileExists file) then*)
  cilfiles := file :: (!cilfiles);
	cilfile := Some file
*)
let cilFileAdd (file:Cil.file) : unit =
  cilfiles := StringMap.add (snd(split_path file.fileName)) file !cilfiles;
	cilfile := Some file


(* Must be in the current file *)  
let vid2fundec (id:int) : Cil.fundec = 
	match !cilfile with 
		| Some file -> 
			begin match Cilinfos.getFundec id file with
				| Some fd -> fd 
				| None -> 
					raise (Impossible "vid2fundec/1")
			end 
		| None -> 
					raise (Impossible "vid2fundec/2")

let vid2fundec_opt (id:int) : Cil.fundec option = 
	match !cilfile with 
		| Some file -> 
				Cilinfos.getFundec id file 
		| None -> 
				None



(*************************************************************************** 
 *                     
 *											  Find Roots
 *
 ***************************************************************************)

(* Set with the vids of all the root functions. *)
let rootFuns : IntSet.t ref = ref IntSet.empty

 
(*** Simple wrapper around PTA call ***)
   
let collectFunsOfType ftype_str curList fdec =
  let ft = fdec.svar.vtype in
  let fts = D.string_of_ftype ft in
  if (fts = ftype_str) then fdec.svar.vname :: curList
  else curList

let resolveFP (exp:exp) : string list =
  let ftype = typeOf exp in
  let ftype_str = D.string_of_ftype ftype in    
  let fdecs = PTA.resolve_funptr exp in
  List.fold_left (collectFunsOfType ftype_str) [] fdecs


class findRootVisitor = object
  inherit nopCilVisitor 
  
  method vinst (i:instr) : instr list visitAction = 
    match i with
    | Call (_, callexp, actuals, loc) ->
        begin          
          match callexp with
          | Lval (Var vi, off) ->              
              if vi.vname = "pthread_create" then
              begin
                (* get the function that is root in the 
                 * new threads call graph *)
                let rexp = L.nth actuals 2 in
                let rec getVi rexp = 
                  match rexp with
                  | AddrOf (Var fvi, _) -> [fvi.vid]
                  | Lval(Var(fvi),NoOffset) -> [fvi.vid]
                  | Lval(Mem(ptrexp), NoOffset) ->
                      let names = resolveFP ptrexp in
                      List.map (
                        fun n -> 
                          (opt2some (varinfo_of_name n)).vid) 
                        names
                  | CastE (_, rexp') -> getVi rexp'
                  | _ -> []
                in
                L.iter (
                  fun id -> 
                    rootFuns := IntSet.add id !rootFuns
                ) (getVi rexp);
                DoChildren
              end
            else 
              DoChildren
          | _ -> DoChildren
        end
    | _ -> DoChildren
end

let function_count = ref 0

let findRoots cg =
  let main_opt = varinfo_of_name "main" in
  let count_main_opt = varinfo_of_name "project_main" in
  let main_opt = 
    if opt2bool main_opt then main_opt
    else count_main_opt 
  in
  if opt2bool main_opt then
    begin
      let main_vid = (opt2some main_opt).vid in
      rootFuns := IntSet.add main_vid !rootFuns;
      let vis = new findRootVisitor in
      FMap.iter (
        fun fk node -> 
          try
            let fdopt = getFunc (fst fk) node.defFile in
            let fd = opt2some fdopt in
            dlog "%s: Rootfun checking: %s\n" node.defFile fd.svar.vname;
            ignore(visitCilFunction vis fd)
          with Opt2some -> ()
      ) cg;
    end
  else
    err "This project does not contain a main function. Analysis will fail.\n"


    

    
(*************************************************************************** 
 *                     
 *											  Cast Visitor
 *
 ***************************************************************************)

(* Special treatment is needed in case the arguments of a function are
 * passed as void *. In this case there usually follows a cast to a 
 * specfic type. This class collects casts to types and associates the
 * relevant exrpessions with these types. *)

module Exp = struct
  type t = Cil.exp
  let hash = Ciltools.hash_exp
  let equal x y = (Ciltools.compare_exp x y == 0)
end

module EH = Hashtbl.Make(Exp)

let castHash (*: (Cil.exp, Cil.typ * Cil.location) EH.t*) =
  EH.create 30

class castVisitor = object (self) inherit Cil.nopCilVisitor as super
(* Simplemen ensures that every cast will be in a Set instruction in 
 * case of casting a struct. So we search for the casts that will be 
 * in Set instructions of CastE expressions. *)
val mutable this_stmt : Cil.stmt = Cil.dummyStmt
val mutable this_sid  : int = 0
val mutable this_instr : Cil.instr = Cil.dummyInstr
val mutable this_instr_ind : int = -1
val mutable this_pp : Cil.prog_point = 
            {pp_stmt = 0; pp_instr = 0;}

method private list_to_single l str = 
  match l with 
  | [a] -> a
  | _ -> rs_impossible str

method private doCast (t:Cil.typ) (e:Cil.exp) 
  (loc:Cil.location) (pp:Cil.prog_point): unit =
  if typeContainsLock t then 
    let (must,elist) =
      SPTA2.getAliasesAtExp pp (Lvals.abs_of_exp e) in				
    let is_singleton l = (List.length l = 1) in
    if not must || not (is_singleton elist) then begin
      dlog "[%s] Casting a multialiased lock handle (%s : %s, %s).\n\
        This cast will be ignored.\n" (loc2strsmall loc) (exp2str e)
        (typ2str t) (inst2str this_instr);
    end
    else begin
      let aexp = (List.hd elist) in
      let el = Lvals.exp_of_abs aexp in
      if is_singleton el then
        begin
          let e' = List.hd el in
          try
            let (prev_type,prev_loc) = EH.find castHash e' in
            if Ciltools.compare_type prev_type t = 0 then
              dlog "[%s] Casting (not for the first time) `%s' (pointing \
                  to `%s') to %s\n" (loc2strsmall loc) (exp2str e) 
                  (exp2str e') (typ2str prev_type)
            else
              err "[%s] Trying to cast `%s' (pointing to `%s') to %s, which \
                  was cast in %s to %s.\n" 
                 (loc2strsmall loc) (exp2str e) (exp2str e')
                 (typ2str t) (loc2strsmall prev_loc) (typ2str prev_type)
          with Not_found ->
            EH.add castHash e (t,loc);
            log "[%s] Casting `%s' (pointing to `%s') to %s\n"
              (loc2strsmall loc) (exp2str e) (exp2str e') (typ2str t)
        end
      else ()
    end
  else ()

method vstmt st = 
  this_stmt <- st;
  this_instr_ind <- -1;
  this_sid <- this_stmt.sid;
  DoChildren

method vinst i =
  this_instr_ind <- this_instr_ind + 1;
  this_pp <- 
    {pp_stmt = this_sid;
    pp_instr = this_instr_ind;};
  begin 
    match i with
    | Set (_, CastE (t,e),loc) -> self#doCast t e loc this_pp
    | Call (_,_,el,loc) ->
        List.iter (
          fun e ->
            match e with 
            | CastE (t,e') -> self#doCast t e' loc this_pp
            | _ -> ()
            ) el
    | _ -> ()
  end; 
  SkipChildren

end

let castvis = new castVisitor

let fillCastHash fn = 
  EH.clear castHash;
  ignore(visitCilFunction castvis fn)


 
(* Locals array's elements might be cast to void. We need to insert the
 * necessary casts so that the bases can be dereferenced. All necessary
 * casts have been noted in castHash. *)
let cast_local (e:Cil.exp) : Cil.exp =
  let rec procLval (lv:Cil.lval) : Cil.lval = 
    match lv with
    | Var _, _ -> lv (* probably irrelevant case *)
    | Mem e, off -> Mem (procExp e), off
  and
  procExp (ex:Cil.exp) : Cil.exp = 
    try 
      let (t,_) = EH.find castHash ex in
      CastE (t,ex)
    with Not_found ->
      match ex with
      | Lval lv -> Lval (procLval lv)
      | AddrOf lv -> AddrOf (procLval lv)
      | _ -> rs_impossible "cast_local"
  in
  procExp e
 
