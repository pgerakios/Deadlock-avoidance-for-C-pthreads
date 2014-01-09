open Cil
open Definitions
open Modsummary
open Cilinfos
open Scope 
open Effect_checks
open Effect_construct
open Effect_tools
open Effect
open Strutil

module H = Hashtbl
module F = Filename
(*************************************************************************** 
 *                     
 *											Code Generation
 *
 ***************************************************************************)
(* Field creation *)
let mkfield s f ci = 
   (s,f ci,None,[],Cil.locUnknown )

let mkrecfield s  =  (* recursive field*)
   mkfield s (fun ci-> TPtr(TComp (ci,[]),[])) 

let mksfield s t = (* simple field*)
   mkfield s (fun ci -> t) 

let mkstruct s flds =  (* create a struct*)
  mkCompInfo true s
    (fun ci ->
       List.map (fun x -> x ci) flds
    ) []


(*************************************************************************** 
 *                     
 *						      Intra-procedural Effects
 *
 ***************************************************************************)

(***************************************
 *  get type of struct  node_t 
 ***************************************)
let max_effect = 255
let max_offset = 255
let max_parent = 255

(* get compinfo from type *)
let rec get_ci t : Cil.compinfo = 
 match t  with 
 | TComp(ci,_) ->  ci
 | TNamed(ti,_) -> get_ci ti.ttype
 | TPtr(t',_) ->  get_ci t'
 | _ -> 
   rs_impossible "ci_of_node: %s" (typ2str t)


let fieldinfos = H.create 10

let init_fieldinfos t = 
	let add f s =  H.add fieldinfos s (f s) in
	let node_fld : string -> Cil.fieldinfo = 
		Cil.getCompField (get_ci t) in

	(* A. meta info *)
	let meta_info = (node_fld "meta_info")  in
	let meta_info_fld =  Cil.getCompField (get_ci meta_info.ftype) in

	let kind = (node_fld "kind")  in
	let kind_fld =  Cil.getCompField (get_ci kind.ftype) in


  (* This is for stack and heap *)
  let ind_off = (kind_fld "io_elt") in
	let ind_off_fld =  Cil.getCompField (get_ci ind_off.ftype) in

  (* This is for globals *)
  let gs_elt = (kind_fld "gs_elt") in
	let gs_elt_fld =  Cil.getCompField (get_ci gs_elt.ftype) in

  let add_meta_info = add (fun s ->  meta_info_fld s) in
	let add_kind = add (fun s ->  kind_fld s) in
  let add_ind_elt = add (fun s -> ind_off_fld s) in
  let add_gs_elt = add (fun s -> gs_elt_fld s) in  

	(* Fill in the hashtable *)
	add (fun _ -> meta_info)   "meta_info" ;
	add (fun _ -> kind )       "kind"      ;
  add (fun _ -> ind_off)     "inf_off"   ;

	add_meta_info "tag" ;
	add_meta_info "type" ; 
	add_meta_info "mem" ;
	add_meta_info "has_parent" ;
	add_meta_info "dummy" ;
	add_meta_info "parent" ;
	add_meta_info "parent_offset" ;
	add_meta_info "size" ;

  add_kind "offset";
	add_kind "io_elt"; (* i(ndex)o(ffset)element for stack and heap *)
	add_kind "gs_elt";  
(*	add_kind "handle";
 	add_kind "handle_addr";*)
	add_kind "com";

  add_ind_elt "type";
  add_ind_elt "index";
  add_ind_elt "offset";

  add_gs_elt "offset1";
  add_gs_elt "offset2";
	add_gs_elt "handle";
	add_gs_elt "handle_ptr";

	try
		add (fun s -> node_fld s) "node_name" 
	with _ -> () 


(*get field info *)
let get_fi s : Cil.fieldinfo =
  try 
   H.find fieldinfos s
  with Not_found -> 
   rs_impossible "get_fi: Field %s was not found !" s

let stack_struct_name = "stack" 

let search_vi_opt opt str : varinfo =
  match !opt with
  | None -> 
  (** look for a global w/ the given name *)
   begin match varinfo_of_name str with
    | Some ret ->
        opt := Some ret;
        ret
    | None -> rs_impossible "search_vi_opt"
   end
  | Some r ->  r

(* stack varinfo : extern __thread stack_node_t *stack; *)
let rstack_vi_opt = ref None
let rstack_vi () : varinfo = 
  search_vi_opt rstack_vi_opt stack_struct_name

  (*match !rstack_vi_opt with
 | None -> 
 (** look for a global w/ the given name *)
   begin match varinfo_of_name stack_struct_name with
    | Some ret ->
        log "Called here!!!\n\n";
        rstack_vi_opt := Some ret;
        ret
    | None -> 
        rs_impossible "rstack_vi" 
   end
 | Some r ->  r*)
 
(* type of the stach node *)
let stack_typ () = 
   match (rstack_vi ()).vtype with
    TPtr(t,_) -> t
   | _ -> 
      rs_impossible "stack_typ : %s" 
                    (typ2str ((rstack_vi ()).vtype))


let typ_node_t_opt = ref None 

(*
typedef  struct node {
  meta_info_t meta_info; // 4 bytes
	kind_t kind;           // sizeof(void * )
  const char *node_name;
} node_t;
*)

let typ_node_t () : Cil.typ =
  let failwith t n = 
    let p = typ2str t in
    raise (Impossible ("typ_node_t/" ^ n  ^ ": " ^ p))
  in
  match !typ_node_t_opt with 
  | None -> 
      let vi = rstack_vi () in
      begin 
        match vi.vtype with
        | TPtr(TComp(ci,_),_) -> 
            let current = Cil.getCompField ci "current" in
            let (node_t:typ) = current.ftype in
            H.add fieldinfos "current" current ;
            begin 
              match node_t with
              | TPtr(TNamed(ti,_),[]) -> 
                  typ_node_t_opt := (Some ti.ttype);
                  init_fieldinfos ti.ttype;
                  ti.ttype (* struct node *)
              | _ ->
                  failwith node_t "1"
            end
            (* changed this *)
        | TPtr (TNamed (ti,_), _) -> 
            begin
              match ti.ttype with
              | TComp (ci,_) -> 
                  (*let _ = log "Found this: %s\n" (typ2str ti.ttype) in*)
                  let current = Cil.getCompField ci "current" in
                  let (node_t:typ) = current.ftype in
                  H.add fieldinfos "current" current ;
                  begin 
                    match node_t with
                    | TPtr(TNamed(ti,_),[]) -> 
                        typ_node_t_opt := (Some ti.ttype);
                        init_fieldinfos ti.ttype;
                        ti.ttype (* struct node *)
                    | _ -> failwith ti.ttype "1"
                  end
              | _ -> failwith ti.ttype "2" 
            end     
        | _ -> failwith vi.vtype "3"
      end 
  | Some x -> (x:Cil.typ)


let mkptr_typ t = TPtr(t,[])

let vid2vi = H.create 100

(* make extern effect global varinfo unique for every vid-function *)
let mk_fun_effect vid : varinfo =
	let node_t = typ_node_t () in
	let typ_node_t_star = mkptr_typ node_t in
	(*mkarray_typ node_t (-1)  in*)
	let name = ("__effect_" ^ (string_of_int vid)) in
	let vi =  makeGlobalVar name typ_node_t_star in
	vi.vstorage <-  Extern;
	H.add vid2vi vid vi;
	vi

let fun_effect vid : varinfo = 
	try H.find vid2vi vid 
	with _ -> mk_fun_effect vid

let vid2ma = H.create 100

(* make malloc array global varinfo unique for every vid-function *)
let mk_fun_mall_arr vid : varinfo option =
  if IntSet.mem vid !rootFuns then
    begin
      let name = ("__malloc_array_" ^ (string_of_int vid)) in
      let vi = makeGlobalVar name intPtrType in
      vi.vstorage <-  Extern;
      H.add vid2ma vid vi;
      Some vi
    end
  else
    None

let fun_malloc_array vid : varinfo = 
	try H.find vid2ma vid
	with _ -> opt2some (mk_fun_mall_arr vid)


let mkarray_typ t sz = 
   TArray (t, 
         (if sz < 0 then None 
         else Some (Cil.integer sz)),[])

let ptr_of_typ t =  TPtr(t,[]) 

let mktemp_var fd typ = makeTempVar fd typ  

let mkframe_var fd = 
 mktemp_var fd (stack_typ ())

let mkpthreadarray_var fd sz = 
  mktemp_var fd (mkarray_typ myLockPtrT sz)


let gl_malloc_array ast =
  let vi = (*search_vi_opt gma_vi_opt "global_malloc_array" in*)
    makeGlobalVar "global_malloc_array" intPtrType in
  vi.vstorage <- Extern;
  vi.vattr <- Attr ("thread",[]) :: vi.vattr;
  ast.globals <- (GVarDecl (vi,locUnknown))::ast.globals;
  vi

let gl_malloc_array_ind ast =
  let vi = (*search_vi_opt gma_vi_opt "global_malloc_array" in*)
    makeGlobalVar "global_malloc_array_ind" intType in
  vi.vstorage <- Extern;
  vi.vattr <- Attr ("thread",[]) :: vi.vattr;
  ast.globals <- (GVarDecl (vi,locUnknown))::ast.globals;
  vi

let gl_mal_arr = ref Lvals.dummyVar
let gl_mal_arr_ind = ref Lvals.dummyVar


(* add the new variables to the function definition and
 * return a set of instructions that should be inserted
 * at the begging of the function specified by fd
 * *)
let mk_rtstack fd (vlist: exp (*lval*) list):
                     (Cil.varinfo * Cil.instr list) =
                           
	let arr = mkpthreadarray_var fd (List.length vlist)  in
	let frame = mkframe_var fd in	(* __cil_tmp... *)
	let set i lvi' : Cil.instr = 
    let rhs = CastE (myLockPtrT (* TPtr (TVoid [],[])*), (*Lval*) lvi') in
		let lhs = (Var arr, Index (Cil.integer i,NoOffset)) in
			(Set (lhs,rhs, Cil.locUnknown))
	in
	let cnt = ref (-1) in
	let init_arr =
    List.map (fun vi -> 
               cnt:=!cnt+1;
               (*H.add var_map vi !cnt;*)
               set !cnt vi) vlist in
 (* end initialize array
  *
  * now init stack frame
  * and push it on stack
  * *)
	(*log "STACK NODE TYPE: %s\n" (typ2str (stack_typ ()));*)
	let ci_stack_node = get_ci (stack_typ ()) in
	let ci_stack_fld = Cil.getCompField ci_stack_node in
	let next_field =  ci_stack_fld "next" in
	let locals_field = ci_stack_fld "locals" in
	let current_field =  ci_stack_fld "current" in
	let gmas_field =  ci_stack_fld "fun_malloc_array_start" in
	(* let base_field =  ci_stack_fld "base" in*)
	(* frame->next = rstack *)
	let rstack_offset = NoOffset in
	let next_offset = Field (next_field,NoOffset) in   
	let locals_offset = Field (locals_field,NoOffset) in
	let current_offset = Field (current_field,NoOffset) in
	let gmas_offset = Field (gmas_field,NoOffset) in

	(* let base_offset = Field (base_field,NoOffset) in   *)

	let lhs0 = (Var frame, next_offset) in
	let rhs0 = Lval (Var (rstack_vi ()),rstack_offset) in
	let i0 =  (Set (lhs0,rhs0, Cil.locUnknown)) in

  (* stack.locals = __local_array *)
	let lhs1 = (Var frame,locals_offset) in
	let rhs1 = Lval (Var arr,NoOffset) in
	let i1 =  (Set (lhs1,rhs1, Cil.locUnknown)) in

  (* stack.fun_malloc_array_start = global_malloc_array_start *)
	let lhs2 = (Var frame,gmas_offset) in
	let rhs2 = Lval (Var (!gl_mal_arr_ind ),NoOffset) in
	let i2 =  (Set (lhs2,rhs2, Cil.locUnknown)) in

  (* stack.current = __effect_x *)
	let fun_vid   = fd.svar.vid in 
	let effect_vi = fun_effect fun_vid in
	let lhs3 = (Var frame, current_offset) in
	let rhs3 = Lval (Var effect_vi,NoOffset) in
	let i3 =  (Set (lhs3,rhs3, Cil.locUnknown)) in

	let lhs4 = (Var (rstack_vi ()),rstack_offset) in
	let rhs4 = Cil.mkAddrOf (Var frame,NoOffset) in
	let i4 =  (Set (lhs4,rhs4, Cil.locUnknown)) in

  (* compose frame instructions*)
  let init_frame = [i0;i1;i2;i3;i4] in 
	(* compose all instructions *)
	(frame, init_frame @ init_arr)


(* pop the stack at the end of the function *)
let pop_stack () :  Cil.instr  =
	let frame_ci = get_ci (stack_typ ()) in
	let fieldinfo = Cil.getCompField frame_ci "next" in
	let offset = Field (fieldinfo,NoOffset) in   
	let rs_offset = NoOffset in
	let rstack_exp = Lval (Var (rstack_vi ()),rs_offset) in
	let rhs0 = Lval (Mem rstack_exp, offset) in
	let lhs0 = (Var (rstack_vi ()), NoOffset) in
	let i0 =  (Set (lhs0,rhs0, Cil.locUnknown)) in
	i0


let arrayi vi ioffset : lval =
 let idx = Index (Cil.integer ioffset,NoOffset) in
 let lhs = ((Var vi,idx)) in
 lhs

 (*use : addOffset end current 
  *      addOffsetLval o lval *)

let array_set l o rhs : Cil.instr =
 Set (addOffsetLval o l,rhs,Cil.locUnknown)

(*if debugging is off then this field does not exist*) 
let set_name l name_v : Cil.instr list = 
 try
  let name = get_fi "node_name" in
  (Set (addOffsetLval (Field (name,NoOffset)) l,
      (Const (CStr name_v )),Cil.locUnknown)
  )::[]
 with _ -> [] 

(*tokenize a string*)
let rec split_char sep str =
 try
  let i = String.index str sep in
    String.sub str 0 i ::
    split_char sep (String.sub str (i+1) 
    (String.length str - i - 1))
 with Not_found -> [str]

(* convert a string of the form "field1.field2.field3"
 * to a Cil offset *)
let s_o str = 
 let strs = split_char '.' str in
 List.fold_left (fun o s -> 
    addOffset (Field (get_fi s,NoOffset)) o
 ) NoOffset strs

let mkarray_typ t sz = 
   TArray (t, 
         (if sz < 0 then None 
         else Some (Cil.integer sz)),[])

let glob_init_instr = (H.create 100:
                       (int,instr list) H.t)

let get_glob_instr vid = 
 match  absFind  H.find glob_init_instr vid with
 | Some x -> x 
 | None -> [] 

let add_glob_init vid elt =
  H.replace glob_init_instr
           vid ((get_glob_instr vid) @ elt)

let finalizeGlobInit () =
	let fd = getGlobInit (opt2some !cilfile) in
	let i = H.fold 
	(fun _ instr ilist -> ilist @ instr )
	glob_init_instr []  in
	fd.sbody.bstmts <- [Cil.mkStmt (Instr i)]

(* the following defs must be kept in sync with
 * the header file *)
(* the 2nd int is the offset *)
type mem = 
   | STACK of int
   (* HEAP : escaping abs.loc., index, offset *)
   | HEAP of (bool * int * int)
   | GLOBAL_DRF_HDL     of (lval * int * int)
   | GLOBAL_NODRF_HDL   of (lval * int * int)
   | GLOBAL_DRF_PTR     of (lval * int * int)
   | GLOBAL_NODRF_PTR   of (lval * int * int)
(*
   | GLOBAL_D_L of sexp
   | GLOBAL_D_LH of sexp
   | GLOBAL_I_S_L of (lval * int)
   | GLOBAL_I_SH_L of (lval * int)
   | GLOBAL_I_S_LH of (lval * int)
   | GLOBAL_I_SH_LH of (lval * int)
*)

let mem2i m = 
  match m with
  | STACK _             -> -3
  | HEAP _              -> -2
  | GLOBAL_DRF_HDL _    -> -1
  | GLOBAL_NODRF_HDL _  ->  0 
  | GLOBAL_DRF_PTR _    ->  1
  | GLOBAL_NODRF_PTR _  ->  2
(*  | GLOBAL_D_L _ -> -2
  | GLOBAL_D_LH _ -> -3
  | GLOBAL_I_S_L _ -> -4
  | GLOBAL_I_SH_L _ -> -5
  | GLOBAL_I_S_LH _ -> 3
  | GLOBAL_I_SH_LH _ -> 4
*)

type str_exp_t = string * Cil.exp
type msl_t = str_exp_t list
type mem_str_t = NonSimple of str_exp_t (* for SEQ, CALL, PATH *)
                | ST of str_exp_t (* for STACK *)
                | IO of msl_t | GS of msl_t | Simple of str_exp_t

let mem2strexp mem = 
  let escapes b = if b then integer 1 else integer 0 in
  match mem with
  | STACK i ->  ST ("offset", (integer i))
  | HEAP (b, i, o) ->
      IO [("type", (escapes b)) ;("index", (integer i)); 
        ("offset", (integer o))]
  | GLOBAL_DRF_HDL    (base,o1,o2) 
  | GLOBAL_DRF_PTR  (base,o1,o2) -> 
      GS [("offset1",(integer o1)); ("offset2",(integer o2));
          ("handle", char_ptr_0);
          ("handle_ptr", mkCast (AddrOf base) charPtrPtrType)]
  | GLOBAL_NODRF_HDL    (base,o1,o2) 
  | GLOBAL_NODRF_PTR  (base,o1,o2) -> 
      GS [("offset1",(integer o1)); ("offset2",(integer o2));
          ("handle", mkCast (AddrOf base) charPtrType);
          ("handle_ptr", char_ptr_ptr_0)]      
(* 
  | GLOBAL_D_L s -> Simple ("handle", sexp2exp s)
  | GLOBAL_D_LH s -> Simple ("handle_addr", sexp2exp (SAddrOf s))
  | GLOBAL_I_SH_L (base,o)
  | GLOBAL_I_SH_LH (base,o) ->
      GS [("offset", (integer o)); ("handle", char_ptr_0);
      ("handle_addr", CastE (TPtr(charPtrType,[]), AddrOf base))]
  | GLOBAL_I_S_L (base,o)  
  | GLOBAL_I_S_LH (base,o) ->
      GS [("offset", (integer o)); ("handle",  mkCast (AddrOf base) charPtrType);
      ("handle_addr", void_ptr_0)]
*)

type lock = LOCK | UNLOCK

let lock2i l =
 match l with
 | LOCK -> 1
 | UNLOCK -> (-1)

let bool2lock b =
  if b then LOCK else UNLOCK

type tag =
   | SIMPLE of string * mem * lock
   | SEQ  of varinfo * int
   | PATH of varinfo * int
   | CALL of (varinfo * int) option * string 

(* changed this *)
let tag2strexpl tag : mem_str_t =
	let addo vi o =
		let lval_e = Lval (Var vi,NoOffset) in
    ("com",Cil.increm lval_e o)
	in match tag with
		| SIMPLE (_,m,_)-> mem2strexp m 
    | SEQ (vi,i) -> NonSimple (addo vi i)
    | PATH (vi,i) -> NonSimple (addo vi i)
		| CALL (o,s) -> begin 
        match o with
        | Some (vi,i) ->  NonSimple (addo vi i)
        | None -> 
        let null = CastE (TPtr (typ_node_t (),[]), zero) in
        NonSimple ("com",null)
			end 

let tag2i k =
   match k with
   | SEQ _ -> -2
   | SIMPLE _ -> 0
   | PATH _ -> 1
   | CALL _ -> -1

let tag2str k =
   match k with
   | SEQ _ -> "SEQ"
   | SIMPLE (s,_,_) -> "SIMPLE (" ^ s ^ ")"
   | PATH _ -> "PATH"
   | CALL (_,s) ->  "CALL (" ^ s ^ ")"


let check_offsets lst = 
  List.iter (fun o -> if o > 2048 then
             begin
                err "Offset > 2048\n";
                rs_impossible "OFFSET IS BIG: %d\n" o
             end
 ) lst

let glob_init_static= (H.create 100:
                       (int,(offset*init) list) H.t)

let get_glob_init_static vid = 
  match absFind H.find glob_init_static vid with
  | Some x -> x 
  | None -> [] 

let add_glob_init_static vid elt =
 (* log "add_glob_init_static vid = %d\n" vid;*)
  H.replace glob_init_static
           vid ((get_glob_init_static vid) @ elt)

type node_init = int -> (*offset *)
                  (* abs parent, poffset array size *)
                 (tag *int *int *int) -> 
                 (offset*init) list



(*************************************************************************** 
 *                     
 *							Code for static initialization of nodes
 *
 ***************************************************************************)

let node_init 
	offset  (tag,parent,poffset,size)  = 
	(*let ini fi i = (Field (fi,NoOffset), i) in*)
	(*SingleInit: single initializer *)
	let sim_inis s exp =(Field ((get_fi s),NoOffset),
											SingleInit exp) in
	(* Struct initializer *)
	let comp_ini s (b : (Cil.offset * Cil.init) list )  =
		let fi = get_fi s in
		(Field (fi,NoOffset),CompoundInit (fi.ftype,b)) 
	in

  let strexpl = tag2strexpl tag in
	let kind_ini = 
    match strexpl with
    | ST (kstr,kexp) ->  comp_ini "kind" [sim_inis kstr kexp]
    | IO l -> comp_ini "kind" [ comp_ini "io_elt"
                (List.map (fun (kstr_in,kexp) -> sim_inis kstr_in kexp) l)]
    | GS l -> comp_ini "kind" [ comp_ini "gs_elt"
                (List.map (fun (kstr_in,kexp) -> sim_inis kstr_in kexp) l)]
    | Simple (kstr,kexp) -> comp_ini "kind" [sim_inis kstr kexp]
    | NonSimple (kstr,kexp) -> comp_ini "kind" [sim_inis kstr kexp]
  in
  let i ii = Cil.integer ii in
	let (has_parent,parent',poffset') =
		if parent < 0 then (0,0,0) 
		else (1,offset-parent,poffset) 
	in
	let (ilktyp,imem) = 
	match tag with 
	|  SIMPLE (_,mem,lktyp) ->
		(i (lock2i lktyp),i (mem2i mem))
	| _ ->
		(zero,zero)
	in

	let meta_info_ini = comp_ini "meta_info" 
											[sim_inis "tag" (i (tag2i tag)) ;
												sim_inis "type" ilktyp;
												sim_inis "mem"  imem; 
												sim_inis "has_parent" (i has_parent) ;
												sim_inis "dummy"  zero ;
												sim_inis "parent" (i parent');
												sim_inis "parent_offset" (i poffset');
												sim_inis "size" (i size)
											]  
	in 
	let node_t = typ_node_t () in
	let name = ((tag2str tag) ^ " @ " ^  (string_of_int offset)) in
	let node_ini = CompoundInit (node_t,
								[meta_info_ini; kind_ini;
									sim_inis "node_name" (Const (CStr name))])	in 
	let idx = Index (Cil.integer offset,NoOffset) in
	[(idx,node_ini)]

let effect_init inis = 
  let node_t = typ_node_t () in
  let node_array_t = mkarray_typ node_t  (-1) in
  CompoundInit (node_array_t, inis)


(* Common instructions for all kinds of 
 * effect nodes *)
(* Example:
   n0[0].name = "k @ 0";
   n0[0].meta_info.tag = k;
   n0[0].meta_info.has_parent = 0;
   n0[0].meta_info.parent = 0;
   n0[0].meta_info.parent_offset = x; //optional
   n0[0].meta_info.size = 4;
*)
let make_effect (k:tag) (vid:int) (offset:int) 
  (parent:int) (* parent node offset *)
  (poffset:int) (*this node's offset in parent array*)
  (nodes:int) : (varinfo * (string-> Cil.exp->unit)) =
  if offset < parent+1 then 
    rs_impossible "make_effect: offset=%d parent=%d" offset parent;
    (* check offsets *)
  check_offsets [offset;parent;poffset;nodes];
  (* get fields and definitions*)            
  let vi = fun_effect vid in 
  (* n0[0] *)
  let ai = arrayi vi offset in 
  let sai s e = add_glob_init vid 
								[(array_set ai (s_o s) e)] in
	(* .name = "tag @ " + offset *)
  let tail = set_name ai ((tag2str k) ^ " @ " ^
													(string_of_int offset)) in
  let i k = integer k in
  let (has_parent,parent',poffset') =
    if parent < 0 then (0,0,0) else (1,offset-parent,poffset) in
  add_glob_init vid tail;

  sai "meta_info.tag" (i (tag2i k));
  sai "meta_info.has_parent" (i has_parent);
  sai "meta_info.parent" (i parent');
  sai "meta_info.parent_offset" (i poffset');
  sai "meta_info.size" (i nodes);
  (vi,sai)


(* Example:
  n0[0].name = "SEQ @0";
  n0[0].meta_info.tag = SEQ;
  n0[0].meta_info.has_parent = 0;
  n0[0].meta_info.parent_offset = x; //optional
  n0[0].meta_info.size = 4;
  n0[0].kind.com = n0+0+1; *)
let make_seq 
         (vid:int)     (* vid of fun using this effect*)
         (offset:int)  (* array index*)   
         (parent :int) (* idx of parent *)
         (poffset:int) (* offset in parent array*)
         (nodes:int)   (* number of children *)
         (coffset:int) (* child offset*)
         : unit =
	(* get fields and definitions*)            
	let (vi,sai) = make_effect (SEQ (dummyFunDec.svar,coffset))
								vid offset parent poffset nodes in
	let lval_e = Lval (Var vi,NoOffset) in
	sai "kind.com"  (Cil.increm lval_e (coffset))

(* Example: 
  n0[3].name = "PATH @ 3";
  n0[3].meta_info.tag = PATH;
  n0[3].meta_info.has_parent = 1;
  n0[3].meta_info.parent = 3; //offset from parent
  n0[3].meta_info.parent_offset = 2;
  n0[3].meta_info.size = 2; // paths

  n0[3].kind.com = n0+3+2; *)
let make_path 
         (vid:int)     (* vid of fun using this effect*)
         (offset:int)  (* array index*)   
         (parent :int) (* idx of parent *)
         (poffset:int) (* offset in parent array*)
         (nodes:int)   (* number of children *)
         (coffset:int) (* child offset*)
         : unit =
 (* get fields and definitions*)            
	let (vi,sai) = make_effect (PATH (dummyFunDec.svar,coffset))
								vid offset parent poffset nodes in
	let lval_e = Lval (Var vi,NoOffset) in
	sai "kind.com"  (Cil.increm lval_e (coffset))

(* Example: 
  n0[3].name = "CALL(function_name) @ 3";
  n0[3].meta_info.tag = CALL;
  n0[3].meta_info.has_parent = 1;
  n0[3].meta_info.parent = 3; //offset from parent
  n0[3].meta_info.parent_offset = 2;
  n0[3].meta_info.size = 1; 

  n0[3].kind.com = n1;
*)
let make_call
         (vid:int)     (* vid of fun using this effect*)
         (offset:int)  (* array index*)   
         (parent :int) (* idx of parent *)
         (poffset:int) (* offset in parent array*)
         (fun_vi:varinfo )
         (is_empty_effect : bool)
         : unit =
	let (_,sai) = make_effect (CALL (None,fun_vi.vname)) 
								vid offset parent poffset 0 in
	sai "kind.com"
	(if not is_empty_effect then        
	begin
		let call_vi = fun_vi.vid in 
		let effect_vi = fun_effect call_vi in 
		let lval_e = Lval (Var effect_vi,NoOffset) in
		lval_e  
	end 
	else 
			CastE (TPtr (typ_node_t (),[]), zero)
	)

(* Example:
 n0[1].name = "SIMPLE @1: &p0";
 n0[1].meta_info.tag = SIMPLE;
 n0[1].meta_info.has_parent = 1;
 n0[1].meta_info.parent = 1; //offset from parent
 n0[1].meta_info.parent_offset = 0;
 n0[1].meta_info.size = 3; //parent size

 n0[1].meta_info.type = LOCK; 
 n0[1].meta_info.mem = STACK; 
 n0[1].kind. ...
 *)
 let make_simple 
         (msg:string)
         (vid:int)     (* vid of fun using this effect*)
         (offset:int)  (* array index*)
         (parent :int) (* idx of parent *)
         (poffset:int) (* parent offset *)
         (nodes:int)   (* number of parent nodes*)
         (lockop:bool) (* lockop true=lock,false=unlock*)
         (mem:mem)
         : unit =
  (* get fields and definitions*)   
  let lockop_str = if lockop then "+" else "-" in
  let l = bool2lock lockop in
  let (_,sai) = make_effect (SIMPLE (msg ^ lockop_str,mem,l))
                vid offset parent poffset nodes in
  sai "meta_info.type" (integer (lock2i l));
  sai "meta_info.mem"  (integer (mem2i mem));
  let escapes b = if b then integer 1 else integer 0 in
  match mem with
  | STACK i ->
      sai "kind.offset" (integer i);
  | HEAP (b,i,o) -> begin
      sai "kind.io_elt.type" (escapes b);
      sai "kind.io_elt.index" (integer i);
      sai "kind.io_elt.offset" (integer o);     
    end 
  | GLOBAL_DRF_HDL (base,o1,o2)
  | GLOBAL_DRF_PTR (base,o1,o2) -> begin
      sai "kind.gs_elt.offset1" (integer o1);
      sai "kind.gs_elt.offset2" (integer o2);
      sai "kind.gs_elt.handle" char_ptr_0;
      sai "kind.gs_elt.handle_ptr" (AddrOf base);
    end
  | GLOBAL_NODRF_HDL (base,o1,o2)
  | GLOBAL_NODRF_PTR (base,o1,o2) -> begin
      sai "kind.gs_elt.offset1" (integer o1);
      sai "kind.gs_elt.offset2" (integer o2);
      sai "kind.gs_elt.handle" (AddrOf base);
      sai "kind.gs_elt.handle_ptr" char_ptr_0;
    end
(*  
  | GLOBAL_D_L s ->
      sai "kind.handle" (sexp2exp s) 
  | GLOBAL_D_LH s ->
      sai "kind.handle_addr" (sexp2exp (SAddrOf s)) 

  | GLOBAL_I_S_L (base,o) 
  | GLOBAL_I_S_LH (base,o) -> begin     
      sai "kind.gs_elt.offset" (integer o);
      sai "kind.gs_elt.handle" (mkCast(AddrOf base) charPtrType);
      sai "kind.gs_elt.handle_addr" char_ptr_0;
    end
  | GLOBAL_I_SH_LH (base,o)
  | GLOBAL_I_SH_L (base,o) -> begin
      sai "kind.gs_elt.offset" (integer o);
      sai "kind.gs_elt.handle" char_ptr_0;
      sai "kind.gs_elt.handle_addr" 
        (CastE (voidPtrType, AddrOf base));    
    end
*)



(***************************************************)

let mkEffectInstr (vi:varinfo)
                  (f:effect) : Cil.instr list = [] 

let no_effect_gen = ref IntSet.empty

let lockop_map = ref [] 

let lockop_offset loc = 
(* try*)
   snd (List.find (fun (loc',_) -> loc' = loc) !lockop_map)
(* with Not_found ->
   rs_impossible "Could not find location %s\n" (loc2str loc) *)
    
let next_pos = ref 0 



(*************************************************************************** 
 *                     
 *				Code to create locals array and calculate size and offset   
 *
 ***************************************************************************)

let off_map_size off_map = 
  OffMap.fold (fun o i f -> f+1) off_map 0

let locals_size () = 
  IntMap.fold (
    fun i (off_map,_) feed ->
      (off_map_size off_map) + feed
  ) !arg_map 0

let locals_index arg_ind off_ind = 
  let rec loop ind count = 
    if ind > -1 then begin
      let off_map = 
        try let (om,_) = IntMap.find ind !arg_map in om
        with Not_found -> OffMap.empty
      in
      loop (ind-1) (count + (off_map_size off_map))
    end
    else
      count
  in
  let other_args = loop (arg_ind-1) 0 in
  other_args + off_ind

(* Function that creates list of expressions to be used as elements of 
 * the locals array. *)
let ret_map_0 : (Cil.exp IntMap.t) ref = ref IntMap.empty

let crLocalsList _ : Cil.exp list = 
  let ret_map_0 = IntMap.empty in
  let map_0 = !arg_map in
  let ret_map = 
    IntMap.fold (
      fun i (_,off_exp_map) f->
        IntMap.fold (
          fun j (off,exp) f' -> 
            IntMap.add j exp f'
        ) off_exp_map f
    ) map_0 ret_map_0 in
  (* This suffices to iterate with an ascending order on the keys. *)
  IntMap.fold (
    fun i a feed -> feed @ [a] 
  ) ret_map []

(* Create memory info for runtime *)
let runtime_mem sexp lm loc =
  let vi = vi_of_sexp sexp in
  match lm with
  | Heap (o,_) ->
      begin try
        (* all mallocs from all contexts should be here *)
        let ind = H.find aa_mal_hash vi.vname in
        HEAP (true,ind,o)
        with Not_found ->
          err "[%s] Cannot resolve the location being locked.\n"
            (loc2strsmall loc);
          HEAP (false,H.hash vi.vname,o)
      end
  | Global (base_lv,deref,handle,o1,o2) -> 
      begin
        (* There is a chance that this global lock is not
         * declared in this file. In this case we have to 
         * declare it as extern variable to use it. *)
        (match base_lv with
        | (Var vi,_) -> 
            if F.basename vi.vdecl.file <> 
              F.basename (!cur_ast).fileName then
            begin                             
              info_set := StringSet.add
              ("`"^ (lval2str base_lv)^"' was declared in `"^
              (loc2strsmall vi.vdecl)^".\nIt will be redeclared in `"^
              ((!cur_ast).fileName)^
              "' as external in order to be used in the effect.\n")
              !info_set;
              (* If the original value is declared as static, 
               * make it non-static. *)
              if vi.vstorage == Static then begin
                try
                  let remoteFile = 
                    StringMap.find
                      (snd(split_path vi.vdecl.file)) 
                      !cilfiles
                  in
                  L.iter ( 
                    fun gl -> 
                      match gl with
                      | GVar (v,_,_) -> 
                          if v.vname = vi.vname then
                            v.vstorage <- NoStorage
                      | _ -> ()
                  ) remoteFile.globals 
                with Not_found -> ();
              end;
              let declExists = L.exists (
                function
                  | GVarDecl (v,_) -> v.vname = vi.vname 
                  | _ -> false
                ) (!cur_ast).globals
              in
              if not declExists then begin
                let vi' = copyVarinfo vi vi.vname in
                vi'.vstorage <- Extern;
                (* In case this has type TNamed, we want full unroll. *)
                vi'.vtype <- unrollTypeDeep vi'.vtype;
                (!cur_ast).globals <- 
                  (!cur_ast).globals @ [GVarDecl (vi',locUnknown)]
              end
            end
        | _ -> ());

        match deref, handle with
        | true  , true  -> GLOBAL_DRF_HDL   (base_lv,o1,o2)
        | true  , false -> GLOBAL_DRF_PTR   (base_lv,o1,o2)
        | false , true  -> GLOBAL_NODRF_HDL (base_lv,o1,o2)
        | false , false -> GLOBAL_NODRF_PTR (base_lv,o1,o2)
      end  
  | Stack i -> STACK i



(*************************************************************************** 
 *                     
 *											Insert effect code
 *
 ***************************************************************************)

(* For every function that has an effect, ... *)
let doIntraEffect fd : unit =
  let f = 
    try 
      let ht = H.find fun_to_funInfo fd.svar.vid in
      ht.funEffect
    with Not_found -> [] 
  in
	let fd_vid = fd.svar.vid in

	(*begin effect opt *)
  let f1 = scall f in (*INVARIANT:  scall AFTER shrink ONLY*)

  (* Now that effect substitution from calls has taken place 
   * we can check for counts in joins. - currently done earlier *)
  (*if IntSet.mem fd_vid !rootFuns then begin
    log "Checking join counts.\n";
    check_join_eff f1
  end;*)

  (* DON'T do common prefix optimization after scall:
    * comparison between lock operations depends on location,
    * inlined code might depend on the arguments passed to function, which 
    * ARE NOT taken into account. *)

  (* CAUTION: do not run sgarbage after this, cause it will remove all  NCall *)  
	if nonEmptyEffect f1 then    
	begin

    let fsize = effect_size f1 in

    log "\nEffect of function %s (vid=%d VID=%d,SIZE=%d):\n"
      (vid2str fd_vid) fd_vid fd.svar.vid fsize;

    if !enable_log && (f1 <> []) then 
      ignore(print_effect f1);
				
		if fsize > 1024 then
		begin
				err "Effect too large: %d nodes\n" fsize;
				exit (-1)
		end;

    (* INITIALZE type info DO NOT REMOVE *)
    ignore(typ_node_t ()); 
    lockop_map := [] ; (* reset lockop map *)
    next_pos := 0 ; (*reset next_pos*)

    let add_lockop loc offset =
      lockop_map := (loc,offset)::(!lockop_map)  in
    let worklist = Queue.create () in
    let enq e = Queue.add e worklist in 
    let deq () = Queue.take worklist in
    let notEmpty () = not (Queue.is_empty worklist) in
    let fadd () = 
      let n = !next_pos in next_pos := n+1; n in

    let qoffset () = 
      let n = Queue.fold (fun o _ -> o+1) 0 worklist in
      n+1
    in
    let is_globinit f =
      match f with
      | NCall((call_loc,_,_,called_vi,_),_) -> 
          (strstr called_vi.vname 
          "__globinit_cil" 0)    <> -1
      | _ -> false
    in
    
    (* Each tuple on the queue has type
    * effect * parent offset * my_offset_in_parent *
    * #parent_nodes
    * *)                   
    enq (f1,-1,-1,0); (* enqueue effect *)
    while notEmpty () do

      let (f'',parent_offset,my_parent_offset,parent_nodes) = deq () in
      match f'' with 
(*      | [] -> ()*)
      | hd::[] ->
        begin match hd with
        | LockOp((loc,_,_),is_acquire,sexp,lm) ->
            let offset = fadd () in
            let rmem = runtime_mem sexp lm loc in 
            
            (* Extensive description *)
            (* let descr = ("|"^(loc2str loc)^"|"^(sexp2str sexp)) in*)
            (* Shorter descritpion *)
            let descr = ("|"^(string_of_int loc.line)^
            "|"^(exp2str (sexp2exp sexp))^"|") in
            (*log "SIMPLE %d (ln. %d)\n" offset loc.line;*)

            (* we need this for the final pass *)
            add_lockop loc offset; 
            
            make_simple descr fd_vid offset
              parent_offset my_parent_offset
              parent_nodes is_acquire rmem;

              let (lk,lks) = if is_acquire then (LOCK,"+") 
                              else (UNLOCK,"-") in
            (*static initializer *)
              add_glob_init_static fd_vid 
                (node_init offset 
                ((SIMPLE (descr ^ lks,rmem,lk)),
                parent_offset,my_parent_offset,parent_nodes))

        | Join el -> 
            begin 
              match el with
              | [] -> () 
              | _  -> 
                  let eff_vi = fun_effect fd_vid in
                  let len = List.length el in
                  let offset = fadd () in 
                  let q = qoffset () in
                  let qo = offset + q in
                  (*log "PATH : %d qoffset=%d offset+qoffset=%d #paths=%d\n"
                    offset q qo len;*)
                  make_path fd_vid offset parent_offset my_parent_offset len qo;
                  add_glob_init_static fd_vid 
                    (node_init offset (PATH (eff_vi,qo),
                    parent_offset,my_parent_offset,len));
                    
                  ignore(List.fold_left
                    (fun i path -> enq (path,offset,i,len); i+1) 0 el)
            end

        | NCall((call_loc,_,_,called_vi,_),_) -> 
            let r = (strstr called_vi.vname "__globinit_cil" 0) in
            if r  = -1 then
              begin
                let offset = fadd () in 
                make_call fd_vid offset parent_offset
                my_parent_offset called_vi true;
                (*log "CALL : %d line=%d\n" offset call_loc.line;*)
                add_glob_init_static fd_vid 
                  (node_init offset (CALL (None,called_vi.vname),
                  parent_offset,my_parent_offset,0));
                (* we need this for the final pass *)
                add_lockop call_loc offset          
              end

        | RCall _ ->  rs_impossible "doIntraEffect/RCall"
        | Assign _ -> rs_impossible "doIntraEffect/Assign"
        | BpLoop _ -> rs_impossible "doIntraEffect/BpLoop" 
        end
      | _ -> (*at least two elements*)  
          
          let eff_vi = fun_effect fd_vid in
          let len = List.length f'' in
          let offset = fadd () in 
          let q = qoffset () in
          let qo = offset + q in
          (*log "SEQ : %d qoffset=%d offset+qoffset=%d children_size=%d\n"
          offset q qo len;*)
          
          make_seq fd_vid offset parent_offset
            my_parent_offset len qo;
              
          add_glob_init_static fd_vid 
            (node_init offset (SEQ (eff_vi,qo),
            parent_offset,my_parent_offset,len));
            ignore(List.fold_left
              (fun i elt ->
                if is_globinit elt then i
                else begin 
                  enq ([elt],offset,i,len);
                  i+1
                end
              ) 0 f'')

    done (*end while *)
  end
  else begin
    no_effect_gen := IntSet.add fd_vid !no_effect_gen
  end


(**********************************************************
 *
 *        Code for Malloc - free (updated)
 *
 **********************************************************)

let cr_ins_lock fstexp lv : Cil.instr = 
  let func = makeVarinfo true "ins_lock" (TVoid []) in
  let arg0 = fstexp in
  let arg1 = (*AddrOf*)Lval lv in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [arg0; arg1] in
  let loc = locUnknown in 
  Call (None, call_exp, call_args, loc)

let cr_rem_lock name : Cil.instr = 
  let func = makeVarinfo true "rem_lock" (TVoid []) in
  let arg0 = integer (H.hash name) in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [arg0] in
  let loc = locUnknown in 
  Call (None, call_exp, call_args, loc)

(* THe argument exp is the address that will be removed *)
let cr_rem_lock_inv exp : Cil.instr = 
  let func = makeVarinfo true "rem_lock_inv" (TVoid []) in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [exp] in
  let loc = locUnknown in 
  Call (None, call_exp, call_args, loc)

let is_rf (lv: lval option) : Cil.instr =
  let func = makeVarinfo true "is_root_fun" (TVoid []) in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [] in
  let loc = locUnknown in
  Call (lv, call_exp, call_args, loc)  

exception Free_case

let ins_lock_l : string list ref = ref []
let rem_lock_l : Cil.exp list ref = ref []

let crInitHashtblSt fd = 
  let func = makeVarinfo true "init_hashtbl" (TVoid []) in
  let arg0 = Const (CStr fd.svar.vname) in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [arg0] in
  let loc = locUnknown in 
  let new_i = Call (None, call_exp, call_args, loc) in
   mkStmtOneInstr new_i 

let crExitFun _ = 
  let func = makeVarinfo true "exit_fun" (TVoid []) in
  let call_exp = Lval (Var func, NoOffset) in
  let call_args = [] in
  let loc = locUnknown in 
  Call (None, call_exp, call_args, loc)
  

let rec findUniqueName fdec () : string =
  let n = "__a_" ^ (string_of_int (1 + fdec.smaxid)) in
  if (List.exists (fun vi -> vi.vname = n) fdec.slocals)
    || (List.exists (fun vi -> vi.vname = n) fdec.sformals) then begin
      fdec.smaxid <- 1 + fdec.smaxid;
      findUniqueName fdec ()
    end else n


(* Visitor that manages insertions and deletions of malloced locks
 * in and from the hashtable. *)
class heapVisitor = object (self) inherit Cil.nopCilVisitor

val mutable needs_hash = false;

(* This is the malloc effect of the current function that remains to
 * be distributed to function calls and mallocs at any point. *)
val mutable rem_mal_eff = []
val mutable imal_eff = 0
val mutable cur_mal_array = Lvals.dummyVar
val mutable cur_mal_map = StringMap.empty

method private containsMalloc vid : bool =
  try
    let funStruct = H.find fun_to_funInfo vid in
    funStruct.has_malloc
  with Not_found -> true

method vfunc fd =
  ins_lock_l := [];
  rem_lock_l := [];
  (* In order to insert hashtable, this must be both a root of a thread
   * execution and a function that (it or a function called by it) allocates
   * locks. *)
  needs_hash <- (IntSet.mem fd.svar.vid !rootFuns)
                && self#containsMalloc fd.svar.vid;
  if needs_hash then begin
    let fsSt = List.hd fd.sallstmts in
    let initSt = crInitHashtblSt fd in
    initSt.succs <- [fsSt];
    fsSt.preds <- initSt :: fsSt.preds;
    fd.sbody.bstmts <- initSt :: fd.sbody.bstmts;
  end;

  let vid = fd.svar.vid in
  let vname = fd.svar.vname in

  imal_eff <- 0; (*reset the index for the array*)

  (* Mapping containing all the abstract locations that are going 
   * to be malloced by this function. *)
  let maleff = sum#getMalEff (vid,vname) in
  (* Initialize the stack only for the root function. *)
  if IntSet.mem vid !rootFuns && (maleff <> []) then
    begin
      let lv1 = (Var (!gl_mal_arr ),NoOffset) in
      let exp1 = Lval (Var (fun_malloc_array vid),NoOffset) in
      let inst1 = Set (lv1,exp1,locUnknown) in

      let lv2 = (Var (!gl_mal_arr_ind ),NoOffset) in
      let exp2 = integer 0 in
      let inst2 = Set (lv2,exp2,locUnknown) in
      
      let bl1 = mkBlock [mkStmt (Instr [inst1; inst2])] in
      let bl2 = mkBlock [] in
      let resvar = makeTempVar fd ~insert:true intType in
      let tlv = (Var resvar, NoOffset) in
      let set = is_rf (Some tlv) in 
      let s1 = mkStmt (Instr [set]) in
      let ifstk = If (Lval tlv, bl1, bl2, locUnknown) in
      let s2  = mkStmt ifstk in
      fd.sbody.bstmts <- s1::s2::fd.sbody.bstmts
    end;
  DoChildren

method vinst i = 
  match i with
  (* Look out for malloc expressions:
   * replace `l := & _A_...' instructions with ins_hash() and 
   * update in the malloc array indecx *)
  | Set (retval, AddrOf (Var vi, NoOffset), loc) -> begin
      try
        let name = vi.vname in
        let (_,_,is_alloc,_) = H.find (getMalloc1 ()) name in
        if H.mem aa_mal_hash name then begin
        (* ins_hash(arr[gl_m_ind], l) *)
          let lv = (Var (!gl_mal_arr_ind ), NoOffset) in
          let gli_exp = Lval (Var (!gl_mal_arr_ind ), NoOffset) in
          let arr_elt =
            Lval (Var (!gl_mal_arr ), Index (gli_exp,NoOffset)) in
          let ins = cr_ins_lock arr_elt retval in 
          ins_lock_l := name :: (!ins_lock_l);
        (* gl_malloc_array_ind ++ *)
          let inc_exp = increm gli_exp 1 in
          let inc = Set (lv,inc_exp,locUnknown) in
        (* update index to malloc array*)
          imal_eff <- imal_eff + 1;
          ChangeTo [ins;inc]
        end
        else if is_alloc then 
          begin
            log "[%s] Hash: %s -> %d\n" (loc2strsmall loc)
              vi.vname (H.hash vi.vname);
            let hexp = integer (H.hash vi.vname) in
            let ins = cr_ins_lock hexp retval in
            ChangeTo [ins]
          end
        else
          DoChildren
      with Not_found ->
        DoChildren
    end

  | Call(ret, (Lval (Var vi, NoOffset)), actuals, loc) ->
      if vi.vname = "free" then begin
        match actuals with
        | [e] -> begin
            (* We can't be certain that what is freed is not a lock 
             * so we must be conservative and remove free(void * ...) 
             * as well. *)
            let e' = match e with CastE (_,e0) -> e0 | _-> e in
            if isVoidPtrType (typeOf e') 
              || typeOfLockPtr (typeOf e') then
              let rem = cr_rem_lock_inv e in
              ChangeTo [i; rem]
            else
            (* this will happen when freeing sth that is definitely not a
             * lock *)
            DoChildren

          end
        | _ -> DoChildren
      end
      else 
        DoChildren      

  (* Remove dummy instruction - used as placeholder *)        
  | Asm ([],[ str ],[],[],[],_) -> 
      if str = "dummy statement!!" then ChangeTo []
      else DoChildren

  | _ -> DoChildren

end

let heapvis_opt = ref None

let heapvis () = 
  match !heapvis_opt with
  | Some hv -> hv 
  | None -> new heapVisitor

let revTransformMalloc fn = 
  let hvis = ( heapvis () : heapVisitor :> Cil.cilVisitor )  in
  ignore(visitCilFunction hvis fn)

(* Removes auxillary heap variable declarations from global's list *)
let remove_heap_declarations f : unit =
  let hh = getMalloc1 () in
  let rem_filter l = 
    List.filter ( 
      fun g ->
        match g with
        | GVarDecl (vi,loc) -> 
            not ( H.mem hh vi.vname)
        | _ -> true
    ) l 
  in
  let change_filter l =
    List.iter (
      fun g ->
        match g with
        | GVar (vi,_,_) -> 
            if vi.vname = "global_malloc_array" ||
            vi.vname = "global_malloc_array_ind" then
              vi.vstorage <- Extern
        | _ -> ()
    ) l 
  in
  change_filter f.globals;
  f.globals <- rem_filter f.globals


let addExternDecl (f:file) = 
  let makeFunDecl n =
    let t = TFun (TVoid [] ,None,false, []) in
    let vi = makeVarinfo true n t in
    let _ = vi.vstorage <- Extern in
    GVarDecl (vi, locUnknown)
  in
  let newDecls = List.map makeFunDecl 
    ["ins_lock";"rem_lock";"rem_lock_inv";"init_hashtbl";"exit_fun"]
  in
  f.globals <- newDecls @ f.globals;
  let gma = gl_malloc_array f in
  let gmai = gl_malloc_array_ind f in
  gl_mal_arr := gma;
  gl_mal_arr_ind := gmai


(**************************************************************************
 *
 *                    Insert Effect Offsets
 *
 **************************************************************************)

class insertVisitor = object (self) inherit Cil.nopCilVisitor as super

val mutable call_loc      =  Cil.locUnknown
val mutable vid           = -1
val mutable vname         = ""
val mutable current_vi    = Cil.dummyFunDec.svar
val mutable called_vi     = Cil.dummyFunDec.svar

method private doCall e =
  match e with
  | Lval (Var(f),_) -> 
      called_vi <- f;
      begin match f.vname  with
      | "mypthread_mutex_unlock" -> self#doRelease () 
      | "mypthread_mutex_lock" -> self#doAcquire () 
      | "mypthread_cond_wait" -> self#doCondWait () 
      | _ ->  self#doNormal ()
      end
  (* Indirect call *)
  | Lval( Mem(Lval(Var(f),_)),_) ->
      called_vi <- f;
      self#doIndirect ()
  | _ -> self#doIndirect ()


(* inserts the assignment of __cil_tmpn.current *)
method doInsert () =
 try  
   let offset = lockop_offset call_loc in
   let effect_vi = fun_effect vid in
   let lval_e = Lval (Var effect_vi,NoOffset) in
   let rhs =   (Cil.increm lval_e offset) in
(*   let rstack_vi = get_rstack_vi () in*)

   let lhs = ( Var current_vi
               (*Mem (Lval(Var rstack_vi,NoOffset))*),
              Field (get_fi "current",NoOffset)) in
   let set = Set (lhs,rhs,Cil.locUnknown) in
   (* log "INSERT : %s\n" called_vi.vname; *)
   self#queueInstr [set]
 with 
  | Not_found -> 
        (*log "\nNOT found for function :%s\n"
            (called_vi.vname); *)
        ()

method doNormal  ()  =
  let r = (strstr called_vi.vname "__globinit_cil" 0) in
  if r = -1 then self#doInsert ()

method doAcquire  () = self#doInsert ()

method doRelease  () = () 

method doCondWait () = self#doInsert ()

method doIndirect () = self#doInsert ()

val file2prepost = (H.create 10 :
                    (string,(global list * global list))
                    H.t)

method private addGlob () =
  let sz = !next_pos in
  let lst = get_glob_init_static vid in  (*to disable static init lst=[]*)
  let lst_len = (List.length lst) in
  if lst_len <> sz  then
    rs_impossible "addGlob lst_len = %d sz=%d vid=%d" lst_len sz vid
    (* sanity check *)
  else if sz > 0 then 
    begin 
      let node_t = typ_node_t () in
      let ntyp = mkarray_typ  node_t sz in
      let vi = fun_effect vid in
      let glob_vi = makeGlobalVar vi.vname ntyp in
      let g2 = GVar (glob_vi,{init = Some (effect_init lst)},Cil.locUnknown) in
      let g1 = GVarDecl(vi,Cil.locUnknown) in
      vi.vtype <- ntyp;
      vi.vstorage <- Extern;
      
      let name =  (opt2some (!cilfile)).fileName in
      (*log "Adding globs for file : %s\n" name; *)
      begin  
        match absFind H.find file2prepost name with
        | Some (pre,post) ->
            H.replace file2prepost 
            name (pre @ [g1], post @ [g2])
        | None -> 
            H.add file2prepost name ([g1], [g2])
      end
    end

method effectDecls name = 
  begin  
    match absFind H.find file2prepost name with
    | Some a -> a
    | None -> ([],[])
  end 

method vinst i = 
  begin 
    match i with
    | Call(_,e,_,loc) -> call_loc <- loc; self#doCall e
    | _ -> ()
  end;
  SkipChildren

method vstmt s = 
  begin
    match s.skind with 
    | Return _ -> self#queueInstr [pop_stack ()]
    | _ ->  () 
  end;
  DoChildren


method private array_init lst (sz:int) =
  let array_t = mkarray_typ intType sz in
  let inis = List.fold_left (
    fun (i,arr) (vi,cnt,ctx) ->
      let nm = vi.vname in
      let _ = log "Hash: %d. %s -> %d\n" i nm (H.hash nm) in
      (i+1,
      arr@[(Index (integer i,NoOffset),SingleInit (integer (H.hash nm)))])
  ) (0,[]) lst in
  CompoundInit (array_t, snd inis)

(** Inserts initializer for the function's malloc array. 
 *  Only for the root functions. *)
method addMalArr () = 
  let maleff = sum#getMalEff (vid,vname) in
  if IntSet.mem vid !rootFuns && (List.length maleff > 0) then
    begin
      let sz = List.length maleff in
      let ntyp = mkarray_typ intType sz in
      let vi = fun_malloc_array vid in
      let glob_vi = makeGlobalVar vi.vname ntyp in
      let g1 = GVarDecl(vi,Cil.locUnknown) in
      let g2 = GVar ( glob_vi,
                    { init = Some (self#array_init maleff sz)},
                      Cil.locUnknown) in
      vi.vstorage <- Extern;
      vi.vtype <- ntyp;
      let name =  (opt2some (!cilfile)).fileName in
      begin  
        match absFind H.find file2prepost name with
        | Some (pre,post) -> H.replace file2prepost name (pre@[g1],post@[g2])
        | None -> H.add file2prepost name ([g1],[g2])
      end
    end
    

method vfunc fd =
  vid <- fd.svar.vid;
  vname <- fd.svar.vname;
  self#addMalArr ();
  let no_insert_cond = (IntSet.mem vid !no_effect_gen) in
  if no_insert_cond  then
  begin
    (*log "NO CODE GEN for : %s\n"  fd.svar.vname;*)
    SkipChildren
  end
  else begin
    log "CODE GEN for : %s\n"  fd.svar.vname;

    (* this is the list of the formal variables only if their 
     * type is/contains pthread_mutex_t *)
    let vlist = crLocalsList () in
    (* Check the cast hashtble to see if this is 
     * supposed to be hashed *)
    let vlist' = List.map cast_local vlist in
    let (frame_vi,vl) =  mk_rtstack fd vlist' in
    let si  = (Cil.mkStmt (Instr vl)) in
    fd.sbody.bstmts <- si::fd.sbody.bstmts;
    current_vi <- frame_vi;
    EH.clear castHash; (* clear cast hash table *)
    self#addGlob (); (* add globals if necessary*)
    super#vfunc fd (* insert pop statements and offsets*)
  end

end

let ivis = new insertVisitor 

let doInsertOffsets fn = 
  let insertvis = ( ivis : insertVisitor :> Cil.cilVisitor )  in
  ignore(visitCilFunction insertvis fn)


(*************************************************************************** 
 *                     
 *										      Remove Scopes 
 *
 ***************************************************************************)

class scopeVisitor = object (self)
   inherit Cil.nopCilVisitor as super 

method vvdec vi =  
  begin try
    Scope.removeScope vi;
  with BadScope -> () end;
  DoChildren

end

let doRemoveScopes file = 
 (* log "VFUNC : %s : %d\n" (fn.svar.vname) 
      (List.length  (fn.sbody.bstmts) );*)
  let svis = (new scopeVisitor : scopeVisitor :>Cil.cilVisitor)  in
  visitCilFile svis file



(*************************************************************************** 
 *                     
 *										    Finalization
 *
 ***************************************************************************)

let doFinalize dynamic_init f : unit =
	let is_the_typedef g = 
			begin match g with
			| GType (ti,_) ->
				ti.tname = "node_t" 
			| _ ->
				false 
			end 
	in
	let (pre,post) = ivis#effectDecls f.fileName in

	let decide hd tl = 
		let (* gname *) _  = function
		| GVarDecl (vi, _) -> vi.vname
		| GVar (vi, _, _) ->  vi.vname
		| _ -> "" 
	in

	let is_gcc_builtin  = 
    function
      | GVarDecl (vi, _) -> 
          let b1 = (strstr  vi.vname "__sync_" 0) = 0 in
          let b2 = vi.vstorage = Extern in
          let b3 = List.exists
            (function 
              | Attr(an,[]) -> 
                  an = "missingproto"
              | _ -> false
            ) (typeAttrs vi.vtype) in
          (*log "CONSIDERING : %s b1=%b b2=%b b3=%b\n" 
           vi.vname b1 b2 b3;*)
          b1 && b2 && b3   
      |  _ -> false
  in

  if (*(is_malloc_global (gname hd)) || *)
     (is_gcc_builtin hd)
    then tl
    else hd::tl
  in

	let rec insert  lst =
		match lst with
		| [] -> []
		| _::[] -> lst
		| hd :: tl ->
			if is_the_typedef hd then
		(*  let vi  = opt2some (varinfo_of_name "main") in
			let ini1 = node_init 0 
									(SEQ, LOCK, STACK 0,-1,0,0) in
			let ini2 = node_init 1
									(SEQ, LOCK, STACK 2,-1,0,0) in
			let enit = effect_init (ini2 @ ini1) in*)

			(hd
					(* ::(GVar ( (fun_effect vi.vid), 
									{init = Some enit
									},
									Cil.locUnknown
								))*)
					::pre) @ (insert tl)
			else
			decide hd (insert tl)
	in

	log "Finalizing instrumented file %s\n" f.fileName;

	(*let f = opt2some (!cilfile) in*)
	(*insert global effect definitions *) 
	f.globals <- (insert f.globals) @ post;
  
	(* place effects in glob init*)
	if dynamic_init then
		finalizeGlobInit ();

	(*remove scope annotations from file*)
	doRemoveScopes f;
  
  (* save to output file*)
  let dump_path = mkpath !cgDir "gen" in
  let (old_path,fname) = split_path f.fileName in
  let fl =  mkpath dump_path fname  in
  let oc = open_out fl in
  (log "Dumping file in %s.\n" fl;
  lineDirectiveStyle := Some LinePreprocessorOutput;
  (*lineDirectiveStyle := Some LineComment;*)
  dumpFile defaultCilPrinter oc fl f;
  close_out oc)

