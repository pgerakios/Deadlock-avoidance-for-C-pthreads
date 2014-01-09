(**
 * Dumps the parsed and pre-processed file.
 *)


open Cil
open Sys
open Pretty
open Filetools

module Dum = Cildump

exception Impossible of string
let rs_impos format =
 Printf.ksprintf (fun x -> raise (Impossible x)) format
(************************************************************************)
let any2str f e  = (sprint 80 (dprintf "%a" f e))
let exp2str     = any2str d_exp 
let stmt2str    = any2str d_stmt 
let loc2str loc =  any2str Cil.d_loc loc
let opt2bool = function Some _ -> true | _ -> false 
let typ2str   = any2str Cil.d_type  
let offset2str  = any2str (Cil.d_offset  (text ""))
exception Opt2some of string
let opt2some msg  = function Some x -> x | _ -> raise (Opt2some msg)
(************************************************************************)


(* Requires an ENV variable to be defined given *)
let dumpTo = ref ""
let getDumpTo () = 
  (if !dumpTo = "" then
     try
       dumpTo := (Sys.getenv "DUMPROOT");
     with Not_found ->
       prerr_string "Dumpfile: Can't find DUMPROOT environ var\n";
       dumpTo := "/tmp";);
  !dumpTo

(*******************************)
let txt = open_out (Filename.concat !dumpTo "first_pass.txt")
let ptxt format =  Printf.ksprintf
              (fun x ->Printf.fprintf txt "%s\n" x) format

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

let mktemp_var fd typ = makeTempVar fd typ  
  
let mkarray_typ t sz = 
   TArray (t, 
         (if sz < 0 then None 
         else Some (Cil.integer sz)),[])

let ptr_of_typ t =  TPtr(t,[]) 
(*****************************************************)
type typedef_map = (string,(Cil.typ *Cil.compinfo)) Hashtbl.t
let tmap =  (Hashtbl.create 117 : typedef_map) 

(* Type declarations *)
let register_typedefs = 
      ["node_t"; 
       "stack_node_t"; 
       "mypthread_mutex_t"
      ]

let checkTypes ti = 

  let ok = List.exists
           (fun s->s=ti.tname) register_typedefs
  in 
  if ok then 
  begin 
  ptxt "Adding type type : %s\n" (ti.tname);
  match ti.ttype with 
  | TComp (ci,_) ->
      Hashtbl.replace tmap ti.tname (ti.ttype,ci);
      if ti.tname = "stack_node_t" then
      begin
        let rec get_ci t =
           match t  with 
            | TComp(ci,_) ->  ci
            | TNamed(ti,_) -> get_ci ti.ttype
            | TPtr(t',_) -> get_ci t' 
            | _ -> rs_impos "get_ci" 
        in 
        let get_fld ci f =
          try  Cil.getCompField ci  f
          with 
           Not_found -> rs_impos 
             "Could not find field %s in type %s" f 
             (typ2str (TComp (ci,[])))
        in
        let node_t = (get_fld ci "current").ftype in
        let ci_node = get_ci node_t in
        let kind_f = get_fld ci_node "kind" in
        let ci' = get_ci kind_f.ftype in
        let handle_f =  get_fld ci' "gs_elt" in
        let t = handle_f.ftype in
        let ci'' = get_ci t in 
        if ci''.cname <> "global_struct" then
          rs_impos "Expected global_struct but found %s" ci''.cname
          (*Hashtbl.replace tmap "mypthread_mutex" (t,ci'');
          let ti' = { tname= "mypthread_mutex_t";
                      ttype= t;
                      treferenced=true } in
          ptxt "Adding type : mypthread_mutex and mypthread_mutex_t\n";
          Hashtbl.replace tmap "mypthread_mutex_t"
                (TNamed (ti',[]),ci'')*)
      end
  | _ -> 
    raise (Impossible "checkTypes/1") 
  end 

let get_typci s = 
try   
  Hashtbl.find tmap s  
with 
  | Not_found -> rs_impos "get_typci for type %s" s

let get_typ s = 
try
  fst (Hashtbl.find tmap s)
with 
  | Not_found -> rs_impos "get_typ for type %s" s

let get_ci s =
 try 
  snd (Hashtbl.find tmap s)
 with 
  | Not_found -> rs_impos "get_ci for field %s" s

(*****************************************************)
let mk_rstack_vi is_extern is_thread =
  let vi =  makeGlobalVar "stack"
            (ptr_of_typ (get_typ "stack_node_t")) in
  if is_extern then vi.vstorage <-  Extern;
  if is_thread then vi.vattr <- (Attr ("thread",[]))::vi.vattr;
  vi

let rstack_vi_opt = ref None
let rstack_vi () : varinfo =
 match !rstack_vi_opt with
 | None -> 
   let ret = (mk_rstack_vi true true) in
   rstack_vi_opt := Some ret;
   ret
 | Some r ->  r

(**)
let mk_rstack_gdecl () =
   GVarDecl (rstack_vi (), Cil.locUnknown)

let mkframe_var fd = 
 mktemp_var fd (get_typ "stack_node_t")
(******************************************************)

let mkpthreadarray_var fd sz = 
 let t =  ptr_of_typ (get_typ "mypthread_mutex") in
 mktemp_var fd (mkarray_typ t sz)
(******************************************************)

(* add the new variables to the function definition and
 * return a set of instructions that should be inserted
 * at the begging of the function specified by fd
 * *)
let mk_rtstack fd_cnt fd (vlist: lval list):
                     (Cil.varinfo * Cil.instr list) =
                           
 let arr = mkpthreadarray_var fd (List.length vlist)  in
 let frame = mkframe_var fd in
 let set i vi' : Cil.instr = 
  let rhs = Cil.mkAddrOf vi' in
  let lhs = (Var arr, Index (Cil.integer i,NoOffset)) in
  (Set (lhs,rhs, Cil.locUnknown))
 in
 let cnt = ref (-1) in
 let init_arr =
    List.map (fun vi -> 
               cnt:=!cnt+1;
               (*Hashtbl.add var_map vi !cnt;*)
               set !cnt vi) vlist in
 (* end initialize array
  *
  * now init stack frame
  * *)
 let  ci_stack_node = get_ci "stack_node_t" in
 let ci_stack_fld = Cil.getCompField ci_stack_node in
 let next_field =  ci_stack_fld "next" in
 let locals_field =  ci_stack_fld "locals" in
(* let base_field =  ci_stack_fld "base" in*)
 (* frame->next = rstack *)
 let rstack_offset = NoOffset in
     (*Index (Cil.integer fd_cnt,NoOffset) in*)
 let next_offset = Field (next_field,NoOffset) in   
 let locals_offset = Field (locals_field,NoOffset) in   

(* let base_offset = Field (base_field,NoOffset) in   *)

 let lhs0 = (Var frame, next_offset) in
 let rhs0 = Lval (Var (rstack_vi ()),rstack_offset) in
 let i0 =  (Set (lhs0,rhs0, Cil.locUnknown)) in

(* let lhs2 = (Var frame, base_offset) in
 let rhs2 = Lval (Var ef_vi,NoOffset) in
 let i2 =  Set (lhs2,rhs2, Cil.locUnknown) in*)
 (* rstack = &frame *)
 let lhs1 = (Var (rstack_vi ()),rstack_offset) in
 let rhs1 = Cil.mkAddrOf (Var frame,NoOffset) in
 let i1 =  (Set (lhs1,rhs1, Cil.locUnknown)) in

 let lhs2 = (Var frame,locals_offset) in
 let rhs2 = Lval (Var arr,NoOffset) in
 let i2 =  (Set (lhs2,rhs2, Cil.locUnknown)) in

 (* compose frame instructions*)
 let init_frame = [i0;i2;i1] in 
 (* compose all instructions *)
 (frame, init_frame @ init_arr)


(********************************************************)
let pop_stack fd_cnt:  Cil.instr  =
 let frame_ci = get_ci "stack_node_t" in
 let fieldinfo = Cil.getCompField frame_ci "next" in
 let offset = Field (fieldinfo,NoOffset) in   
 let rs_offset = NoOffset in
            (*Index (Cil.integer fd_cnt,NoOffset) in *)
(*(*Mem*) ((*Lval*) (Var rstack_vi (),rs_offset))
 * *)
 let rstack_exp = Lval (Var (rstack_vi ()),rs_offset) in
 let rhs0 = Lval (Mem rstack_exp, offset) in
 let lhs0 = (Var (rstack_vi ()), NoOffset) in
 let i0 =  (Set (lhs0,rhs0, Cil.locUnknown)) in
 i0

(******************************************************)

(******************************************************)

(* ensure that locals+formals are not stored in 
*  a register *)

let is_pthread_mutex_t t = 
 match t with
 | TNamed (ti,_) ->  
   ti.tname =  "pthread_mutex_t" 
 | _ ->
   false

let rec extract_pthread_fields  (o:offset) (t:typ) = 
 match t with
  | TComp(comp,_) ->
        (*isPointerType*)
   List.fold_left 
   (fun l0 fi-> 
     let o'= Cil.addOffset (Field (fi,NoOffset)) o in
     l0 @ (extract_pthread_fields o' fi.ftype) 
   ) [] comp.cfields

  | TNamed (ti, _)  ->
    if ti.tname =  "pthread_mutex_t" then
     o::[]
    else
     extract_pthread_fields o ti.ttype

  | TArray (t', e_opt, _) ->
    let im s = raise (Impossible s) in
    begin match e_opt with
     | Some e ->
       begin match isInteger e with
       | Some n0 -> 
         let n = Int64.to_int n0 in
         let rec elts i  =
          if i = n then []
          else 
           let o' = Index ((Cil.integer i),o) in
            (extract_pthread_fields o' t') @ (elts (i+1))
         in
         elts n
       | _ -> 
         []
        (* rs_impos "extract_pthread_fields/1: e=%s"
         (exp2str e)*)
       end
     | None -> 
         [](*im "extract_pthread_fields/2"*)
    end
          

  | TVoid _ 
  | TInt _ 
  | TFloat _ 
  | TPtr _ 
  | TEnum _ 
  | TBuiltin_va_list _ 
  | TFun _ -> [] 
 



class callVisitor = object (self) inherit nopCilVisitor

val mutable pthread_mutex_t  = Cil.TVoid []

val mutable pthread_mutex_init = Cil.dummyFunDec.svar

val mutable pthreads_vis = ([] : Cil.lval list) 

method doVar (vi : Cil.varinfo) : unit =
  (* register pthread_mutex_t in order*)
  ptxt "Checking Type %s of var : %s --- used ? %b\n"
    (typ2str vi.vtype) (vi.vname) (vi.vreferenced);
    let os = 
      extract_pthread_fields NoOffset vi.vtype in
    List.iter (fun o -> ptxt "Offset : %s  size = %d\n" 
                (offset2str o) ((bitsSizeOf vi.vtype)/8) ) os;
    if  is_pthread_mutex_t vi.vtype then 
      pthreads_vis <- pthreads_vis @ [Cil.var vi]
    else if os <> [] then
      pthreads_vis <- pthreads_vis @ 
      (List.map (fun o -> (Var vi,o)) os) 
    else 
      ptxt "Type %s does not contain pthread_mutex_t !\n"
        (typ2str vi.vtype);

method initLocal (vi : Cil.varinfo) : Cil.instr list =
   (*bitsSizeOf : typ -> int *)
   (* sizeOf : typ -> exp *)
   (* alignOf_int : typ -> int *)
   (* bitsOffset : typ -> offset -> int * int  (offset,width) *)
 self#doVar vi;
 []
 (*
 let ass (o:Cil.offset) (e:Cil.exp) : instr =  
    Set ( (Var vi,o),e,Cil.locUnknown) 
 in
 let init = makeZeroInit vi.vtype in
 let rec mkInit init o : instr list = 
 begin match init with 
    SingleInit e -> [ass o e]
  | CompoundInit (_,loi) ->
    let f l (o',i) = 
      l @ (mkInit i (Cil.addOffset o' o)) 
    in
    List.fold_left f  ([] :instr list) loi 
 end 
 in mkInit init NoOffset 
 *)

method private checkType (t:Cil.typ) : bool =
 (*TODO: handle case typedef pthread_mutex_t another_type*)
 let r t =  ()
(*  Printf.fprintf txt "Checking type : %s\n" (typ2str t)*) in
 not (existsType (fun t' -> r t';match t' with 
    TNamed (ti,_) ->  
      if ti.tname =  "pthread_mutex_t" then ExistsTrue
      else ExistsMaybe
  | TPtr _ -> ExistsFalse
  | _ ->  ExistsMaybe) t)
   (*
 match t with 
  TNamed (ti,_) -> ti.tname <> "pthread_mutex_t" 
   
 | TArray (t',_,_) -> self#checkType t'
 | TComp (ci,_) -> 
   Printf.fprintf txt "Checking type : %s\n" (typ2str t); 
       List.for_all (fun fi -> self#checkType fi.ftype)
       ci.cfields
 | _ -> true*)


val fun_map =  (Hashtbl.create 117 :
       (int,(int * (Cil.lval,int) Hashtbl.t)) Hashtbl.t)

val mutable fun_count = (-1)

(*method saveFunMap () =
 (*ptxt "Listing ht\n"; 
 Hashtbl.iter
 (fun k _ -> 
    ptxt "Key : %d\n" k ) fun_map; *)
 let fname = Filename.concat !dumpTo "funids.bin" in
 let handle = open_out fname  in
 Marshal.to_channel handle fun_map [];
 close_out handle*)

(*
method vstmt s = 
 (match s.skind with 
  | Return _ ->
    self#queueInstr ((pop_stack fun_count)::[])
  | _ ->  () 
  );
  DoChildren
*)

(*val mutable new_globals = ([] : Cil.global list)*)


method vglob g = 
(*ptxt "GLOBAL: %s\n" (any2str d_global g);*)
  match g with
  | GFun (fdec,loc) ->
      ptxt "DUMPFILE: GFUN 1\n";
      let var_map =  Hashtbl.create 117 in
      fun_count <- fun_count + 1;
      ptxt "Adding %d to ht\n" fdec.svar.vid;
      Hashtbl.add fun_map fdec.svar.vid (0,var_map);
      pthreads_vis <- []; (* reset local var counter  *)
      
      List.iter (fun vi -> self#doVar vi) fdec.sformals;
      
      let vl' = List.fold_left 
        (fun l vi -> 
          let l' = self#initLocal vi in 
          l @ l'
        ) []  fdec.slocals
      in
      ptxt "DUMPFILE: GFUN 2\n";
      (* insert instructions for manipulating 
       * the stack *)
      (*let (frame_vi,vl'') = 
        mk_rtstack fun_count fdec pthreads_vis in*)
      let vl = []  (*vl''*) (*@vl'*) in
      ptxt "DUMPFILE: GFUN 3\n";
      (* let s_i = Cil.mkStmt (Instr vl) in
        fdec.sbody.bstmts <- s_i::fdec.sbody.bstmts  ;*)
      let mk_si vl = (Cil.mkStmt (Instr vl)) in

      if (List.length vl) > 0 then        
        begin 
          match fdec.sbody.bstmts with
          | [] ->  () (* no initialization is required here*)
          | stmt::tl ->
              begin
                match stmt.skind with
                | Instr il -> 
                    fdec.sbody.bstmts <- (mk_si (vl@il))::tl
                | Block b ->
                    begin 
                      match b.bstmts with
                      | hd::tl ->
                          begin 
                            match hd.skind with
                            | Instr il -> 
                                b.bstmts <- (mk_si (vl@il))::tl
                            | _ ->
                                b.bstmts <- mk_si vl :: b.bstmts 
                          end 
                      | [] ->
                          b.bstmts <- [(mk_si vl)]
                    end
                | _ ->
                    fdec.sbody.bstmts <-  (mk_si vl)::fdec.sbody.bstmts
              end
        end;
      begin
        match fdec.svar.vtype with
        | TFun(tret, targsopt,isVarArg,_) ->
            let bret =  List.for_all self#checkType  
              (tret::
                (match targsopt with 
                | Some targs -> List.map (fun (_,t,_) -> t) targs
                | None -> []))
            in 
            if not bret then 
              begin 
                Printf.fprintf txt 
                  "%s : Bad type ! Explicit handles should not be passed by
                  value. (function type: %s)" (loc2str loc)
                  (typ2str fdec.svar.vtype) ; exit 0
              end
        | _ ->  Printf.fprintf txt "Unexpected type" ; exit 0
      end;
      DoChildren
  |GType (ti,loc) -> 
      checkTypes ti;
      if ti.tname = "pthread_mutex_t" then
        pthread_mutex_t <- ti.ttype;
      SkipChildren
      
  |GVar (vi,init,loc) ->
      (*init.init <- Some (makeZeroInit vi.vtype);*)
      SkipChildren
  | _                -> SkipChildren

end   

(************************************************************************)
(************************************************************************)


let dumpHelp = "path to dump results"

let strip1Slash (s:string) =
  if ((String.get s 0) = '/') then
    Str.string_after s 1
  else 
    s

(* Requires an argument stating the currently processed file *)
let curFile = ref ""
let getCurFile () =
  (if !curFile = "" then
     try
       curFile := (strip1Slash (Sys.getenv "CUR_CIL_FILE"));
     with Not_found ->
       prerr_string "Dumpfile: Can't find CUR_CIL_FILE environ var\n";
       curFile := "/tmp");
  !curFile

let getTargetFile (_:unit) =
  Filename.concat (getDumpTo ()) (getCurFile ())

let makeCFG fundec =
  if fundec.smaxstmtid = None && fundec.sallstmts = [] then begin
    Printf.printf "Making cfg for %s\n" fundec.svar.vname;
(*
    Cil.prepareCFG fundec;
    Cil.computeCFGInfo fundec false;
*)
    Cil.prepareCFG fundec;
    Cfg.clearCFGinfo fundec;
    ignore (Cfg.cfgFun fundec); (* handles "noreturn" attribute... *)
(*    let dotFile = 
      Filename.concat (getDumpTo ()) (fundec.svar.vname ^ ".cfg.dot") in
    Cfg.printCfgFilename dotFile fundec *)
  end else
    (*Printf.printf "Skipping cfg for %s\n" fundec.svar.vname*)
    ()

(* dumps the pre-processed / parsed file *) 
let dumpFile (f:file) =
  try
    (* Assume first character of f.fileName is '/' -- we skip that *)
    let dumpToFile = getTargetFile () in
    if Sys.file_exists dumpToFile then
      prerr_string ("Dumpfile: File " ^ dumpToFile ^ " already exists\n");

    f.fileName <- (getCurFile ()); (* store relative path/file name *)
    ensurePath (Filename.dirname dumpToFile);
    let outFile = (open_out_gen 
                     [Open_creat; Open_wronly] 
                     0o644 
                     dumpToFile) in
    
    (* Xform functions to CFGs first (non-unique stmt ids)... *)
    Cil.iterGlobals f (fun glob -> match glob with
                         Cil.GFun(fundec, _) -> makeCFG fundec
                       | _ -> ());

    (*
      Cil.dumpFile Cil.defaultCilPrinter outFile f;
    *)
    Cil.saveBinaryFileChannel f outFile;
    close_out outFile;
    
  with e -> Printf.printf "Exc. in dumpFile: %s\n"
    (Printexc.to_string e) ; raise e




(* insert our defs at the "right" places *)
let addGlobDefs f = 
  let newdefs = (mk_rstack_gdecl ())::[] in
  let is_the_typedef g = 
    begin 
      match g with
      | GType (ti,_) ->
          ti.tname = "stack_node_t" 
      | _ ->
          false 
    end 
  in
  let fd = getGlobInit f in
  let rec insert lst =
    match lst with
    | [] -> []
    | _::[] -> []
    | hd :: tl ->
        if is_the_typedef hd then
          (hd::newdefs) @ tl 
          (* missing extern decl  effects which 
           * are currently unknown
           * *)
          (*((GFun (fd,Cil.locUnknown))::tl)*)
        else 
          hd::(insert tl)
  in
  (*f.globals <- newdefs @ f.globals *)
  let g = (insert f.globals) 
  (* (List.map
       (fun vi->GVarDecl (vi,Cil.locUnknown)) vis) @
       (insert f.globals) *)
  in
  let g' = 
    List.filter (fun g ->
      match g with 
      | GVar (vi,_,_) ->
          vi.vname <> "dummy___stack"
      | _ -> true 
    ) g 
  in 
  f.globals <- g'

    

(* Entry point
 * @arg f   a parsed Cil file
 *)      
let dump (f:file) =
  try
    let lkvis = new callVisitor in
    let cilvis = (lkvis : callVisitor :>Cil.cilVisitor) in
    (* f.globals <- header_file.globals @ f.globals;*)
    ptxt "DUMPFILE: visiting globals\n";
    visitCilFileSameGlobals cilvis f;
    ptxt "DUMPFILE: adding global definitions\n";
    addGlobDefs  f;
    ptxt "DUMPFILE: dumping file\n";

    dumpFile f;
    (*lkvis#saveFunMap ();*)
    close_out txt
  with 
  | (Impossible s) as e -> 
      ptxt "DUMPFILE: received an IMPOSSIBLE: %s\n" s;
      close_out txt;
      raise e
  | Not_found as e -> 
      ptxt "DUMPFILE: received an NOT_FOUND\n";
      close_out txt;
      raise e
  | e ->
      ptxt "DUMPFILE: received an unknown exception\n";
      close_out txt;
      raise e

(* Cil feature descriptor API *)

let doDumpFile = ref false

let feature : featureDescr = 
  { fd_name = "dumpfile";
    fd_enabled = doDumpFile;
    fd_description = "Dumps pre-processed file";
    fd_extraopt = 
      [("--dumproot", Arg.String (fun s -> dumpTo := s), dumpHelp)];
    fd_doit = dump;
    fd_post_check = true
  } 
