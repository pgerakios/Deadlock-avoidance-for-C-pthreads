open Cil

module D = Cildump
module PTA = Myptranal
module L = List
open Printf
open Pretty
open Trans_alloc


let txt = ref stdout

let gettxt () = !txt

let settxt () = 
  txt := open_out_gen [Open_append] 777 "allocation.out"

(*let txt = open_out "allocation.out"*)
(*let txt = open_out_gen [Open_append] 777 "allocation.out"*)

let logtxt format =  Printf.ksprintf
  (fun x ->Printf.fprintf !txt "%s" x) format
  
(* Counters *)
let function_counter  = ref 0 
let global_c          = ref 0
let static_c          = ref 0
let local_c           = ref 0
let dyn_alloc_c       = ref 0
let array_c           = ref 0
let rec_struct_c      = ref 0

let inc i = 
  i := !i + 1

let any2str f e = (sprint 80 (dprintf "%a" f e))
let exp2str     = any2str d_exp 
let typ2str     = any2str d_type 
let lval2str    = any2str d_lval
let off2str = any2str (Cil.d_offset (text "<base>"))


let loc2strsmall loc = 
  let (file,line) = (loc.file, loc.line) in
  let li = 
    try String.rindex file '/' 
    with Not_found -> -1
  in
  let only_name = String.sub file (li+1) ((String.length file) - li -1) in
  only_name^":"^(string_of_int line)

let testPthread str =
  try 
    let pref = String.sub str 0 (String.length "pthread_mutex_t") in
    pref = "pthread_mutex_t"
  with _ -> false

(* is the type : `pthread_mutex` ? *)
let typeOfLock typ = 
	match typ with
	| TComp (ci, _) ->
      testPthread ci.cname
  		(*ci.cname = "pthread_mutex"*)
	| TNamed (t, _) -> 
      testPthread t.tname
      (*t.tname = "pthread_mutex_t"*)
	| _ -> false

(* is the type : `pthread_mutex_t *` ? *)
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
      (*ExistsMaybe*)
      match t with
      | TComp (ci,_) ->
          (* Conservative approach:
           * This hack aims at resolving cases where 
           * the type is only declared as a prototype.*)
          if ci.cfields = [] then ExistsTrue
          else ExistsMaybe
      | _ -> ExistsMaybe
  in
  typeOfLock inType || typeOfLockPtr inType ||
  existsType decide inType



let rec typ2offsetl t =
  if typeOfLock t then
    (* we found the lock *)
    [NoOffset]
  else
    match t with
    (* not insteresting cases *)
    | TVoid _ | TInt _ | TFloat _ | TFun _
    | TEnum _ | TBuiltin_va_list _ -> []
    
    (* pointers mean dereference, so the locks will
     * have to be allocated elsewise *)
    | TPtr (t,_) -> []

    (* arrays of locks ? *)
    | TArray (t,exp_opt,_) ->
        let offl = typ2offsetl t  in
        begin
          match exp_opt with
          | Some exp ->
              L.map (fun o -> Index(exp,o)) offl
          | _ ->
              L.map (fun o -> Index(Cil.integer 0,o)) offl
        end

    (* TNamed will have been unfolded*)
    | TNamed _ -> []

    | TComp (ci,_) -> 
        let ctl = 
          L.map 
            (fun fi -> 
              let offl = typ2offsetl fi.ftype in
              L.map (fun o -> Field (fi, o)) offl
            ) ci.cfields
        in
        L.concat ctl

(* Check if an lvalue is an array *)
let rec lvalContainsIndex lval = 
  match lval with
  | _ , Index (_,o) -> true 
  | Mem exp , Field (_,o) -> 
      offsetContainsIndex o ||
      expContainsIndex exp
  | _ -> false
and offsetContainsIndex off = 
  match off with
  | Index (_,o) -> true 
  | Field (_,o) -> offsetContainsIndex o
  | _ -> false
and expContainsIndex exp = 
  match exp with
  | SizeOf _ | SizeOfStr _ -> false
  | CastE (_, e2) -> expContainsIndex e2
  (* an indx is usually hidden in here *)
  | BinOp (op, e1, e2, _) -> true
  | UnOp (_,e1,_) -> expContainsIndex e1
  | AlignOf _ -> false
  | AlignOfE e | SizeOfE e -> expContainsIndex e
  | Const _ -> false
  | Lval lv | AddrOf lv -> lvalContainsIndex lv
  | StartOf e -> false

let rec containsArithmetic exp : bool =
  match exp with
    SizeOf _ | SizeOfE _ | SizeOfStr _ -> false
  | CastE (_, e2) -> containsArithmetic e2
  | BinOp (op, e1, e2, _) ->
      containsArithmetic e1 ||
      containsArithmetic e2
  | UnOp (_,e1,_) -> containsArithmetic e1
  | AlignOf _ -> false
  | AlignOfE e -> containsArithmetic e 
  | Const _ -> false
  | Lval _ | AddrOf _ | StartOf _ -> false
 

module TypeSet = Set.Make (
  struct
    type t = Cil.typ
    let compare = Ciltools.compare_type
  end)


let containsRecursiveStruct t =   
  let rec crs carry tset t = 
    match t with
    | TVoid _ | TInt _  | TFloat _ | TFun _
    | TEnum _ | TBuiltin_va_list _ -> false
    (* There will be no TNamed *)
    | TNamed _ -> false

    | TPtr (t',_) | TArray (t',_,_) -> 
        if TypeSet.mem t' tset && carry then true        
        else 
          let tset' = TypeSet.add t tset in
          crs carry tset' t'

    | TComp (cinfo,_) -> 
        let tl = L.map (fun field -> field.ftype) cinfo.cfields in
        (* is one of the fields a lock ? *)
        let carry' =
          carry || (L.exists typeContainsLock tl) in
        let tset' = TypeSet.add t tset in
        L.exists (crs carry' tset' ) tl
  in
  let t' = unrollTypeDeep t in
  crs false TypeSet.empty t'


let rec unrollToPthread t = 
  match t with
  | TNamed (ti,_) -> 
      if ti.tname <> "pthread_mutex_t" then
        ti.ttype 
      else t (*unrollToPthread ti.ttype*)
  | TComp (ci,_) -> begin
      L.iter (fun f -> f.ftype <- unrollToPthread f.ftype ) ci.cfields;
      t
    end
  (*| TPtr (t',a) -> TPtr (unrollToPthread t, a)*)
  | TArray (t,e,a) -> TArray (unrollToPthread t,e,a)
  | _ -> t

(** This function returns all lvalues that are lock handles and are
 * located inside an lvalue (1st parameter). *)
let lval2locklvals lval : lval list = 
  let inType = typeOfLval lval in
  let offset_list = typ2offsetl inType in
  L.map (fun o -> addOffsetLval o lval) offset_list

let var2locklvals vi : lval list = 
  let inType = unrollToPthread vi.vtype in
  let offset_list = typ2offsetl inType in
  L.map (fun o -> (Var vi, o)) offset_list


 
let lock_name x : bool =
  match x with
  |  "pthread_mutex_lock" -> true
  |  "pthread_mutex_unlock" -> true
  |  "pthread_mutex_trylock" -> true
  |  "pthread_cond_wait" -> true
  | _       -> false


type alias_map = (Cil.location,string list) Hashtbl.t
type cg_alias_map = (Cil.prog_point,string list) Hashtbl.t

type alias_bin_type = (alias_map * cg_alias_map)

(* Retrieve previous alias.bin *)
let ((alias_map, cg_alias_map) : alias_bin_type) =
  let fname = Filename.concat "ciltrees" "alias.bin" in
  if Sys.file_exists fname then
  	let ic = open_in fname in
    let (a, cga) = (Marshal.from_channel ic : alias_bin_type) in
    close_in ic;
    (a, cga)
  else
    (Hashtbl.create 50, Hashtbl.create 50)



class statsVisitor = object (self)
  inherit nopCilVisitor 

  val mutable cur_fname = ""
  val mutable cur_fid = -1

  val mutable mysid = 0 
  val mutable myinst = 0   
  val mutable mypp = {pp_stmt=0; pp_instr=0;}

  method vfunc fd = 
    cur_fname<- fd.svar.vname;
    cur_fid<- fd.svar.vid;
    DoChildren

  method vstmt s = 
    mysid <- s.sid;
    myinst <- 0;
    DoChildren

  method vinst (i:instr) = 
    mypp <- {pp_stmt=mysid; pp_instr=myinst };
    myinst <- myinst + 1;

    let rec resolveCall0 a_opt (exp:exp) : string list = 
      match exp with
        Lval(Var(va), NoOffset) ->
          [va.vname]
      | Lval(Mem(ptrexp), NoOffset) ->
            let names = Trans_alloc.resolveFP ptrexp in
            (*begin match a_opt with
             | Some a -> 
               logtxt "Expr: %s %d\n"
               (exp2str ptrexp) (List.length names);
                List.iter
                (fun x -> 
                   logtxt "ALIAS: %s\n" x) names;
               let names' = (PTA.resolve_funptr ptrexp) in
                  List.iter
                  (fun fd-> logtxt "FUN : %s\n" fd.svar.vname ) names';
                  a (List.map (fun fd-> fd.svar.vname)
                     names')
             | None -> () 
            end;*)
            names

      | CastE(t, e) -> resolveCall0 a_opt e
      | _ -> 
          prerr_string "allocVisitor: unknown callexp form\n";
          []
    in

    let resolveCall = resolveCall0 None in
    (* add aliases to table*)
    begin match i with 
     | Call (_,callexp,_,loc) ->
         begin
           ignore(resolveCall0 (Some (addAlias loc)) callexp);
           ignore(resolveCall0 (Some (addCgAlias mypp)) callexp)
         end
     | _ -> ()
    end;

    match i with
      Call (Some(retval), callexp, actuals, loc) ->
        begin
          (*Printf.printf "[%s] Calling %s.\n"
              (loc2strsmall loc) (exp2str callexp);*)

          let retType = typeOfLval retval in 
          let fnames = resolveCall callexp in
          let is_malloc = (L.exists (fun fn -> Alloc.isAlloc fn ) fnames) in




          if is_malloc then 
            begin
              match retType with
              | TPtr (t, _) -> begin
                  try
                    let finalT = pickType t actuals in
                    let finalT = unrollToPthread finalT in
                    let offset_list = typ2offsetl finalT in
                    (*Printf.printf "%s: Allocating: %s\n"
                      (loc2strsmall loc) (typ2str finalT);*)

                    L.iter (fun o -> 
                      (*let lvt = Cil.typeOfLval lv in
                      let lv =  mkMem (Lval retval) NoOffset in*)
                      if containsRecursiveStruct finalT then begin
                        Printf.printf "%20s:  RECURSIVE STRUCTURE \
                          CONTAINING LOCK: %s\n"(loc2strsmall loc) 
                          (typ2str finalT);
                        inc rec_struct_c
                      end;
                      inc dyn_alloc_c;
                      if L.length actuals > 0 && 
                        L.for_all containsArithmetic actuals then begin
                        inc array_c;
                        Printf.printf "%20s:  DYNAMIC ALLOCATION OF \
                        AN ARRAY `%s' (type: %s) \n" (loc2strsmall loc) 
                        (off2str o) (typ2str finalT);
                      end
                      else                        
                        Printf.printf "%20s:  DYNAMIC ALLOCATION OF `%s' 
                        (type: %s)\n" (loc2strsmall loc) (off2str o) 
                        (typ2str finalT)
                    ) offset_list;                                         
                    DoChildren
                  with _ -> 
                    Printf.printf "%20s:  UNRESOLVED DYNAMIC ALLOCATION\n"
                      (loc2strsmall loc);
                    DoChildren
                end
              | _ -> DoChildren
              end
          else if (L.exists lock_name fnames) (*&&
                  (L.exists expContainsIndex actuals)*) then
            (* This is a lock operation with an index in it *)
                    begin
                      inc array_c;
                      Printf.printf "%20s:  LOCKING AN ARRAY ELEMENT\n"
                        (loc2strsmall loc);
                      L.iter (fun e -> Printf.printf "\t\t\t%s\n" (exp2str e))
                      actuals;                      
                      DoChildren
                    end
          else
            DoChildren
        end
    | Call (_, callexp, actuals, loc) ->
        let fnames = resolveCall callexp in
        if (L.exists lock_name fnames) &&
          (L.exists expContainsIndex actuals) then
            (* This is a lock operation with an index in it *)
            begin
              inc array_c;
              Printf.printf "%20s:  LOCKING AN ARRAY ELEMENT\n"
              (loc2strsmall loc);
              L.iter (fun e -> Printf.printf "\t\t\t%s\n" (exp2str e))
                actuals;
              DoChildren
            end
        else
            DoChildren
       


    | Set (lv, exp, loc) -> 
        let lv_t = typeOfLval lv in
        if typeContainsLock lv_t && 
          (containsArithmetic exp || expContainsIndex exp) then 
          begin
            inc array_c;
            Printf.printf "%20s:  ASSIGNING AN ARRAY ELEMENT\n"
              (loc2strsmall loc)
          end;
          DoChildren

    | _ -> 
        DoChildren

  method vglob (g:global) : global list visitAction =
    match g with
    | GFun (fd, loc) -> 
        begin
          L.iter (fun vi -> 
            if typeContainsLock vi.vtype then 
              function_counter := !function_counter + 1; 
              (*Printf.printf "%20s:  FORMAL PARAMETER: \
                `%s' of function `%s'.\n"
              (loc2strsmall loc) vi.vname fd.svar.vname;*)
          ) fd.sformals;
          L.iter (fun vi -> 
            let lvs = var2locklvals vi in
            L.iter (fun lv -> 
              let lvt = Cil.typeOfLval lv in
              inc local_c;
              (* static locals are defined as globals *)
              Printf.printf "%20s:  LOCALY SCOPED: `%s' of function `%s'.\n"
                (loc2strsmall loc) (lval2str lv) (typ2str lvt)
            ) lvs
          ) fd.slocals;
         DoChildren
        end
    | GVar (varinfo, _, loc) ->
        begin
          (*Printf.printf "%s : %s (%s)\n" (loc2strsmall loc) (varinfo.vname)
            (typ2str varinfo.vtype);*)
          let lvs = var2locklvals varinfo  in
          L.iter (fun lv ->
            let lvt = Cil.typeOfLval lv in
            (* Check for recursive and arrays *)
              if containsRecursiveStruct varinfo.vtype then begin
                inc rec_struct_c;
                Printf.printf "%20s:  RECURSIVE STRUCTURE CONTAINING LOCK: %s\n"
                  (loc2strsmall loc) (typ2str varinfo.vtype)
              end;
              if lvalContainsIndex lv then begin
                inc array_c;
                Printf.printf "%20s:  GLOBAL LOCK ARRAY: %s\n"
                  (loc2strsmall loc) (typ2str varinfo.vtype)
              end;
              begin
              match varinfo.vstorage, varinfo.vglob with
              | Static, true -> 
                  begin
                    inc static_c;
                    Printf.printf "%20s:  GLOBAL STATIC LOCK VARIABLE: %s\n"
                    (loc2strsmall loc) (typ2str varinfo.vtype)
                  end
              | Static, false -> 
                  (* No such thing: all local statics are globals *)
                  Printf.printf "%20s:  LOCAL STATIC LOCK VARIABLE: %s\n"
                    (loc2strsmall loc) (typ2str varinfo.vtype)
              | _,true ->
                  begin
                    inc global_c;
                    Printf.printf "%20s:  SIMPLE GLOBAL LOCK VARIABLE: %s\n"
                      (loc2strsmall loc) (typ2str varinfo.vtype)
                  end
              | _,_ -> ()
              end
            ) lvs;
          DoChildren        
        end
    | _ ->
        DoChildren        
end
     
let vis = new statsVisitor

let doStats (f:file) = 
  Cfg.computeFileCFG f;
  settxt ();
  visitCilFile (vis :> cilVisitor) f;
  if !function_counter > 0 then 
    Printf.printf "%20s   FUNCTIONS WITH LOCKS IN PARAMETERS: %d\n"
    "" !function_counter;
(* dump results in file *)
  logtxt "%s %d %d %d %d %d %d %d\n" f.fileName !function_counter !static_c
    !global_c !local_c !dyn_alloc_c !array_c !rec_struct_c;

  (*dumpFile defaultCilPrinter stdout "" f;*)
  Pervasives.flush_all ()


(*** Cil feature descriptor API ***)

let doLockStats = ref false

let feature : featureDescr = 
  { fd_name = "lockstats";
    fd_enabled = doLockStats;
    fd_description = "statistics regarding lock usage.";
    fd_extraopt = [];
    fd_doit = doStats;
    fd_post_check = true
  } 
