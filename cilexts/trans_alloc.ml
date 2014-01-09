open Cil

module D = Cildump
module PTA = Myptranal

(*** Naming fresh global vars (used to substitute/represent alloc calls) ***)

(* use this regexp to grab the first portion of the filename that is
   valid for variable names *)
let varnameRegExp = Str.regexp "[_a-zA-Z][_a-zA-Z0-9]*"

let allocNameRegExp = Str.regexp "_a[0-9]+_[0-9]*_[_a-zA-Z][_a-zA-Z0-9]*_[0-9]*"

let nameLine ln =
  string_of_int ln

let nameByte b =
  if (b > 0) 
  then (string_of_int b)
  else ""
    
let nameFile f =
  let baseF = Filename.basename f in
  (if (Str.string_match varnameRegExp baseF 0) then
     Str.matched_string baseF
   else "alloc")
    
let nameAllocVar ( { line = ln;
                     file = f;
                     byte = b; } :location) (moreID : int) =
  "_A_" ^ (*nameLine ln ^ "_" ^ 
    nameByte b ^ "_" ^
    nameFile f ^ "_" ^ 
    (string_of_int moreID)*)
    nameFile f ^ "_" ^
    nameLine ln ^ "_" ^
    (*nameByte b ^ ":" ^*)
    string_of_int moreID

let nameAllocVarMD5 ( { line = ln; file = f; byte = b; }:location)
  (moreID : int) =
  "_a" ^ nameLine ln ^ "_" ^
  (Digest.to_hex (Digest.string (nameFile f ^ "_" ^ nameByte b)))

let isAllocVar (n:string) : bool =
  Str.string_match allocNameRegExp n 0

(** Reversing the process. How to find out if an assignment was
    original a malloc call, given the RHS of the assignment. *)
let rec findMalloc exp =
  match exp with
    AddrOf (Var v, _) 
  | StartOf (Var v, _) ->  if isAllocVar v.vname then Some (v) else None
  | AddrOf (Mem _, _)
  | StartOf (Mem _, _)
  | Lval _ -> None
  | CastE (t, e) -> findMalloc e
  | Const _ | SizeOf _ | SizeOfStr _ | SizeOfE _ 
  | AlignOf _ | AlignOfE _ | UnOp _ | BinOp _  -> None

let unknownMallocType = 
  (* turn void types in arrays of uchar (arbitrary, but unlikely size) *)
  TArray (TInt (IUChar, []), Some (Cil.integer 231), [])

 
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

let warnHasMultipleSizeOf exp =
  let rec loop cur exp =
    match exp with
      SizeOf _ | SizeOfE _ | SizeOfStr _ -> cur + 1
    | Const _ | Lval _ | AddrOf _ | StartOf _ | AlignOf _ | AlignOfE _ -> cur
    | CastE (_, e) -> loop cur e
    | UnOp (_, e, _) -> loop cur e
    | BinOp (_, e1, e2, _) -> 
        let c = loop cur e1 in
        loop c e2
  in
  if loop 0 exp > 1 then
    Printf.fprintf stderr "Alloc: multiple sizeof (%s) @ %s\n"
      (D.string_of_exp exp) (D.string_of_loc !currentLoc)

let rec typeFromSizeOf cur exp =
  match cur with 
    Some x -> cur
  | None ->
      try findSizeOf exp
      with Not_found -> cur

and findSizeOf exp =
  match exp with
    SizeOf t -> Some t
  | SizeOfE e -> Some (typeOf e)
  | SizeOfStr _ -> Some (!stringLiteralType)
  | CastE (_, e2) -> findSizeOf e2
  | BinOp (op, e1, e2, _) ->
      (try
         let sz1 = findSizeOf e1 in
         try 
           let _ = findSizeOf e2 in
           warnHasMultipleSizeOf exp;
           sz1
         with Not_found ->
           sz1
       with Not_found ->
         findSizeOf e2)
  | UnOp (op, e1, _) ->
      findSizeOf e1
  | AlignOf _ | AlignOfE _ | Const _
  | Lval _ | AddrOf _ | StartOf _ -> raise Not_found


let pickType retType actuals =
  match List.fold_left typeFromSizeOf None actuals with
    None -> if (isVoidType retType) then unknownMallocType else retType
  | Some t ->
      (*if Ciltools.compare_type retType t <> 0 then
        Printf.fprintf stderr "Trans_alloc: %s <> %s\n" 
          (D.string_of_type retType) (D.string_of_type t);*)
      (* Should do something smarter to pick the widest? *)
      if (isVoidType t) then
        if (isVoidType retType) then unknownMallocType
        else retType
      else t


(**** My stuff ****)

let txt = open_out "my.out"  
let logtxt format =  Printf.ksprintf
  (fun x ->Printf.fprintf txt "%s" x) format  
let any2str f e  = 
         (Pretty.sprint 80 
            (Pretty.dprintf "%a" f e)) 
let exp2str = any2str d_exp
let typ2str = any2str d_type

type malloc_map = (location, string * string * bool * varinfo) Hashtbl.t
type malloc_map_inv = (string, location * string * bool * varinfo) Hashtbl.t
type alias_map = (Cil.location,string list) Hashtbl.t
type cg_alias_map = (Cil.prog_point,string list) Hashtbl.t

type malloc_bin_type = (malloc_map * malloc_map_inv * alias_map * cg_alias_map)

(* Retrieve previous alias.bin *)
let ((malloc_map, malloc_map_inv, alias_map, cg_alias_map) : malloc_bin_type) =
  let fname = Filename.concat "ciltrees" "alias.bin" in
  if Sys.file_exists fname then
  	let ic = open_in fname in
    let (m0, m1, a, cga) = (Marshal.from_channel ic : malloc_bin_type) in
    close_in ic; (m0, m1, a, cga)
  else
    (Hashtbl.create 50, Hashtbl.create 50, Hashtbl.create 50,Hashtbl.create 50) 


let saveAliases () : unit = 
  let fname = Filename.concat "ciltrees" "alias.bin" in
  let oc = open_out fname in
  Marshal.to_channel oc 
  ((malloc_map,malloc_map_inv, alias_map, cg_alias_map) : malloc_bin_type) [];
  close_out oc

(* keep an extra boolean to denotate addresses we want to keep in the hash *)
let addMallocGlobal fnm loc g keep vi =
  Hashtbl.add malloc_map loc (g,fnm,keep,vi);
  Hashtbl.add malloc_map_inv g (loc,fnm,keep,vi)

let addAlias loc aliases = 
 let l = try Hashtbl.find alias_map loc 
         with Not_found -> []  in 
 let l' = List.filter 
         (fun x -> not 
           (List.exists (fun y -> x = y) aliases)) l in
  Hashtbl.replace alias_map loc (l' @ aliases)

let addCgAlias pp aliases = 
  let l = try Hashtbl.find cg_alias_map pp
         with Not_found -> []  in 
  let l' = List.filter
         (fun x -> not
           (List.exists (fun y -> x = y) aliases)) l in
  Hashtbl.replace cg_alias_map pp (l' @ aliases)


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

  (*
let log = Printf.printf
let any2str f e  = (Pretty.sprint 80 (Pretty.dprintf "%a" f e))
let typ2str     = any2str Cil.d_type
module TypSet = Set.Make (
       struct
         type t = Cil.typ
         let compare a b = 
           String.compare (typ2str a) 
             (typ2str b)
       end
      )

let tset : TypSet.t ref = ref TypSet.empty

let traverse typ =
  let dorec f s t = 
    if not (TypSet.mem t s) then f (TypSet.add t s) t
    else log "*" (*typ2str t*) in
  let rec  traverseT s typ = 
    match typ with
    | TVoid _ -> log "Tvoid "
    | TInt _ -> log "TInt "
    | TFloat _ -> log "TFloat "
    | TPtr (t,_ ) -> (log "TPtr (" ; dorec traverseT s t; log ") ")
    | TArray (t,_,_) -> (log "TArr ("; dorec traverseT s t; log ") ")
    | TFun _ -> log "TFun "
    | TNamed (ti,_) -> ( log "TNamed %s (" ti.tname; dorec traverseT s ti.ttype)
    | TComp (ci,_) -> (log "TComp %s (" ci.cname; List.iter (
      fun fld -> dorec traverseT s fld.ftype; log "; ") ci.cfields ; log ") ")
    | TEnum _ -> log "TEnum "
    | TBuiltin_va_list _ -> log "TBuiltin "
  in
  traverseT TypSet.empty typ ;
  log "\n"
*)


(*** The actual transformation ***)

(** A visitor that converts p = alloc(x), into p = &fresh_global *)
class allocVisitor = object (self)
  inherit nopCilVisitor 

  val mutable cur_fname = ""

  val newVars = ref []

  val alreadyUsedLocs = Hashtbl.create 11

  method checkUsed loc =
    let oldID = try Hashtbl.find alreadyUsedLocs loc with Not_found -> 0 in
    let newID = oldID + 1 in
    Hashtbl.replace alreadyUsedLocs loc newID;
    newID

  val mutable mysid = 0 
  val mutable myinst = 0   
  val mutable mypp = {pp_stmt=0; pp_instr=0;}

  method vfunc fd = 
    (*Printf.printf "In func: %s. %d\n" fd.svar.vname fd.svar.vid;*)
    DoChildren

  method vstmt s = 
    mysid <- s.sid;
    myinst <- 0;
    DoChildren

  method vinst (i:instr) : instr list visitAction = 
    mypp <- {pp_stmt=mysid; pp_instr=myinst };
    myinst <- myinst + 1;
    let rec resolveCall0 a_opt (exp:exp) : string list = 
      match exp with
        Lval(Var(va), NoOffset) ->
          [va.vname]
      | Lval(Mem(ptrexp), NoOffset) ->
            let names = resolveFP ptrexp in
            begin match a_opt with
             | Some a -> 
               logtxt "Expr: %s %d\n"
               (exp2str ptrexp) (List.length names);
                List.iter
                (fun x -> 
                   logtxt "ALIAS: %s\n" x) names;
               let names' = (PTA.resolve_funptr ptrexp) in
                  List.iter
                  (fun fd-> logtxt "FUN : %s\n" 
                      fd.svar.vname ) names' ;
                 a (List.map (fun fd-> fd.svar.vname)
                     names')
             | None -> () 
            end ;
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
           ignore(resolveCall0 (Some  (addAlias loc)) callexp);
           ignore(resolveCall0 (Some  (addCgAlias mypp)) callexp)
         end
     | _ -> ()
    end;

    match i with
      Call (Some(retval), callexp, actuals, loc) ->
(* TODO : translate even if retType is Int and call is to a malloc'er *)
        let retType = typeOfLval retval in begin
        match retType with
          TPtr (t, _) ->
            let fnames = resolveCall callexp in
            let finalT = pickType t actuals in
            (* Check for alloc of locks or structs containing locks. *)
            let ft = TPtr (finalT,[]) in
            let cont_lock = typeContainsLock ft in
            let is_malloc = 
              (List.exists 
                (fun fn -> 
                    let res = Alloc.isAlloc fn in
                    (*if res then
                      (Printf.printf "[%d] Found lock malloc %b\n"
                        loc.line cont_lock;
                      traverse finalT);*)
                    res
              ) fnames) in

            (* Changing this: only interested in direct mallocs*)
            if cont_lock && is_malloc then
              let moreID = self#checkUsed loc in
              let name = nameAllocVar loc moreID in
              let freshAllocVar = Cil.makeGlobalVar name finalT in
              newVars := freshAllocVar :: !newVars;
              (* my stuff *)
              Printf.printf "Creating var: %s " name ;
              Pretty.printf "(%a)\n" d_type finalT;
              (*traverse_type retval;*)
              addMallocGlobal cur_fname loc name true freshAllocVar;
              let fresh =  Cil.mkAddrOf(Var(freshAllocVar), NoOffset) in
              ChangeTo [ i ; Set (retval,fresh,loc); Cil.dummyInstr]
              (* end of my stuff *)
              (*Printf.printf "[line %d] Just changed a malloc.\n" loc.line;
                Printf.printf "[line %d] Returned type: %s\n" 
                loc.line (typ2str finalT);*)
            else
              SkipChildren
                
        | _ -> SkipChildren
        end                                                     
    | _ -> 
        SkipChildren 


  method vglob (g:global) : global list visitAction =
    let addDecls (parentFun:fundec) (loc:location) (globs:global list) =
      if (!newVars <> []) then begin
        (* Hack to know what the malloc callers are *)
        (*Printf.fprintf stderr "Trans_alloc: %s %s\n" parentFun.svar.vname 
          (D.string_of_loc loc);*)

        (* add global var decls to the list of globals *)
        let newGs = List.fold_left 
          (fun curGlobs newVar ->
             newVar.vdecl <- loc;
             GVarDecl (newVar, loc) :: curGlobs) globs !newVars in
        newVars := [];
        newGs
      end
      else
        globs
    in
    
    match g with
      GFun (f, loc) -> (* only place that can have instructions? *)
        begin
          cur_fname <- f.svar.vname;
          ChangeDoChildrenPost ([g], addDecls f loc)
        end
    | _ ->
        SkipChildren        
end
     
(**  Entry point -- ASSUMES PTA analysis has been run
     @arg f   a parsed Cil file  *)      
let transformAlloc (f:file) = 
  Cfg.computeFileCFG f;
  let vis = new allocVisitor in
  visitCilFile (vis :> cilVisitor) f;
  (*dumpFile defaultCilPrinter stderr "" f;*)
  saveAliases ()


(*** Cil feature descriptor API ***)

let doTransformAllocs = ref false

let feature : featureDescr = 
  { fd_name = "trans_alloc";
    fd_enabled = doTransformAllocs;
    fd_description = "Transforms invocations of alloc functions to &global";
    fd_extraopt = 
      [];
    fd_doit = transformAlloc;
    fd_post_check = true
  } 
