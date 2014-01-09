open Cil
open Simple_definitions
open Simple_effect_dataflow
open Simple_effect_tools
open Simple_effect_checks

module D = Definitions


let peep_f : bool ref = ref false

let resetPeep () =
    peep_f := false;
    
(* Simple flow-insensitive visitor which checks if a function has an effect or
 * not. If there isn't, we avoid the dataflow (which costs more). *)
class peepEffectVisitor = object (self)
  inherit nopCilVisitor 

  method vinst (i:instr) = 
    match i with
    | Call (lvo,e,_,loc) ->
        begin
          begin
            match e with          
            | Lval (Var vi, off) ->
                (* Found a lock/unlock operation *)
                if D.isFunLockOp vi.vname then
                  peep_f := true;
            | _ -> ()
          end;
          let fids =
            match e with
            (* Direct call *)
            |	Lval(Var(callfn),_) ->
                [callfn.vid]
            (* Indirect Call *)
            | _ -> begin
                try
                  let strs = Modsummary.alias_map loc in
                  let vids = L.flatten (List.map (
                    fun s -> 
                      match Cilinfos.varinfo_of_name s with
                      | Some vi -> [vi.vid]
                      | None -> []
                    ) strs)
                  in
                  D.dlog "[%s] PTA for `%s' returned:\n" 
                      (D.loc2strsmall loc) (D.exp2str e);
                  if L.length strs = 0 then 
                    D.dlog "\t<empty>\n"
                  else
                    L.iter (fun s -> D.dlog "\t%s\n" s) strs;
                  vids
                with Not_found -> 
                  let _ = D.warn "[%s] PTA resolve for `%s' returned \
                              \"Not_found\".\n"
                    (D.loc2strsmall loc) (D.exp2str e) in []
                end
          in
          let fid2peep id = 
            try 
              let fs = H.find simpleFInfoHash id in
              fs.has_effect;              
            with Not_found ->
            (* Not declared in the sources, we assume they don't 
             * produce effects. *)
              !peep_f
          in
          let curr =
            L.fold_left (
              fun feed p -> feed || p)
              false (L.map fid2peep fids) in
          peep_f := !peep_f || curr;
          DoChildren        
        end
    | _ -> DoChildren
end

let peepEffect fn =
  resetPeep ();
  let vis = new peepEffectVisitor in 
  ignore(visitCilFunction vis fn);
  try 
    let fs = H.find simpleFInfoHash fn.svar.vid in
    fs.has_effect <- !peep_f;
    (*log "This function has malloc: %b, effect: %b.\n"
    fs.has_malloc fs.has_effect*)
  with Not_found -> ()

let simpleEffectComp (fd : fundec) (funStruct : simpleFunInfo_t) : unit =
  cur_sfstruct := funStruct;
  peepEffect fd;

  if funStruct.has_effect then begin
    Sanity.reset ();
    
    (* Initialize Dataflow *)
    initializeDF fd.svar.vid fd;
    
    (* Compute the function's effect *)
    computeFunEffect ();
    
    (* Get the result *)
    let funSt = getOutState () in
    let funEff = funSt.outEff in
    
    let cleanedEff = fixInline funEff in
    let backpatchedEff = backpatch cleanedEff in
    let finalEff = fixInline backpatchedEff in

    funStruct.sEffect <- finalEff;
    funStruct.summary <- summarize finalEff;
    

    if finalEff <> [] then begin
      D.log "%s" (magenta D.thick_line);
      D.log  "\027[35m\027[1m Lock results for function `%s' \
              (decl.: %s) (vid:%d)\n\027[0m"
        fd.svar.vname (D.loc2strsmall fd.svar.vdecl) fd.svar.vid;
      funWeffect_count := !funWeffect_count + 1;
      let eff_sz = effect_size finalEff in
      total_effect_size := eff_sz :: !total_effect_size;
      D.log "Size: %d\n" eff_sz;
      (*
      H.iter (fun i eff ->
        (*IntMap.iter (fun i e ->
          let e' = fixInline (filterBp i e) in
          (*if e' <> [] then*)
            (D.log "%d.\n" i;
            print_seffect e)) eff;*)
        let f = fixInline (backpatch (cp_effect_list_2 (fmap2flist eff))) in
        if f <> [] then
          (D.log "%d.\n" i;
          print_seffect f)
      ) !loopHashRef;
      D.log "----------\n";
      print_seffect cleanedEff;*)
      (*D.log "Distinct exps:\n";
      distinctExps finalEff;*)
    
      doFuncCountLocks finalEff;
      Sanity.check_sanity finalEff;
    (*D.printDotFile fd*)
    end  
  end
    (*else
      D.log "### Won't dataflow `%s'\n" fd.svar.vname*)
