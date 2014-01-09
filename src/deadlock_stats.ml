(*
  Copyright (c) 2006-2007, Regents of the University of California

  Authors: Jan Voung
  
  All rights reserved.
  
  Redistribution and use in source and binary forms, with or without 
  modification, are permitted provided that the following 
  conditions are met:
  
  1. Redistributions of source code must retain the above copyright 
  notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above 
  copyright notice, this list of conditions and the following disclaimer 
  in the documentation and/or other materials provided with the distribution.

  3. Neither the name of the University of California, San Diego, nor 
  the names of its contributors may be used to endorse or promote 
  products derived from this software without specific prior 
  written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  
*)

open Cil
open Gc_stats
open Callg
open Scc_cg
open Fstructs
open Cilinfos
open Stdutil 
open Lvals
open Printf
open Pretty
open Scope
open Strutil

open Definitions
open Simple_definitions
open Modsummary
open Effect
open Code_gen
open Simple_effect_checks


module A = Alias
module Intra = IntraDataflow
module BS = Backed_summary
module SPTA2 = Symex

module FC = Filecache
module L = Logging
module I = Inspect
module P = Pervasives

(* Open simple effect modules *)
module SE = Simple_effect
module SD = Simple_definitions
module SEC = Simple_effect_construct


let split_path f = 
   (Filename.dirname f, Filename.basename f)
let mkpath  = Filename.concat 
exception Opt2some

(***************************************************)
(* Commandline handling                            *)

let dumpDir = ref ""
let configFile = ref "client.cfg"
let userName = ref "xyz"

(* Command-line argument parsing *)
let argSpecs = 
  [("-cg", Arg.Set_string cgDir, "call graph directory");
   ("-su", Arg.Set_string configFile, "name of config/summary bootstrap");
   ("-i", Arg.String 
      I.inspector#addInspect, "inspect state of function (given name)");
   ("-u", Arg.Set_string userName, "username to use");
   ("-dd", Arg.Set_string dumpDir, "dump code");
   ("-debug", Arg.Unit (fun _ -> enable_log:=true), 
     "print debug information");
   ("-ddebug", Arg.Unit (fun _ -> enable_log:=true; detailed_log:=true), 
     "print more verbose debug information");  
    ("-cl", Arg.Unit (fun _ ->count_locks:=true),"count locks");
    ("-sl", Arg.Unit (fun _ ->static_lockset:=true),"static lockset");
  ]

let anonArgFun (arg:string) : unit = ()
    
let usageMsg = getUsageString "-cg fname\n"


(***************************************************)
(* Debug - Printing                                *)

let printCallGraph cg = 
  log "Print call graph.\n";
  FMap.iter (
    fun (id,str) node ->
      log "\n%d. %s\nCallees:\n" id node.name;

      (List.iter (
        fun ct -> 
          match ct with
          | CDirect (_,(fid,s)) -> log "  Direct %d,%s\n" fid s
          | CIndirect (pp,fidl) ->
              (log "  Indirect (%s): " (pp2str pp);
              List.iter (fun (i,s) -> log "%d,%s " i s) fidl;
              log "\n")) node.ccallees
      );
      log "Caller(s): ";
      List.iter (fun (i,s) -> log "%d,%s " i s) node.ccallers;
      log "\n"
  ) cg

let printSCC sccCG = 
  log "Print SCCs.\n";
  Fstructs.IntMap.iter (
    fun i scc ->
      let nodes = scc.scc_nodes in
      log "\n%d: " i;
      FSet.iter (fun (id,name) -> log "(%d,%s) " id name) nodes;
      log "\n" 
  ) sccCG


  

(***************************************************)
(* Run                                             *)        
  

let txt = open_out "effect.out"

let logtxt format =  Printf.ksprintf
  (fun x ->Printf.fprintf txt "%s" x) format

let initSettings () =
  Cil.initCIL ();
  try
    Cilinfos.reloadRanges !cgDir;
    let settings = Config.initSettings !configFile in
    (*Request.init settings;*)
    DC.makeLCaches (!cgDir);
    Threads.initSettings settings;
    A.initSettings settings !cgDir;

    loadFunAlias (); (*local function*)    
    
    initCountLocks ();
    let cgFile = Dumpcalls.getCallsFile !cgDir in
    let cg = readCalls cgFile in

    let sccCG = Scc_cg.getSCCGraph cg in

    (*printSCC sccCG;*)

    let () = Backed_summary.init settings !cgDir cg sccCG in

    if !detailed_log then 
      ignore(
      log "\nMalloc read from alias.bin:\n";
      Hashtbl.iter (fun name (loc,_,_,_) ->
          log "[%s,%d,%d] -> %s\n" loc.file loc.line loc.byte name
        ) (getMalloc1 ())
    );
    SPTA2.init settings cg (sum :> Modsummaryi.absModSumm);
    cg
  with e ->
    Printf.printf "Exc. in initSettings: %s\n"
    (Printexc.to_string e) ; raise e


(* We don't have to keep in the hash info that is not going 
 * to be used later on. *)
let clearFInfoHashEntry vid =
  try 
    let fs = H.find simpleFInfoHash vid in
    (*fs.sEffect <- [];*)
    fs.loopSet <- IntSet.empty;
    fs.loopEffect <- IntMap.empty;
  with Not_found -> ()


    

let myDumpFile (f:Cil.file) = 
  log "Dumping file...\n";
  let oc = open_out "test.c" in 
  dumpFile defaultCilPrinter oc "test.c" f;
  close_out oc


(************************************************************)
let cur_instr_ind = ref 0
let cur_stmt = ref dummyStmt 


(* Traverse the call graph bottom up *)

let doBottomUp cg  (f : (int * string) -> callN -> unit) =
  let visited = ref Fstructs.IntSet.empty in 
  let worklist = Queue.create () in
  let addw x  = Queue.add x worklist in
  let nextw () = Queue.take worklist  in 
  let hasnextw () = not (Queue.is_empty worklist) in  
  let sccCG  = Scc_cg.getSCCGraph cg in
     
  let find_unvisited_callees scc = 
    let fld sccK (map: Fstructs.IntSet.t) = 
      let scc = Fstructs.IntMap.find sccK sccCG in
      try begin 
        (FSet.iter (fun (fkey,_) ->
          if not (Fstructs.IntSet.mem fkey !visited) then
            raise Not_found 
          ) scc.scc_nodes);
          map
      end with Not_found -> Fstructs.IntSet.add sccK map
      
    in Fstructs.IntSet.fold 
        fld scc.scc_callees Fstructs.IntSet.empty        
  in
  Fstructs.IntMap.iter    
  (fun sccK scc -> 
    if isLeaf scc then 
      begin
        Queue.add sccK worklist
        (*;printScc cg scc*)
    end
  ) sccCG;
  
  (* Stop the analysis if errors are found *)
  while hasnextw () && not (!found_errors) do
    let sccK = nextw () in
    try
      (*process strongly connected component*)
      let scc = Fstructs.IntMap.find sccK sccCG in        
      currSCC := Some scc;
      let uv = find_unvisited_callees scc in
      if Fstructs.IntSet.is_empty uv then
        begin
          (* process nodes of scc*)
          FSet.iter
          (fun skey ->
            (* ensure that each key is visited once *)
            let fkey = Summary_keys.fkey_of_sumKey skey in
            if not (Fstructs.IntSet.mem fkey !visited) then
              begin
                begin try
                  let n = FMap.find skey cg in
                  if not (!found_errors) then
                    f skey n
                  else
                    ()
                with
                | Not_found -> 
                    rs_impossible "doBottomUp/1: %s" 
                    (Summary_keys.string_of_sumKey skey)
                end;
                visited := Fstructs.IntSet.add fkey !visited 
              end
          ) scc.scc_nodes;
          (* add parent sccs to worklist*)
          Fstructs.IntSet.iter addw scc.scc_callers 
        end
      else begin
        Fstructs.IntSet.iter addw uv; (*add unfinished stuff*)
        addw sccK (* process scc once children are done*)
      end
    with 
    | Not_found -> 
        rs_impossible "doBottomUp/0" 
  done 


let main () = 
  try
    Arg.parse argSpecs anonArgFun usageMsg;
    (* Didn't know how to require the -cg file, etc., so check manually *)
    if (!cgDir = "") then
      begin
        Arg.usage argSpecs usageMsg;
        exit 1
      end
    else
      begin
        (* Get Callgraph structures *)
        let cg = initSettings () in 

        log "\n-------------------------------------\n";
        log "DEADLOCK ANALYSIS\n";
        log "-------------------------------------\n";

        let sym2 = new SPTA2.symexAnalysis in

        let string_of_fidnode fid fnode = 
          Printf.sprintf "%s(%s)" fnode.name (fid_to_string fid)
        in
        let setInspect fid fnode =
          if I.inspector#mem fnode.name then begin
            L.logStatusF "Trying to inspect %s\n"
              (string_of_fidnode fid fnode);
            (*sym1#setInspect true;*)
            sym2#setInspect true
          end else begin
            (*sym1#setInspect false;*)
            sym2#setInspect false
          end
        in

        (** Do bottom up *)
        doBottomUp cg
          (fun (fkey,fname) node -> 
              
            if node.defFile <> ""  && node.hasBody then begin
              setInspect (fkey,fname) node;
              L.flushStatus ();

              let firstFilePass = not (cilFileNameExists node.defFile) in
              (* get the AST of the file where the function is defined *)
              let ast = try
                cilFileGet node.defFile
                with Not_found ->
                  !DC.astFCache#getFile node.defFile                  
              in

              cur_ast := ast;

              if firstFilePass then
              begin
                (* This will be needed generally. *)
                Cfg.clearFileCFG ast;                
                Cfg.computeFileCFG ast;

                (* initiate the functionHash *)
                SD.createSFunctionHash ast;
              end;
              A.setCurrentFile ast;
              (sum#setFile) ast;

              (* Add the file for the next time. *)
              cilFileAdd ast;

              (* This computes the CFG of the specified function. *)
              match getCFG fkey ast with
              | Some (fn) when fn.svar.vstorage <> Extern ->
                begin

                  let fname = fn.svar.vname in
                  curFunc := fn;     (** Pretty printing *)
                  function_count := !function_count + 1;
                    
                  log "Analyzing function `%s' (decl.: %s) (vid:%d) \n"
                    fn.svar.vname (loc2strsmall fn.svar.vdecl) fn.svar.vid;

              (** Simple effect computation *)
                  let sfs = 
                    try Hashtbl.find SD.simpleFInfoHash fkey
                    with Not_found -> rs_impossible "functionNotInHash" in
                  
                  SE.simpleEffectComp fn sfs;


            (** Output the error/info messages *)
                  StringSet.iter (fun s -> info "%s" s) !info_set;
                  StringSet.iter (fun s -> err "%s" s) !error_set;
                  
                end
              | _ -> ()
            end 
          else
            L.logStatusF "Skipping (no body) %s in %s\n" 
              (string_of_fidnode (fkey,fname) node) node.defFile;

        );
        (**   end of bottom up *)
        log "\n\n%s: %d\n\n" (magenta "Total number of functions")
          !function_count;
        log "%s: %d\n\n" 
          (magenta "Total number of recursive functions with effect")
          !recursive_count;
        log "%s: %d\n\n" (magenta "Invalid argument substitution")
          !SEC.invalid_arg_c;
        log "%s: %d\n" (magenta "Invalid var")
          !SEC.invalid_var;
        log "%s: %d\n" (magenta "Invalid addrof")
          !SEC.invalid_addrof;
        log "%s: %d\n" (magenta "Invalid memval")
          !SEC.invalid_memvlal;
        log "%s: %d\n" (magenta "Invalid memlval")
          !SEC.invalid_memptr;
        log "%s: %d\n" (magenta "Invalid memptr")
          !SEC.invalid_expaddr;
        log "%s: %d\n" (magenta "Invalid expaddr")
          !SEC.invalid_startof;
        log "%s: %d\n" (magenta "Invalid expaddr")
          !SEC.invalid_align;
        
        aggregateCountLocks ();
  
        log "-------------------------------------\n";
        log "END OF DEADLOCK ANALYSIS\n";
        log "-------------------------------------\n\n"; 
    
        let list_stats l = 
          List.fold_left (
            fun (min,max,sum) elt ->
              if elt > max && elt < min then
                (elt,elt,sum+elt)
              else if elt > max then
                (min,elt,sum+elt)
              else if elt < min then
                (elt,max,sum+elt)
              else
                (min,max,sum+elt)
          ) (1000000,-1,0) l in

        let (min_eff, max_eff, avg_eff) = 
          let (min,max,sum) = list_stats !total_effect_size in
          let len = List.length !total_effect_size in
          if len > 0 then
            (min, max, (P.float sum)/.(P.float len))
          else
            (0,0,0.0)
        in


        log "%s: %d\n" (magenta "Minimum effect size")
          min_eff;
        log "%s: %d\n" (magenta "Maximim effect size")
          max_eff;
        log "%s: %f\n\n" (magenta "Average effect size")
          avg_eff;

        let (ls,sbsf,sbdf,u) = !total in
        logtxt "%d %d %d %d %f %d %d %d %d %d\n"
          !function_count !funWeffect_count min_eff max_eff avg_eff
          !recursive_count ls sbsf sbdf u;              

        (*printStatistics ();
        let ret = 
          if hasErrors () then 
            ( log "Compilation failed.\n"; -1 )
          else ( (* save instrumented sources *)                     
            let dump_path = mkpath !cgDir "gen" in
            Unix.mkdir dump_path 0o700;
            StringMap.iter (fun nm f ->
              doFinalize false f) !cilfiles; 
              log "Compilation OK\n"; 0) 
        in
        exit ret;*)        
      end
  with e -> 
    L.logStatus ("Exc. in Test Symstate: " ^ (Printexc.to_string e)); 
    printStatistics ();
    L.flushStatus ();
    raise e
;;
main () ;;
