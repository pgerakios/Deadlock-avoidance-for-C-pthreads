open Cil
open Definitions
open Simple_definitions
open Simple_effect_tools
open Simple_effect_construct

module L = List
module DF = Dataflow
module H = Hashtbl

(*********************************************************
 *                Effect state
 *********************************************************)

(* per program-point state *)
type effState = {
  inEff: simple_effect IntMap.t;
  loopInEff: simple_effect IntMap.t;  
  ownEff: simple_effect;
  outEff: simple_effect;
  mutable visited: IntSet.t;
  mutable stid: int;
  mutable stmt: stmt;
}

let bottomEffect = []

let packState inf loopIn ownf outf vis id st= {
    inEff = inf;
    loopInEff = loopIn;
    ownEff = ownf;
    outEff = outf;
    visited = vis;
    stid = id;
    stmt = st;
  }

(* Check if this is a looping node. *)
let loopingNode st = 
  IntSet.mem st.stid (!cur_sfstruct).loopSet

let fStatesEqual s1 s2 =
  (compare_seffects s1.outEff s2.outEff) &&
  (IntMap.equal compare_seffects s1.inEff s2.inEff) &&
  (if loopingNode s1 then
    (IntMap.equal compare_seffects s1.loopInEff s2.loopInEff)
  else true )



(* Checks if visiting oldSt means we are looping *)
let looping oldSt newSt = 
  IntSet.mem oldSt.stid newSt.visited

(* Update the incomming effect of an predecessor state 
 * in the current state*)
let registerStinMap oldMap newSt = 
  IntMap.add newSt.stid newSt.outEff oldMap

let registerInEff oldSt newSt =
    registerStinMap oldSt.inEff newSt


let rec remaining_new oldF newF = 
  match oldF, newF with
  | [],_ -> newF
  | _,[] -> []
  | h1::t1,h2::t2 -> 
      if compare_slockops h1 h2 then
        remaining_new t1 t2
      else
        begin
          match h1,h2 with
          | SJoin el, _ ->
              let olds = L.map (fun e -> fixInline (e@t1)) el in
              let (is_assoc,remaining,olds') = associated_with newF olds in
              remaining             
          (* we cannot do anything better for this case *)
          | _ -> let _ = log "Cannot do anything better.\n" in newF          
        end


(* This is the combination used for joining effects. *) 
(* newSt is the incomming state
 * oldSt is the state of the current statement *)
let fCombineStates oldSt newSt lh =
  let newVis = IntSet.add oldSt.stid newSt.visited in
  if looping oldSt newSt then begin
  (* Visiting oldSt coming from newSt creates a loop. *)
    let remaining = remaining_new oldSt.outEff newSt.outEff in
    (* We had removed the own effect from the loop effect -
     * this must be brought back in. *)
    let lf = oldSt.ownEff @ remaining in
    (* The inF is not altered by the looping effect - everything we need 
     * from the loop will be placed in to [BpLoop]. *)
    let inF = oldSt.inEff in
    let loopF = IntMap.add newSt.stid lf oldSt.loopInEff in
    let ownF = oldSt.ownEff in
    let inFlist = fmap2flist inF in
    let outF = fixInline ((cp_effect_list_2 inFlist) @ ownF) in
    (*if !curFunc.svar.vid = 1014 && oldSt.stid = 1065  && newSt.stid = 1036 then 
      (log "Loop Eff ( %d ) Own:\n" oldSt.stid;
      print_seffect ownF;
      IntMap.iter (fun i e -> if i = 1036 then (log " %d" i ;print_seffect e))
      loopF);*)
    H.replace lh oldSt.stid loopF;
    packState inF loopF ownF outF newVis oldSt.stid oldSt.stmt
  end
  else begin
    (*log "In statement: %d in from %d\n" oldSt.stid newSt.stid;*)
    (*log "Old instate:";
    IntMap.iter (fun i e -> log "From %d:" i ;(print_effect e)) oldSt.inEff;*)
    let inF = registerInEff oldSt newSt in
    (*log "New instate:";*)
    (*IntMap.iter (fun i e -> log "From %d:" i ;(print_seffect e)) inF;*)
    let inFlist = fmap2flist inF in
    let loopF = oldSt.loopInEff in
    let ownF = oldSt.ownEff in
    let outF = fixInline ((cp_effect_list_2 inFlist) @ ownF) in
    (*log "   outeff:\n";
    print_effect outF;*)
    packState inF loopF ownF outF newVis oldSt.stid oldSt.stmt
  end


let compStmtEff (s:stmt) = 
  match s.skind with
  | Instr il -> 
      let doInstr i = 
        begin
          cur_instr_ind := !cur_instr_ind +1;
          compInstrEffect i
        end
      in
      begin
        cur_instr_ind := 0;
        L.concat (L.map doInstr il)
      end
  | _ -> []

(** The function being analyzed *)
let curFunID = ref (-1)


(*****************************************************
 *
 *  Dataflow transfer functions for loop computation
 *
 *****************************************************)

(* newSt is the incomming state
 * oldSt is the state of the current statement *)
let loopCombineStates oldSt newSt =
  let newVis = IntSet.add oldSt.stid newSt.visited in
  if looping oldSt newSt then begin
    (!cur_sfstruct).loopSet <- IntSet.add oldSt.stid (!cur_sfstruct).loopSet
  end;
  packState IntMap.empty IntMap.empty [] [] newVis oldSt.stid oldSt.stmt

module LoopTrans = struct
  let debug = ref false
  let name = "loop df"
  type t = effState
  let copy (d:t) = d  
  let stmtStartData : t Inthash.t = Inthash.create 37
  let pretty () (d: t) = Pretty.nil

  let initStmtStartData () =
    Inthash.clear stmtStartData;
    L.iter (
      fun s -> 
        let initSet = IntSet.add s.sid IntSet.empty in
        let initState = packState IntMap.empty IntMap.empty [] [] initSet s.sid s in
        Inthash.add stmtStartData s.sid initState
    ) !curFunc.sallstmts

  let computeFirstPredecessor (s: stmt) (newD: t) : t = newD      

  let combinePredecessors (s: stmt) ~(old: t) (newD: t) : t option =
    let combSt = loopCombineStates old newD in
    if IntSet.mem old.stid newD.visited then None
    else Some combSt

  let doInstr (i: instr) (inSt: t) = DF.Default
  let doGuard (gexp: Cil.exp) (d: t) = DF.GDefault
  let doStmt (s: stmt) (d: t) = DF.SDefault
  let filterStmt _ = true
end (* End LoopTrans *)


(*****************************************************
 *
 *  Dataflow transfer functions for effect computation
 *
 *****************************************************)

module EffectTrans = struct
  let debug = ref false
  let name = "effect df"
  type t = effState
  let copy (d:t) = d  

  let loopHash : (int,simple_effect IntMap.t) H.t = H.create 10

  let stmtStartData : t Inthash.t = Inthash.create 37
  (* Insert here the own effects of each statement *)

  let pretty () (d: t) = Pretty.nil

  let uneededDF = ref true

  let initStmtStartData () =
    Inthash.clear stmtStartData;
    H.clear loopHash;
    (*log "Initializing df for %d nodes\n" (L.length !curFunc.sallstmts);*)
    uneededDF := true;
    (* Compute own effects for every statement *)
    L.iter (
      fun s -> 
        call_stmt := s;
        loopHashRef := loopHash;
        let instrEff = compStmtEff s in
        if instrEff <> [] then 
          uneededDF := false;
        (* Check if this is a loop node - if yes put a placeholder *)
        let initEff = 
          if IntSet.mem s.sid (!cur_sfstruct).loopSet then
            (SBpLoop s.sid) :: instrEff
          else
            instrEff
        in          
        let initSet = IntSet.add s.sid IntSet.empty in
        let initState = packState IntMap.empty IntMap.empty initEff 
                        initEff initSet s.sid s in
        Inthash.add stmtStartData s.sid initState
    ) !curFunc.sallstmts;
    if !uneededDF then
      L.iter (fun s -> 
        let initSet = IntSet.add s.sid IntSet.empty in
        let initState = packState IntMap.empty IntMap.empty []
          [] initSet s.sid s in
        Inthash.add stmtStartData s.sid initState
      ) !curFunc.sallstmts



  let computeFirstPredecessor (s: stmt) (newD: t) : t =
    newD
      
  let combinePredecessors (s: stmt) ~(old: t) (newD: t) : t option =
    (*log "In %d: effsize %d\n" s.sid (effect_size old.outEff);*) 
    let combSt = fCombineStates old newD loopHash in
    if fStatesEqual combSt old then None
    else Some combSt

  let doInstr (i: instr) (inSt: t) = DF.Default
  let doGuard (gexp: Cil.exp) (d: t) = DF.GDefault
  let doStmt (s: stmt) (d: t) = DF.SDefault
  let filterStmt _ = true

end (* End EffectTrans *)



module EffectDF = DF.ForwardsDataFlow(EffectTrans)
module LoopDF = DF.ForwardsDataFlow(LoopTrans)

(** Prepare analysis *)
let initializeDF (funID: int) (func:fundec) : unit =
  curFunc := func;
  curFunID := funID;
  let allst = (!curFunc).sallstmts in
  LoopTrans.initStmtStartData ();
  LoopDF.clearPPData ();
  (* After the loops have been computed the fstruct.loopSet is updated *)  
  LoopDF.compute allst;

  EffectTrans.initStmtStartData ();
  EffectDF.clearPPData ()
  

(** The actual computation of the effect *)  
let computeFunEffect () = 
  let allst = (!curFunc).sallstmts in
  EffectDF.compute allst 

(** Return the output state for summarization *)
let getOutState () : effState  =
  let funOutMap =
    L.fold_left  (
      fun curMap s ->
        (* Consider Return statements *)
        match (s.skind, s.succs) with
        | Return _, _ ->
            let pp = getStmtPP s in
            let st = EffectDF.getDataBefore pp in
            (*let _ = log "Return at: %s.\n" (loc2strsmall (get_stmtLoc
             * s.skind)) in*)
            registerStinMap curMap st
            (*st.outEff :: curState*)
(*
 (**)
        | _ , [] ->
            let pp = getStmtPP s in
            let st = EffectDF.getDataBefore pp in
            (*let _ = log "No Succ at: %s: %s\n" (loc2strsmall (get_stmtLoc
            s.skind)) (stmt2str s) in*)
            registerStinMap curMap st
            (*st.outEff :: curState*)
*)
        | _, _ -> 
          curMap
    ) IntMap.empty !curFunc.sallstmts
  in
  (* Delaying sgarbage to collect the assign summary/checks first *)
  let funOutList = fmap2flist funOutMap in
  (*IntMap.iter (
    fun i e -> log "###\n"; print_effect e) funOutMap;*)
  packState funOutMap IntMap.empty []  (cp_effect_list funOutList) IntSet.empty 0
    dummyStmt
   
  
