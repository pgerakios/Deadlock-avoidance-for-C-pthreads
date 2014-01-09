open Symex_base
open Symex_types
open IntraDataflow

include SYMEX

val modSumms : (Modsummaryi.modSum) ref

type symLatt = (symState, SS.sumval) stateLattice

val fullLattice : symLatt

val sumIsFinal : Summary_keys.sumKey -> bool 
  (* shouldn't this depend on the sumType? *)

val substLval : Cil.exp list -> Lv.aLval -> Lv.aLval
val mySubstExp : Cil.exp list -> Lv.aExp -> Lv.aExp   
val mySubstLval : Cil.exp list -> Lv.aLval -> Lv.aExp


class symSummarizer : symLatt -> (SS.data) -> [symState, SS.sumval] summarizer

class symTransFunc : (symState, SS.sumval) stateLattice -> 
  object
  inherit [symState] transFunc
  inherit [symState] inspectorGadget

  method private isFirstStmt : Cil.prog_point -> bool

  method private havocTarget : symState -> (symAddr * Cil.offset) -> symState

end

val printStatePP : Cil.prog_point -> unit  

val getAliasesAtExp : Cil.prog_point -> Lvals.aExp -> (bool * (Lvals.aExp list))
val getAliasesAt : Cil.prog_point -> Lvals.aLval -> (bool * (Lvals.aExp list))
val derefLvalAt : Cil.prog_point -> Cil.lval -> (bool * (Lvals.aLval list))
val getAliasesAtExit : Cil.fundec -> Lvals.aExp -> (bool * (Lvals.aExp list))
