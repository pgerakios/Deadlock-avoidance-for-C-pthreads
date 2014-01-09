
val nameByte : int -> string
val nameFile : string -> string  
val resolveFP : Cil.exp -> string list
val addAlias : Cil.location -> string list -> unit
val addCgAlias : Cil.prog_point -> string list -> unit
val isAllocVar : string -> bool
val findMalloc : Cil.exp -> Cil.varinfo option
val feature : Cil.featureDescr
val unknownMallocType : Cil.typ
val pickType : Cil.typ -> Cil.exp list -> Cil.typ
