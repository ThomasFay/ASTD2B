type bSet =
  Variable of string
| Constant of string
| EnumerateSet of string list;;

type predicateB =
  Equality of bSet * bSet
| BPred of string
| And of predicateB * predicateB
| Or of predicateB * predicateB
| In of bSet * bSet
| True
| False
| Implies of predicateB * predicateB
| Exists of string * predicateB;;

type substitutionB =
  Select of (predicateB * substitutionB) list
| Affectation of bSet * bSet
| Parallel of substitutionB list;;

type initialisation =
| AffectationInit of bSet * bSet
| AnyInit of string * predicateB * bSet * bSet

type operation = {
  nameOf : string;
  parameter : string list;
  preOf : predicateB;
  postOf : substitutionB;
}


type machineB = {
  machine : string;
  sets : (string * (string list)) list;
  variables : string list;
  invariants : (string * (string list)) list;
  init : initialisation list;
  operations : operation list;
}

val predMap : (bSet -> bSet) -> predicateB -> predicateB

val print_machine : machineB -> string


