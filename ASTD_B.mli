type bSet =
  Variable of string
| Constant of string
| Function of string * (string list)
| EnumerateSet of string list
| CartesianP of string list

type predicateB =
  Equality of bSet * bSet
| BPred of string
| And of predicateB * predicateB
| Or of predicateB * predicateB
| In of bSet * bSet
| True
| False
| Implies of predicateB * predicateB
| Exists of string * predicateB
| Forall of string * predicateB * predicateB

type substitutionB =
  Select of (predicateB * substitutionB) list
| Affectation of bSet * bSet
| Parallel of substitutionB list
| AffectationLambda of string * (string * predicateB * string) list
| Call of string * (string list)
| Any of string * predicateB * substitutionB

type initialisation =
| AffectationInit of bSet * bSet
| AnyInit of string * predicateB * bSet * bSet

type operation = {
  nameOf : string;
  parameter : (string*string) list;
  preOf : predicateB;
  postOf : substitutionB;
}

type typeOfMachine =
  |Machine of string
  |Refinement of string * string

type seesMachine =
  |SeenMachine of string
  |NoSeenMachine

type includesMachine =
  |IncludedMachine of string
  |NoIncludedMachine

type inv = {
  typage :  (string * (string list)) list;
  invariantsPreuve : string;
}

type machineB = {
  machine : typeOfMachine;
  sees : seesMachine;
  includes : includesMachine;
  sets : (string * (string list)) list;
  variables : string list;
  assertions : string;
  invariants : inv;
  init : initialisation list;
  operations : operation list;
}

val predMap : (bSet -> bSet) -> predicateB -> predicateB

val print_machine : machineB -> string

val strOfValue : bSet -> string

val simplifyPred : predicateB -> predicateB

val simplifySub : substitutionB -> substitutionB
