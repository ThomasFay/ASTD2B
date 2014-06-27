type bSet =
  Variable of string
| EnumerateSet of string list;;

type predicateB =
  Equality of bSet * bSet
| BPred of string
| And of predicateB * predicateB
| Or of predicateB * predicateB
| In of bSet * bSet
| True

| Implies of predicateB * predicateB;;

type substitutionB =
  Select of (predicateB * substitutionB) list
| Affectation of bSet * bSet
| Parallel of substitutionB list;;

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
  initialisation : (string * (string list) * string) list;
  operations : operation list;
}


val print_machine : machineB -> string


