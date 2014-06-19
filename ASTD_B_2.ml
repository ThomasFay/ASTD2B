(*Définition du type expression :
-Soit c'est un ET logique entre 2 expression
-Soit c'est une comparaison entre une variable (string1), ses paramètres (string list) et la valeur à comparer (string2)*)

type expression =
|And of (expression * expression)
|Or of (expression * expression)
|Guard of string
|ComparisonVar of (string * string list * string)
|ComparisonVal of (string * string)
|ForAll of string list * expression * expression
|Exists of string list * expression
|In of string * string
|None;;

type relation =
|Name of string
|Lambda of string * expression * string
|OverLoad of relation * relation;;

type affectation =
|VarAffect of string * string list * string
|RelAffect of relation * relation;;

(*Définition de la substitution :
-Soit c'est une affectation : on affecte à la variable (string1), paramétrée (string list) une valeur (string2)
-Soit c'est un Select dont la condition est l'expression et dont le then est une nouvelle substitution
*)

type substitution =
|AffectationSub of affectation list
|Select of (expression * substitution) list
|Parallel of substitution * substitution;;

(*Définition d'une opération qui a
-un nom (string)
-des paramètres (string list)
-une précondition (expression)
-une substitution (substitution)*)

type operation = string * (string list) * expression * substitution;;

(*La machine B est définie selon les paramètres d'une machine B classique. Les noms des paramètres sont transparents*)

type machineB = {
  machine : string;
  sets : (string * (string list)) list;
  variables : string list;
  invariants : (string * (string list) * string) list;
  initialisation : (string * (string list) * string) list;
  operations : operation list;
}

(*Cette opération parmet de transfomer en string l'écriture de la clause variable*)

let rec printVariables variables = match variables with
  |[] -> ""
  |[t] -> "   " ^ t
  |h::t -> "   " ^ h ^ " ,\n" ^ (printVariables t);;

(*Permet d'imprimer les différentes valeurs d'un ensemble énuméré*)

let rec printValues values = match values with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ "," ^ printValues t;;

(*Permet d'imprimer la clause SETS*)

let rec printSets sets = match sets with
  |[] -> ""
  |[(name,values)] -> (match values with
    |[] -> "   " ^ name ^ "\n"
    |_::_ ->  "   " ^ name ^ " = {" ^ printValues values ^ "}\n")
  |(name,values)::t -> (match values with
    |[] -> "   " ^ name ^ ";\n" ^ printSets t
    |_::_ -> "   " ^ name ^ " = {" ^ printValues values ^ "};\n" ^ printSets t);;

(*Permet d'afficher le type d'une variable définie comme une fonction dans le cas où on doit utiliser de variables paramétrées*)

let rec printTypesFonction types = match types with
  |[] -> ""
  |h::t -> h ^ " --> " ^ printTypesFonction t;;

(*Permet d'afficher la clause invariant*)

let rec printInvariants invariants = match invariants with
  |[] -> ""
  |[var,typesParam,typ] -> "   " ^ var ^ " : " ^ printTypesFonction typesParam ^ typ ^ "\n"
  |(var,typesParam,typ)::t -> "   " ^ var ^ " : " ^ printTypesFonction typesParam ^ typ ^ " &\n" ^ printInvariants t;;

(*Permet d'afficher la partie droite des affectations dans la clause initialisation dans le cas d'une variable paramétrée (les cas où l'initialisation est state = T * {s1})*)

let rec printTypesStar types = match types with
  |[] -> ""
  |h::t -> h ^ " * " ^ printTypesStar t;;

(*Affiche la clause d'initialisation*)

let rec printInitialisation initialisation = match initialisation with
  |[] -> ""
  |[var,typesParam,typ] -> (match typesParam with
    |[] ->  "   " ^ var ^ " := " ^ typ ^ "\n"
    |h::t ->  "   " ^ var ^ " := " ^ printTypesStar typesParam ^ "{" ^ typ ^ "}\n")
  |(var,typesParam,typ)::t -> (match typesParam with
    |[] -> "   " ^ var ^ " := " ^ typ ^ " ||\n" ^ printInitialisation t
    |h::tail -> "   " ^ var ^ " := " ^ printTypesStar typesParam ^ "{" ^ typ ^ "}" ^ " ||\n" ^ printInitialisation t);;

(*Affiche n tabulation (3 espaces). Utile pour l'indentation*)

let rec printTab n = match n with
  |0 -> ""
  |n -> "   " ^ printTab (n-1);;

(*Affiche les paramètres d'une fonction etc... sous la forme param1, param2, ... ,ParamN*)

let rec printParams param = match param with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ "," ^ printParams t;;

(*Permet d'imprimer le type Expression*)

let rec printExpr n expr = match expr with
  |And (p1,p2) -> "(" ^ printExpr n p1 ^ " &\n" ^  printExpr n p2 ^ ")"
  |Or (p1,p2) ->  "(" ^ printExpr n p1 ^  " or\n"  ^ printExpr n p2 ^ ")"
  |Guard g -> printTab n ^ g
  |ComparisonVar (var,params,value) -> (match params with
    |[] -> printTab n ^ var ^ " = " ^ value
    |h::t -> printTab n ^ var ^ "(" ^ printParams params ^ ") = " ^ value)
  |ComparisonVal (value1,value2) -> printTab n ^ value1 ^ " = " ^ value2
  |Exists (vars,expression) -> printTab n ^ "#(" ^ printParams vars ^ ").\n(" ^ printExpr n expression ^ ")"
  |ForAll (vars,expr1,expr2) -> printTab n ^ "!(" ^ printParams vars ^ ").\n" ^ printTab n ^ "(" ^ printExpr n expr1^ " =>\n" ^ printExpr n expr2 ^ ")"
  |In (var,set) -> var ^ " : " ^ set
  |None -> ""

let rec printRelation rel = match rel with
  |Name s -> s
  |Lambda (var,expr,newVal) ->"%" ^ var ^ ".(\n" ^ printExpr 0 expr ^ " | " ^ newVal ^ ")"
  |OverLoad (rel1,rel2) -> printRelation rel1 ^ " <+ " ^ printRelation rel2;;

(*Affiche la précondition d'une fonction*)

let printPre pre = printExpr 2 pre;;

let rec printAffectation affect n = match affect with
  |VarAffect (var,param,value) -> (match param with
    |[] -> printTab n ^ var ^ " := " ^ value
    |_ -> printTab n ^ var ^ "(" ^ printParams param ^ ") := " ^ value)
  |RelAffect (rel1,rel2) -> printTab n ^ printRelation rel1 ^ " := " ^ printRelation rel2;;

(*Permet d'afficher une affectation sous la forme v1 := s1 ou v1(tt):=s1*)

let rec printAffectationList n l = match l with
  |[] -> ""
  |[t] -> printAffectation t n
  |head::tail -> printAffectation head n ^ " ||\n" ^ printAffectationList n tail;;

let rec printSelect n clause = match clause with
  |[] -> ""
  |(cond,action)::tail -> printTab n ^ "WHEN\n" ^ printExpr (n+1) cond ^ "\n" ^ printTab n ^ "THEN\n" ^ printThen (n+1) action ^ printSelect n tail
and printThen n thenn = match thenn with
  |AffectationSub l -> printAffectationList n l
  |Select ((cond,action)::tail) -> printTab n ^ "SELECT\n" ^ printExpr (n+1) cond ^ "\n" ^ printTab n ^ "THEN\n" ^ printThen (n+1) action ^ "\n" ^ printSelect n tail ^ printTab n ^ "END\n"
  |Parallel (sub1,sub2) -> printThen n sub1 ^ " ||\n" ^ printThen n sub2;;


(*Affiche une opération simple*)

let rec printSingleOperation ope = match ope with
  |(name,param,pre,thenn) ->
    begin
      match param with
      |[] -> "   " ^ name ^ " =\n   PRE\n" ^ printPre pre ^ "\n   THEN\n" ^ printThen 2 thenn ^ "   END"
      |h::t -> "   " ^ name ^ "("^ printParams param ^") =\n   PRE\n" ^ printPre pre ^ "\n   THEN\n" ^ printThen 2 thenn ^ "\n   END"
    end;;

(*Affiche la liste des opérations d'une machine*)

let rec printOperations ope = match ope with
  |[] -> ""
  |[h] -> printSingleOperation h
  |h::t -> printSingleOperation h ^ ";\n\n" ^ printOperations t;;

(*Affiche une machine B*)

let printMachineB m =
  begin
    "MACHINE\n   " ^ m.machine ^ "\nSETS\n" ^
      printSets m.sets ^ "VARIABLES\n" ^ printVariables m.variables ^
      "\nINVARIANT\n"^ printInvariants m.invariants ^ "INITIALISATION\n" ^ printInitialisation m.initialisation ^
      "OPERATIONS\n" ^ printOperations m.operations ^ "\nEND\n"
  end;;
