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

let rec indent n = match n with
  |0 -> ""
  |n -> "   " ^ indent (n-1);;

let rec printValList valList = match valList with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ "," ^ printValList t;;

let rec printSets sets = match sets with
  |[] -> ""
  |[(name,valList)] -> indent 1 ^ name ^ " = {" ^ printValList valList ^ "}\n"
  |(name,valList)::t -> indent 1 ^ name ^ " = {" ^ printValList valList ^ "};\n" ^ printSets t;;

let rec printStringList li = match li with
  |[] -> ""
  |h::t -> h ^ printStringList t;;


let rec printParam parameter = match parameter with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ "," ^ printParam t;;

let rec printBSet bSet = match bSet with
  |Variable s -> s
  |Constant s -> s
  |EnumerateSet l -> "{" ^ printValList l ^ "}";;

let rec printPredicateB pred n = match pred with
  |Equality (set1,set2) -> indent n ^ printBSet set1 ^ " = " ^ printBSet set2
  |And (expr1,expr2) -> "(" ^ (printPredicateB expr1 n) ^ " & \n" ^ (printPredicateB expr2 n) ^ ")"
  |Or (expr1,expr2) ->  "(" ^ (printPredicateB expr1 n) ^ " or \n" ^ (printPredicateB expr2 n) ^ ")"
  |In (set1,set2) -> indent n ^ printBSet set1 ^ " : " ^ printBSet set2
  |True -> indent n ^ "True"
  |BPred str -> indent n ^ str
  |Implies (pred1,pred2) -> "(" ^ printPredicateB pred1 n ^ " =>\n" ^ printPredicateB pred2 (n+1) ^ ")";;


  

let rec printSubstitution sub n= match sub with
  |Affectation (bSet1,bSet2) -> indent n ^ printBSet bSet1 ^ " := " ^ printBSet bSet2
  |Select [] -> failwith "it shouldn't exist"
  |Select [(pred,sub)] -> indent n ^ "SELECT\n" ^ printPredicateB pred (n+1) ^ "\n" ^ indent n ^ "THEN\n" ^ printSubstitution sub (n+1) ^ indent n ^ "END\n"
  |Select ((pred,sub)::t) -> indent n ^ "SELECT\n" ^ printPredicateB pred (n+1) ^ "\n" ^ indent n ^ "THEN\n" ^ printSubstitution sub (n+1) ^ printStringList (List.rev_map (print1SelectCase (n+1)) t) ^ indent n ^ "END\n"
  |Parallel [] -> failwith "it shouldn't appenned"
  |Parallel [t] -> printSubstitution t n ^ "\n"
  |Parallel (h::t) -> printSubstitution h n ^ " ||\n" ^ printSubstitution (Parallel t) n
and print1SelectCase n ca = let pred,sub = ca
			  in indent n ^ "WHEN\n" ^  (printPredicateB pred (n+1)) ^ "\n" ^  indent n ^ "THEN\n" ^ printSubstitution sub (n+1) ^indent n^ "\n";;

let printOperation ope = indent 1 ^ ope.nameOf ^ begin
  let param = printParam ope.parameter in
  if param = ""
  then ""
  else "(" ^ param ^ ")"
end ^ " = \n" ^ indent 1 ^  "PRE\n" ^ (printPredicateB ope.preOf 2) ^ "\n" ^ indent 1 ^ "THEN\n" ^ (printSubstitution ope.postOf 2) ^ indent 1 ^ "END";;




let rec printVariables var = match var with
  |[] -> ""
  |[t] -> indent 1 ^ t ^ "\n"
  |h::t -> indent 1 ^ h ^ ",\n" ^ printVariables t;;

let rec printTypage typage = match typage with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ " -->";;

let rec printInv inv = match inv with
  |[] -> ""
  |[(var,typage)] -> indent 1 ^ var ^ " : " ^ printTypage typage ^ "\n"
  |(var,typage)::t -> indent 1 ^ var ^ " : " ^ printTypage typage ^ " &\n" ^ printInv t;;

let rec printInitTypage typage value = match typage with
  |[] -> "{" ^ value ^ "}"
  |h::t -> h ^ "* {" ^ printInitTypage t value ^ "}"

let rec printInit init = match init with
  |[] -> ""
  |[(var,typage,value)] -> if typage = [] 
    then indent 1 ^ var ^ " := " ^ value
    else indent 1 ^ var ^ " := " ^ printInitTypage typage value
  |(var,typage,value)::t ->  let varPrint = if typage = [] 
    then indent 1 ^ var ^ " := " ^ value
    else indent 1 ^ var ^ " := " ^ printInitTypage typage value
		       in varPrint ^ " ||\n" ^ printInit t

let rec printOperationList li = match li with
  |[] -> ""
  |[h] -> printOperation h
  |h::t -> printOperation h ^ ";\n\n" ^ printOperationList t;;

let rec print_machine ma = begin
  "MACHINE\n" ^ indent 1 ^ ma.machine ^ "\nSETS\n" ^ printSets ma.sets ^ "VARIABLES\n" ^ printVariables ma.variables ^ "INVARIANT\n" ^ printInv ma.invariants ^ "INITIALISATION\n" ^ printInit ma.initialisation ^ "\nOPERATIONS\n" ^ (printOperationList ma.operations) ^ "\nEND"
end;;

