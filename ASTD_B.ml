type bSet =
    Variable of string
   | QVar of string
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
  | Forall of string * predicateB * predicateB;;

type substitutionB =
    Select of (predicateB * substitutionB) list
  | Affectation of bSet * bSet
  | Parallel of substitutionB list
  | AffectationLambda of string list * (string * predicateB * string) list
  | CallB of string * (string list)
  | Any of string * predicateB * substitutionB

type initialisation =
  | AffectationInit of bSet * bSet
  | AnyInit of string * predicateB * bSet * bSet

type operation = {
  nameOf : string;
  parameter : (string * string) list;
  preOf : predicateB;
  postOf : substitutionB;
}

type typeOfMachine =
  | Machine of string
  | Refinement of string * string

type seesMachine =
  |SeenMachine of string
  |NoSeenMachine

type includesMachine =
  |IncludedMachine of string
  |NoIncludedMachine

type inv = {
  typage : (string * (string list)) list;
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

let rec predMap func pred = match pred with
  |Equality (bSet1,bSet2) -> Equality(func bSet1, func bSet2)
  |BPred str -> BPred str
  |And (pred1,pred2) -> And(predMap func pred1,predMap func pred2)
  |Or (pred1,pred2) -> Or(predMap func pred1,predMap func pred2)
  |In (bSet1,bSet2) -> In (func bSet1, func bSet2)
  |True -> True
  |False -> False
  |Implies (pred1,pred2) -> Implies (predMap func pred1,predMap func pred2)
  |Forall (var,pred1,pred2) -> Forall (var,(predMap func pred1),(predMap func pred2))
  |Exists (str,pred1) -> Exists (str,predMap func pred1)

let rec simplifyPred pred = match pred with
  |And (pred1,pred2) ->
    let sPred1 = simplifyPred pred1 in
    begin
      match sPred1 with
      |False -> False
      |True -> simplifyPred pred2
      |_ -> let sPred2 = simplifyPred pred2 in
	    begin
	      match sPred2 with
	      |False -> False
	      |True -> sPred1
	      |_ -> And (sPred1,sPred2)
	    end
    end
  |Or(pred1,pred2) ->
    let sPred1 = simplifyPred pred1 in
    begin
      match sPred1 with
      |False -> simplifyPred pred2
      |True -> True
      |_ -> let sPred2 = simplifyPred pred2 in
	    begin
	      match sPred2 with
	      |False -> sPred1
	      |True -> True
	      |_ -> Or (sPred1,sPred2)
	    end
    end
  |_ -> pred

let rec simplifySub sub = match sub with
  |Select li -> Select (simplifySelectCase li)
  |Parallel li -> Parallel (List.rev_map (simplifySub) li)
  |_ -> sub
and simplifySelectCase li = match li with
  |[] -> []
  |(pred,sub)::t -> let sPred = simplifyPred pred in
		    begin
		      match sPred with
		      |False -> simplifySelectCase t
		      |_ -> (pred,sub)::(simplifySelectCase t)
		    end
		      


let rec indent n = match n with
  |0 -> ""
  |n -> " " ^ indent (n-1);;

let rec printValList valList = match valList with
  |[] -> ""
  |[t] -> t
  |h::t -> h ^ "," ^ printValList t;;

let rec printSets sets = match sets with
  |[] -> ""
  |[(name,valList)] -> 
    begin
      match valList with
      |[] -> indent 3 ^ name ^"\n"
      |t::q -> indent 3 ^ name ^ " = {" ^ printValList valList ^ "}\n"
    end
  |(name,valList)::t ->
    begin
      match valList with
      |[] -> indent 3 ^ name ^ ";\n" ^ printSets t
      |h::q -> indent 3 ^ name ^ " = {" ^ printValList valList ^ "};\n" ^ printSets t
    end

let rec printStringList li = match li with
  |[] -> ""
  |h::t -> h ^ printStringList t;;

let strOfValue bSet = match bSet with
  |Variable str -> str
  |Constant str -> str
  |_ -> failwith "No Str Of Val";;

let rec printParam parameter = match parameter with
  |[] -> ""
  |[param,typ] -> param
  |(param,typ)::t -> param ^ "," ^ printParam t;;

let printCart h ca = h ^ " * {" ^ ca

let closeBracket h ca = h ^ "}"
					 
let rec printParamWithoutType parameter = match parameter with
  |[] -> ""
  |[param] -> "(" ^ param ^ ")"
  |(param)::t -> "(" ^ param ^ ")" ^ printParamWithoutType t;;

let rec printBSet bSet = match bSet with
  |Variable s -> s
  |QVar s -> s
  |Constant s -> s
  |Function (var,paramList)  -> var ^ printParamWithoutType paramList
  |EnumerateSet l -> "{" ^ printValList l ^ "}"
  |CartesianP (h::t) -> List.fold_left printCart h t ^ (List.fold_left closeBracket "" t)
  |CartesianP [] -> failwith "Bad Cartesian Product"
				       
let rec printPredicateB_aux pred n left = match pred with
  |Equality (set1,set2) ->
    (if left
     then indent 0
     else indent n) ^ printBSet set1 ^ " = " ^ printBSet set2
  |And (expr1,expr2) ->
    (if left
     then indent 0
     else indent n) ^ "(" ^ (printPredicateB_aux expr1 (n+1) true) ^
      " & \n" ^ (printPredicateB_aux expr2 (n+1) false) ^ ")"
  |Or (expr1,expr2) ->
    (if left
     then indent 0
     else indent n) ^
      "(" ^ (printPredicateB_aux expr1 (n+1) true) ^
	" or \n" ^ (printPredicateB_aux expr2 (n+1) false) ^ ")"
  |In (set1,set2) ->
    (if left
     then indent 0
     else indent n) ^ printBSet set1 ^ " : " ^ printBSet set2
  |True ->
    (if left
     then indent 0
     else indent n) ^ "True"
  |BPred str ->
    (if left
     then indent 0
     else indent n) ^ str
  |Implies (pred1,pred2) ->
    (if left
     then indent 0
     else indent n) ^ "(" ^ printPredicateB_aux pred1 n true ^
      " =>\n" ^ printPredicateB_aux pred2 (n+3) false ^ ")"
  |Exists (variable,pred) ->
    indent n ^ "#" ^ variable ^ ".(" ^ printPredicateB_aux pred (n+3) true ^ ")"
  |False -> (if left then indent 0 else indent n) ^ "False"
  |Forall (variable,pred1,pred2) ->
    (if left
     then indent 0
     else indent n) ^ "!" ^ variable ^
      ".(" ^ printPredicateB_aux pred1 (n+3) true ^
	" =>\n" ^ printPredicateB_aux pred2 (n+6) false ^ ")"

let printPredicateB pred n = printPredicateB_aux pred n false;;
  
let rec printLambdaOvl n func ovl = let (var,pred,value) = ovl in
				    func ^ "\n" ^ indent n ^ "<+ %" ^ var ^ ".(\n" ^ printPredicateB pred n ^ " | " ^ value ^ ")"

let rec printAffLambda varList = match varList with
  |[] -> failwith "Bad Lambda Affectation"
  |[var] -> var
  |h::t -> (printAffLambda t) ^ "(" ^ h ^ ")"
								     
let rec printSubstitution sub n= match sub with
  |Affectation (bSet1,bSet2) -> indent n ^ printBSet bSet1 ^ " := " ^ printBSet bSet2
  |Select [] -> failwith "it shouldn't exist"
  |Select [(pred,sub)] -> indent n ^ "SELECT\n" ^ printPredicateB pred (n+3) ^ "\n" ^ indent n ^ "THEN\n" ^ printSubstitution sub (n+3) ^ indent n ^ "END\n"
  |Select ((pred,sub)::t) -> indent n ^ "SELECT\n" ^ printPredicateB pred (n+3) ^ "\n" ^ indent n ^ "THEN\n" ^ printSubstitution sub (n+3) ^ printStringList (List.rev_map (print1SelectCase n) t) ^ indent n ^ "END\n"
  |Parallel [] -> failwith "it shouldn't appenned"
  |Parallel [t] -> printSubstitution t n ^ "\n"
  |Parallel (h::t) -> printSubstitution h n ^ " ||\n" ^ printSubstitution (Parallel t) n
  |AffectationLambda (varList, li) ->  indent n ^ printAffLambda varList ^ " := " ^ List.fold_left (printLambdaOvl n) (printAffLambda varList) li
  |CallB (name,parameters) -> indent n ^ name ^ begin
						 let param = printParamWithoutType parameters in
						 if param = ""
 						 then ""
						 else "(" ^ param ^ ")"
					       end
  |Any (name,pred,sub) -> indent n ^ "ANY\n" ^ indent (n+3) ^ name ^ "\n" ^
			    indent n ^ "WHERE\n" ^ printPredicateB pred (n+3) ^ "\n" ^
			      indent n ^ "THEN\n" ^ printSubstitution sub (n+3) ^
				indent n ^ "END\n"
and print1SelectCase n ca = let pred,sub = ca
			    in indent n ^ "WHEN\n" ^  (printPredicateB pred (n+3)) ^ "\n" ^  indent n ^ "THEN\n" ^ printSubstitution sub (n+3);;

let printOperation ope = indent 3 ^ ope.nameOf ^ begin
						   let param = printParam ope.parameter in
						   if param = ""
						   then ""
						   else "(" ^ param ^ ")"
						 end ^ " = \n" ^ indent 3 ^  "PRE\n" ^ (printPredicateB ope.preOf 6) ^ "\n" ^ indent 3 ^ "THEN\n" ^ (printSubstitution ope.postOf 6) ^ indent 3 ^ "END";;




let rec printVariables var = match var with
  |[] -> ""
  |[t] -> indent 3 ^ t ^ "\n"
  |h::t -> indent 3 ^ h ^ ",\n" ^ printVariables t;;

let rec printTypage typage = match typage with
  |[] -> ""
  |[t] -> t
  |h::t -> "(" ^ h ^ " --> " ^ printTypage t ^ ")";;

let rec printInv inv = match inv with
  |[] -> ""
  |[(var,typage)] -> indent 3 ^ var ^ " : " ^ printTypage typage
  |(var,typage)::t -> indent 3 ^ var ^ " : " ^ printTypage typage ^ " &\n" ^ printInv t;;

let rec printInitTypage typage value = match typage with
  |[] -> "{" ^ value ^ "}"
  |h::t -> h ^ "* {" ^ printInitTypage t value ^ "}"

let rec printInit initList = match initList with
  |[] -> ""
  |[init] ->
    begin
      match init with
      |AffectationInit (bSet1,bSet2) -> indent 3 ^ printBSet bSet1 ^ " := " ^ printBSet bSet2
      |AnyInit (var,pred,bSet1,bSet2) -> indent 3 ^ "ANY " ^ var ^ " WHERE " ^ printPredicateB pred 3 ^ " THEN " ^ printBSet bSet1 ^ " := " ^ printBSet bSet2 ^ " END\n"
    end
  |(init)::t ->
    let initPrint =
      begin
	match init with
	|AffectationInit (bSet1,bSet2) -> indent 3 ^ printBSet bSet1 ^ " := " ^ printBSet bSet2
	|AnyInit (var,pred,bSet1,bSet2) -> indent 3 ^ "ANY " ^ var ^ " WHERE " ^ printPredicateB pred 3 ^ " THEN "^ printBSet bSet1 ^ " := " ^ printBSet bSet2 ^ " END"
      end in
    initPrint ^ " ||\n" ^ printInit t;;

let rec printOperationList li = match li with
  |[] -> ""
  |[h] -> printOperation h
  |h::t -> printOperation h ^ ";\n\n" ^ printOperationList t;;

let rec print_machine ma = 
  let nameOf = match ma.machine with
    |Machine name -> "MACHINE\n" ^ indent 3 ^ name
    |Refinement (name,refines) -> "REFINEMENT\n" ^ indent 3 ^ name ^ "\nREFINES\n" ^ indent 3 ^ refines
  in
  let seeString = match  ma.sees with
    |NoSeenMachine -> ""
    |SeenMachine s -> "\nSEES\n" ^ indent 3 ^ s
  in
  let includeString = match ma.includes with
    |NoIncludedMachine -> ""
    |IncludedMachine s -> "\nINCLUDES\n" ^ indent 3 ^ s
  in
  let assertionString = match ma.assertions with
    |"" -> ""
    |_ -> "ASSERTIONS\n" ^ ma.assertions
  in
  let invPreuve = if ma.invariants.invariantsPreuve = ""
		  then "\n"
		  else " &\n" ^ ma.invariants.invariantsPreuve
  in
  begin
    nameOf ^ seeString ^ includeString ^ "\nSETS\n" ^ printSets ma.sets ^ "VARIABLES\n" ^ printVariables ma.variables ^ assertionString ^ "INVARIANT\n" ^ printInv ma.invariants.typage ^ invPreuve ^ "INITIALISATION\n" ^ printInit ma.init ^ "\nOPERATIONS\n" ^ (printOperationList ma.operations) ^ "\nEND"
  end;;

