open ASTD_B;;
open ASTD_astd;;

exception NotFound of string;;
exception InitIsAny of ASTD_B.predicateB;;
exception TrueGuard of ASTD_B.substitutionB;;
exception NoParam;;


(*
  This operation adds the state nameOfTheState to the set nameOfTheStateSet in the setList.
  The set setList is a list (string,(string list)). The first part of the couple is the name of the state, the second part is the list of the values of the enumerate set. If the set doesn't exists, it is created with the name ("AutState_nameOfTheStateSet") and one enumerate value nameOfTheState
  Arguments :
  - nameOfTheState : name of the enumerate value we want to add
  - nameOfTheSet : name of the enumerate set
  - setList : list of the set allready defined
 *)

let rec addStateToStateList nameOfTheState nameOfTheStateSet setList = match setList with
  |[] -> ["AutState_" ^ nameOfTheStateSet,[nameOfTheState]]
  |(name,stateList)::t -> if name = "AutState_" ^ nameOfTheStateSet
			  then (name,nameOfTheState::stateList)::t
			  else (name,stateList)::(addStateToStateList nameOfTheState nameOfTheStateSet t);;


(*
  This function seperates the list opeList into two operation lists : The first one are the operation whose name is "name", the second one are the other operations
  Arguments :
  - name : The label (a string) of the operations we want to collect
  - opeList : The operation list we want to seperate
 *)

let rec seperateOperation name opeList = match opeList with
  |[] -> [],[]
  |(nameState,op)::t -> let nameOperationList,otherOperationList = seperateOperation name t in
			if op.nameOf = name
			then
			  (((nameState,op)::nameOperationList),otherOperationList)
			else
			  (nameOperationList,((nameState,op)::otherOperationList));;

(*
  Same as the previous function, execpt it is for the transitions.
 *)

let rec seperateTransition name transition_list = match transition_list with
  |[] -> [],[]
  |h::t -> let nameTransitionList,otherTransitionList = seperateTransition name t in
	   if (ASTD_arrow.get_label_transition h) = name
	   then
	     ((h::nameTransitionList),otherTransitionList)
	   else
	     (nameTransitionList,(h::otherTransitionList));;

(*
  This operation get the ASTD whose name is "name" in the ASTD "astd" in arguement
  Arguements :
  - name : name of the ASTD we are looking for
  - astd : astd in which we look for the astd
  Operation getAstdFromStateList
  This operation search for the ASTD whose name is "name" in the state list "stateList"
  Arguements :
  - name : name of the ASTD we are looking for
  - statList : list of ASTD state in which we search for the ASTD name
 *)


let rec getAstdFromName name astd = match astd with
  |Elem nameElem -> if nameElem = name then astd else raise (NotFound name)
  |Automata (nameAut,stateList,_,_,_,_)-> if nameAut = name then astd else getAstdFromStateList name stateList
  |Sequence (nameSeq,subAstd1,subAstd2) ->
    if name = nameSeq then astd else
      begin
	try getAstdFromName name subAstd1 with
	|NotFound _ -> getAstdFromName name subAstd2
      end
  |Choice (nameCh,subAstd1,subAstd2) ->
    if name = nameCh then astd else
      begin
	try getAstdFromName name subAstd1 with
	|NotFound _ -> getAstdFromName name subAstd2
      end    
  |Kleene(nameKle,subAstd) -> if nameKle = name then astd else getAstdFromName name subAstd
  |Synchronisation(nameSynch,_,subAstd1,subAstd2) ->
    if name = nameSynch then astd else
      begin
	try getAstdFromName name subAstd1 with
	|NotFound _ -> getAstdFromName name subAstd2
      end
  |Fork(nameFork,_,_,subAstd1,subAstd2) ->
    if name = nameFork then astd else
      begin
	try getAstdFromName name subAstd1 with
	|NotFound _ -> getAstdFromName name subAstd2
      end
  |QChoice(nameQC,_,_,subAstd) -> if nameQC = name then astd else getAstdFromName name subAstd
  |QSynchronisation(nameQS,_,_,_,subAstd) -> if nameQS = name then astd else getAstdFromName name subAstd
  |QFork(nameQF,_,_,_,_,subAstd)-> if nameQF = name then astd else getAstdFromName name subAstd
  |Guard (nameGu,_,subAstd) -> if nameGu = name then astd else getAstdFromName name subAstd
  |Call(nameCa,_,_) -> if nameCa = name then astd else raise (NotFound name)

and getAstdFromStateList name stateList = match stateList with
  |[] -> raise (NotFound name)
  |h::t -> try getAstdFromName name h with
	   |NotFound _ -> getAstdFromStateList name t;;

let quantifyOneInitAllVar set substitution =
      match substitution with
      |Affectation (var,value) ->
	begin
	  match (var,value) with
	  |(Variable _,Constant affVal) ->
	    Affectation (var,CartesianP [set;affVal])
	  |(Variable _,CartesianP li) ->
	    Affectation (var,CartesianP (set::li))
	  |_ -> failwith "bad Affectation"
	end
      |_ -> failwith "Bad Substitution";;
    


(*
  This operation returns an affectation list representing the fact that we initialize all the state variables in the ASTD nameInitialState
  Arguments :
  - nameOfState : name of the state that we want to initialize
  - astd : the ASTD in which we initialize the state. This arguments is needed because we need to search for the ASTD corresponding to the state "nameOfState"
 *)

let rec initializeAllVariable nameOfState astd = 
  let initialAstd = getAstdFromName nameOfState astd in
  match initialAstd with
  |Elem _ -> []
  |Automata (name,_,_,_,_,init) ->
    (Affectation (Variable ("State_" ^ name),
		  Constant init))::(initializeAllVariable init astd)
  |Sequence (name,subAstd1,subAstd2) ->
    let initialize1 = (initializeAllVariable (get_name subAstd1) astd) and
	initialize2 = (initializeAllVariable (get_name subAstd2) astd) in
    (Affectation (Variable ("State_" ^ name),
		  Constant "fst"))::(initialize1@initialize2)
  |Choice (name,subAstd1,subAstd2) ->
    let initialize1 = (initializeAllVariable (get_name subAstd1) astd) and
	initialize2 = (initializeAllVariable (get_name subAstd2) astd) in
    (Affectation (Variable ("State_" ^ name),
		  Constant "none"))::(initialize1@initialize2)
  |Kleene(name,subAstd) ->
    (Affectation (Variable("State_" ^ name),
		  Constant "notStarted"))::(initializeAllVariable (get_name subAstd) astd)
  |Synchronisation (name,_,subAstd1,subAstd2) ->
    let initialize1 = (initializeAllVariable (get_name subAstd1) astd) and
	initialize2 = (initializeAllVariable (get_name subAstd2) astd) in
    initialize1@initialize2
  |Fork (name,_,_,subAstd1,subAstd2) ->
    let initialize1 = (initializeAllVariable (get_name subAstd1) astd) and
	initialize2 = (initializeAllVariable (get_name subAstd2) astd) in
    initialize1@initialize2
  |QChoice (name,_,_,subAstd) ->
    (Affectation (Variable ("State_" ^ name),
		  Constant "notChosen"))::(initializeAllVariable (get_name subAstd) astd)
  |Guard (name,_,subAstd) ->
    (Affectation (Variable ("State_" ^ name),
		  Constant "nonChecked"))::initializeAllVariable (get_name subAstd) astd
  |QSynchronisation(name,_,set,_,subAstd) ->
    let initSub = initializeAllVariable (get_name subAstd) astd in
    List.rev_map (quantifyOneInitAllVar set) initSub		 
  |QFork(name,_,set,_,_,subAstd) ->
    let initSub = initializeAllVariable (get_name subAstd) astd in
    List.rev_map (quantifyOneInitAllVar set) initSub
  |Call(name,subAstdName,_) ->
    (Affectation (Variable ("State_" ^ name),
		  Constant "notCalled"))::initializeAllVariable subAstdName astd
(*
  This operation returns the last element of a list
  Arguments :
  - li : the list
 *)
								 
let rec lastElem li = match li with
  |[] -> failwith "Empty list : no last elem"
  |[t] -> t
  |h::t -> lastElem t

(*
  This operation returns the initial value of the variable var1. This initial value is found in the listVar list.
  Arguements :
  - listVar : The list of variables that is computed by the translate operation
  - var1 : The variable that we need to calculate the inital value
 *)

let rec initValueOfVar listVar var1 =
  let name = match var1 with
    |Constant str -> str
    |Variable str -> str
    |EnumerateSet li -> failwith "Not a Proper Variable"
    |Function (name,param) -> name
    |QVar str -> str
    |_ -> failwith "Bad BSet"
  in
  match listVar with
  |[] -> name
  |(nameVar,typeList,valueVar)::t -> 
    if nameVar = name then
      begin
	match valueVar with
	| AffectationInit (var1,var2) -> 
	   begin
	     match var2 with
	     | Constant str -> str
	     | Variable str -> failwith "initializing a Variable with a variable"
	     | CartesianP li ->  lastElem li
	     | _ -> failwith "Unbound initial Value"
	   end
	| AnyInit (var,pred,_,_) -> raise (InitIsAny pred)
      end
    else initValueOfVar t (Variable name)

(*
  This function correpond to the [init] operation of the translation (see the article with the translation rules). It replaces all the variable by their initial values. The initPredSimpl simplifies the predicate, which means that the x=y are replaced by False and x=x are replaced by False.
  Arguments :
  - pred : The predicate we want to "init"
  - listVar : The variable list as calculated in the translate function. It is used to find the initial value of the variable
 *)
			
let rec initPred pred listVar = match pred with
  |And (pred1,pred2) ->
    let initPred1 = initPred pred1 listVar and
	initPred2 = initPred pred2 listVar in
    begin
      match initPred1,initPred2 with
      |(False,_) -> False
      |(True,_) -> initPred2
      |(_,True) -> initPred1
      |(_,False) -> False
      |(_,_) -> And (initPred1, initPred2)
    end
  |Or (pred1,pred2) ->
    let initPred1 = initPred pred1 listVar and
	initPred2 = initPred pred2 listVar in
    begin
      match initPred1,initPred2 with
      |(True,_) -> True
      |(False,_) -> initPred2
      |(_,False) -> initPred1
      |(_,True) -> True
      |(_,_) -> Or (initPred1, initPred2)
    end
  |BPred s -> BPred s
  |Equality (var1,val1) ->
    begin
      try
	let value1 = initValueOfVar listVar var1
	and value2 = strOfValue val1 in
	if value1 = value2 then True else False
      with
      | InitIsAny pred -> pred
    end
  |In (var1,val1) -> In (Constant (initValueOfVar listVar var1), val1)
  |True -> True
  |Implies (pred1,pred2) -> Implies (initPred pred1 listVar,initPred pred2 listVar)
  |False -> False
  |Exists(var,predicate) -> 
    let initPredicate = initPred predicate listVar in
    begin
      match initPredicate with
      |False -> False
      |True -> True
      |_ -> Exists(var, initPredicate)
    end
  |Forall(var,pred1,pred2) ->
    let initPredicate2 = initPred pred2 listVar in
    begin
      match initPredicate2 with
      |False -> False
      |True -> True
      |_ -> Forall (var,
		    initPred pred1 listVar,
		    initPredicate2)
    end
      
let initPredAffectationLambdaElement listVar elem =
  let str1,pred,str2 = elem in
  str1,(initPred pred listVar),str2

let rec initSub listVar sub = match sub with
  |Affectation (_,_) -> sub
  |Select listSelect -> begin
			try Select (initSubSelectList listSelect listVar) with
			|TrueGuard sub -> sub
		      end
  |Parallel listPara -> Parallel (List.rev_map (initSub listVar) listPara)
  |CallB _ -> sub
  |Any(string, pred, substit) ->
    let initSubstit = initSub listVar substit in
    begin
      match initSubstit with
      |Select [] -> Select []
      |_ -> Any (string , initPred pred listVar, initSubstit)
    end
  |AffectationLambda (var,li) -> AffectationLambda (var,List.rev_map (initPredAffectationLambdaElement listVar) li)
and initSubSelectList listSelect listVar = match listSelect with
  |[] -> []
  |(gu,post)::t -> let initGu = initPred gu listVar in
		   begin
		     match initGu with
		     |True -> raise (TrueGuard (initSub listVar post))
		     |False -> initSubSelectList t listVar
		     |_ -> (initGu,initSub listVar post)::(initSubSelectList t listVar)
		   end

let replaceVariable str1 str2 bSet = match bSet with 
  |Variable var -> if var = str1 then Variable str2 else bSet
  |_ -> bSet

let quantifiedVariable param bSet = match bSet with
  |Variable v -> Function (v,[param])
  |Function (v,paramList) -> Function (v,param::paramList)
  |CartesianP li -> CartesianP (param::li)
  |_ -> bSet

(*
  This operation Translate the list of predicate in the guard of the ASTD into a B predicate.
  Argument :
  - astdPredicate : The astd predicate we want to translate
 *)

let rec translatePredicateList astdPredicate = match astdPredicate with
  |[] -> True
  |[t] -> 
    begin
      match t with
      |ASTD_predicate.IASTDPredicate _ -> failwith "This predicate is not supported"
      |ASTD_predicate.BPredicate str -> BPred str
    end
  |h::t ->
    begin
      match h with
      |ASTD_predicate.IASTDPredicate _ -> failwith "This predicate is not supported"
      |ASTD_predicate.BPredicate str -> And(BPred str,translatePredicateList astdPredicate)
    end



(*
  This operation returns the B predicate that verifies if the ASTD "astd" is final
  Arguments :
  - astd : the ASTD that has to be final
  Function dFinalStateCond :
  This operation is used in the case of deep final state. It returns a B predicate that is the condition for all deep final state to be final
  Arguments :
  - dFinal : the list of deep final states
  - astd : the ASTD in wich we work
 *)

let rec final astd listVar = match astd with
  |Elem e -> True
  |Automata (name,_,_,sFinal,dFinal,_) -> 
    begin
      match sFinal,dFinal with
      |[],[] -> failwith "No Final State"
      |t::q,[] -> In(Variable ("State_" ^ name),
		     EnumerateSet sFinal)
      |[],t::q -> And(In(Variable ("State_"^name),
			 EnumerateSet dFinal),
		      dFinalStateCond dFinal astd listVar)
      |t1::q1,t2::q2 -> (Or(In(Variable ("State_" ^ name),
			       EnumerateSet sFinal),
			    (And (In(Variable ("State_"^name),
				     EnumerateSet dFinal),
				  dFinalStateCond dFinal astd listVar))))			    
			      
    end
  |Fork (name,_,predicate_list,astdRight,astdLeft) ->
    Implies(translatePredicateList predicate_list,
	    And (final astdRight listVar,
		 final astdLeft listVar))
  |Sequence (name,astdFst,astdSnd) -> And (final astdSnd listVar,
					   Implies (Equality (Variable ("State_" ^ name),
							      Constant "fst"),
						    final astdFst listVar))
  |Choice(name,astdLeft,astdRight) -> 
    And (Implies (Equality (Variable ("State_" ^ name),
			    Constant "none"),
		  Or (initPred (final astdLeft listVar) listVar,
		      initPred (final astdRight listVar) listVar)),
	 And (Implies (Equality (Variable ("State_" ^ name),
				 Constant "leftS"),
		       final astdLeft listVar),
	      Implies (Equality (Variable ("State_" ^ name),
				 Constant "rightS"),
		       final astdRight listVar)))
  |Kleene(name,subAstd) -> Or (Equality (Variable ("State_" ^ name),
					 Constant "notStarted"),
			       final subAstd listVar)
  |Synchronisation (name,labelList,astdLeft,astdRight) ->
    And (final astdLeft listVar,
	 final astdRight listVar)
  |QChoice (name,var,domain,subAstd) -> 
    And (Implies (Equality (Variable ("State_" ^ name),
			    Constant "notChosen"),
		  Exists ("vv",
			  And (In (Constant "vv",
				   Constant domain),
			       predMap (replaceVariable var "vv") (initPred (final subAstd listVar) listVar)))),
	 Implies (Equality (Variable ("State_" ^ name),
			    Constant "chosen"),
		  predMap (replaceVariable var "vv") (final subAstd listVar)))
  |QSynchronisation(name,var,domain,_,subAstd) ->
    Forall(var,(In(QVar var,Constant domain)),predMap (quantifiedVariable var) (final subAstd listVar))
  |QFork (name,var,domain,predicate,_,subAstd) ->
    Forall(var,
	   And((In(QVar var,Constant domain)),
	       translatePredicateList predicate),
	   predMap (quantifiedVariable var) (final subAstd listVar))
  |Guard(name,gu,subAstd) ->
    And(Implies (Equality (Variable ("State_" ^ name),
			   Constant "notChecked"),
		 initPred (final subAstd listVar) listVar),
	Implies (Equality (Variable ("State_" ^ name),
			   Constant "checked"),
		 final subAstd listVar))
and dFinalStateCond dFinal astd listVar = match dFinal with
  |[] -> failwith "No DFinal State"
  |[t] -> Implies (Equality(Variable ("State_" ^ (get_name astd)),
			    Constant t),
		   final (getAstdFromName t astd) listVar)
  |t::q -> And(Implies (Equality(Variable ("State_" ^ (get_name astd)),
				 Constant t),
			final (getAstdFromName t astd) listVar),
	       dFinalStateCond q astd listVar);;


(*
  This operation transform an arrow into a couple (precondition, postcondition). The precondition is a B predicate corresponding to the preOf of the function. The postcondition is a substitution corresponding to the thenOf of the function.
  Arguments :
  - translatedAstd : the ASTD we are translating
  - transition : the arrow we are translating
 *)

let transformTransition translatedAstd listVar transition= 
  let name = get_name translatedAstd
  in match transition with
     |ASTD_arrow.Local(fromState,toState,astdTransition,astdPredicate,finale) ->
       ((let cAll = (Equality (Variable ("State_" ^ name ),
			       Constant fromState))
	 in let preOf =
	      (if finale
	       then
		 let finalPred = final (getAstdFromName fromState translatedAstd) listVar in
		 begin
		   match finalPred with
		   |True -> cAll
		   |_ -> (And(cAll,
			      finalPred))
		 end
	       else cAll)
	    in
	    let gu = translatePredicateList astdPredicate in
	    if gu = True then preOf
	    else And(preOf,gu)),
	let tAll = (Affectation (Variable ("State_" ^ name),
				 Constant toState))
	in Parallel (tAll::(initializeAllVariable toState translatedAstd)))
     |ASTD_arrow.From_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
       ((let cAll = (Equality (Variable ("State_" ^ name ),
			       Constant throughState))
	 in let cFromSub = Equality(Variable("State_" ^ throughState),
				    Constant fromState)
	    in let preOf =
		 (if finale
		  then
		    let finalPred = final (getAstdFromName fromState translatedAstd) listVar in
		    begin
		      match finalPred with
		      |True -> And(cAll,cFromSub)
		      |_ -> (And(And(cAll,cFromSub),
				 finalPred))
		    end
		  else And(cAll,cFromSub))
	       in
	       let gu = translatePredicateList astdPredicate in
	       if gu = True then preOf
	       else And(preOf,gu)),
	let tAll = (Affectation (Variable ("State_" ^ name),
				 Constant toState))
	in Parallel (tAll::(initializeAllVariable toState translatedAstd)))  
     |ASTD_arrow.To_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
       ((let cAll = Equality(Variable("State_" ^ name),
			     Constant fromState)
	 in let preOf =
	      (if finale
	       then
		 let finalPred = final (getAstdFromName fromState translatedAstd) listVar in
		 match finalPred with
		 |True -> cAll
		 |_ -> (And(cAll,
			    finalPred))
	       else cAll)
	    in
	    let gu = translatePredicateList astdPredicate in
	    if gu = True then preOf
	    else And(preOf,gu)),
	let tAll = (Affectation (Variable ("State_" ^ name),
				 Constant throughState))
	in let tToSub = (Affectation (Variable("State_" ^ throughState),
				      Constant toState))
	   in
	   begin
	     match toState with
	     |"H1" -> Parallel (tAll::(initializeAllVariable throughState translatedAstd))
	     |"H2" -> Parallel ([tAll])
	     |_ -> Parallel (tAll::tToSub::(initializeAllVariable toState translatedAstd))
	   end)

(*
  This fuction returns the conjunction of the preconditions of the operations in the subList
  Arguments :
  - subList : The list of the operations
 *)

let rec getPreOf subList = match subList with
  |[] -> failwith "fail preOf"
  |[(gu,act)] -> gu
  |(gu,act)::t -> Or (gu, getPreOf t);;



let transformSubOperation name elem = 
  let (name1,operation) = elem in
  let newPost =
    begin
      match operation.postOf with
      |Parallel li -> Parallel ((Affectation (Variable ("State_" ^ name),
					      Constant name1))::li)
      |_ -> Parallel [operation.postOf;
		      Affectation (Variable ("State_" ^ name),
				   Constant name1)]
    end
  in
  (And (Equality (Variable ("State_" ^ name),
		  Constant name1),
	operation.preOf),
   newPost);;

(*
  This operation transform the list of transition in operations, and merges it with the list of allready translated operations. It takes 5 arguments :
  - astd : The current translated astd
  - nameOperation : The name of the operation
  - hOperationList : The list of operations translated in the subAstd
  - hTransitionList : The transition list of the ASTD labelled with nameOperatoin
  - translatedAstd : The global translated Astd
 *)

let merge astd nameOperation hOperationList hTransitionList listVar param=
  let subList = ((List.rev_map (transformTransition astd listVar) hTransitionList)@(List.rev_map (transformSubOperation (get_name astd)) hOperationList))
  in let preOf = getPreOf subList
     in (get_name astd,{nameOf = nameOperation;
			parameter =param;
			preOf=preOf;
			postOf=Select subList});;
  
let rec toStringParamList param = match param with
  |[] -> []
  |h::t -> match h with
	   |(ASTD_term.Var s,ASTD_term.Var s2) -> (s,s2)::(toStringParamList t)
	   |_ -> failwith "Unbound Parameter"

let rec getParamFromTransition h = 
  match h with
  |ASTD_transition.Transition (name,param) -> toStringParamList param

let modifyOperationOfSubAstd astd ope =
  let name = get_name astd in
  let (nameOpe,opeOpe) = ope in
  (name,{nameOf = opeOpe.nameOf;
	 parameter = opeOpe.parameter;
	 preOf = And (Equality (Variable ("State_" ^ name),
				Constant nameOpe),
		      opeOpe.preOf);
	 postOf = Select [(And (Equality (Variable ("State_" ^ name),
					  Constant nameOpe),
				opeOpe.preOf),
			   Parallel[opeOpe.postOf;
				    Affectation(Variable ("State_" ^ name),
						Constant nameOpe)])]})

(*
  This operation construct the new operation list of the translation. It gives an operation list.
  It takes 4 arguments :
  - name : it's the name of the automata that is translated
  - transition_list : The list of the transition of the translated automata
  - opeList : the list of operation of the sub ASTD
  - translatedAstd : the principal translated ASTD
  The idea is to get all the transitions and the operations that have 
 *)

let rec addOperationFromTransitionList astd transition_list opeList listVar = match transition_list with
  |[] -> List.rev_map (modifyOperationOfSubAstd astd) opeList
  |h::t -> let hOperationList,otherOpeList = 
	     seperateOperation (ASTD_arrow.get_label_transition h) opeList in
	   let hTransitionList, otherTransitionList =
	     seperateTransition (ASTD_arrow.get_label_transition h) transition_list in
	   (merge astd (ASTD_arrow.get_label_transition h) hOperationList hTransitionList listVar (getParamFromTransition (ASTD_arrow.get_transition h)))::
	     (addOperationFromTransitionList astd otherTransitionList otherOpeList listVar);;



let createPrePostSeq lOpeFst lOpeSnd name astdFst varList= match (lOpeFst,lOpeSnd) with
  |_,h1::h2::t -> failwith "Shouln't Happend"
  |h1::h2::t,_ -> failwith "Shouln't Happend"
  |[],[] -> failwith "Shouldn't Happend"
  |[(nameFst,opeFst)],[] ->
    let pre1 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "fst"), 
		     opeFst.preOf )) in
    (pre1,
     Select [(pre1,opeFst.postOf)])
  |[nameFst,opeFst],[nameSnd,opeSnd] -> 
    let pre1,pre2,pre3 = (And (Equality (Variable ("State_" ^ name), 
					 Variable "fst"), 
			       opeFst.preOf ),
			  And (Equality (Variable ("State_" ^ name),
					 Variable "snd"),
			       And (final astdFst varList,initPred opeSnd.preOf varList)), 
			  And (Equality (Variable ("State_" ^ name),
					 Variable "snd"),
			       opeSnd.preOf))
    in
    (Or(Or (pre1,pre2),pre3),
     Select [(pre1,opeFst.postOf);
	     (pre2,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "snd"));
			     initSub varList (opeSnd.postOf)]);
	     (pre3,opeSnd.postOf)])
  |[],[nameSnd,opeSnd] ->
    let pre2,pre3 = (
      And (Equality (Variable ("State_" ^ name),
		     Variable "snd"),
	   And (final astdFst varList,initPred opeSnd.preOf varList)), 
      And (Equality (Variable ("State_" ^ name),
		     Variable "snd"),
	   opeSnd.preOf))
    in
    (Or(pre2,pre3),
     Select [(pre2,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "snd"));
			     initSub varList (opeSnd.postOf)]);
	     (pre3,opeSnd.postOf)])

let rec modifyOperationForSequence listFst listSnd name astdFst varList = match (listFst,listSnd) with
  |[],[] -> []
  |[],(hSnd::tSnd) -> 
    let (nameSnd,opeSnd) = hSnd in
    let pre,post = createPrePostSeq [] [hSnd] name astdFst varList in
    (name,{nameOf = opeSnd.nameOf;
	   parameter = opeSnd.parameter;
	   preOf=pre;
	   postOf=post})::(modifyOperationForSequence listFst tSnd name astdFst varList)   
  |((hFst::tFst),listSnd) ->
    let (nameFst,opeFst) = hFst in
    let opeFstList,opeNonFst = seperateOperation opeFst.nameOf listSnd in 
    let pre,post = createPrePostSeq [hFst] opeFstList name astdFst varList in
    (name,{nameOf = opeFst.nameOf;
	   parameter = opeFst.parameter;
	   preOf=pre;
	   postOf=post})::(modifyOperationForSequence tFst opeNonFst name astdFst varList)

let createPrePostChoice lOpeLeft lOpeRight name astdLeft varList= match (lOpeLeft,lOpeRight) with
  |_,h1::h2::t -> failwith "Shouln't Happend"
  |h1::h2::t,_ -> failwith "Shouln't Happend"
  |[],[] -> failwith "Shouldn't Happend"
  |[(nameLeft,opeLeft)],[] ->
    let pre1 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "none"), 
		     initPred opeLeft.preOf varList )) and
	pre3 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "leftS"), 
		     opeLeft.preOf))
    in
    (Or (pre1,pre3),
     Select [(pre1,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "leftS"));
			     initSub varList (opeLeft.postOf)]);
	     (pre3,opeLeft.postOf)])
  |[nameLeft,opeLeft],[nameRight,opeRight] -> 
    let pre1 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "none"), 
		     initPred opeLeft.preOf varList)) and
	pre2 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "none"), 
		     initPred opeRight.preOf varList)) and
	pre3 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "leftS"), 
		     opeLeft.preOf)) and
	pre4 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "rightS"), 
		     opeRight.preOf)) in
    (Or (Or (pre1,pre2),Or (pre3,pre4)),
     Select [(pre1,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "leftS"));
			     initSub varList (opeLeft.postOf)]);
	     (pre2,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "rightS"));
			     initSub varList (opeRight.postOf)]);
	     (pre3,opeLeft.postOf);
	     (pre4,opeRight.postOf)])
  |[],[nameRight,opeRight] ->
    let pre2 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "none"), 
		     initPred opeRight.preOf varList )) and
	pre4 = (And (Equality (Variable ("State_" ^ name), 
			       Variable "rightS"), 
		     opeRight.preOf))
    in
    (Or (pre2,pre4),
     Select [(pre2,Parallel [(Affectation (Variable ("State_" ^ name),
					   Constant "rightS"));
			     initSub varList (opeRight.postOf)]);
	     (pre4,opeRight.postOf)])


let rec modifyOperationForChoice listLeft listRight name astdLeft varList = match (listLeft,listRight) with
  |[],[] -> []
  |[],(hRight::tRight) -> 
    let (nameRight,opeRight) = hRight in
    let pre,post = createPrePostChoice [] [hRight] name astdLeft varList in
    (name,{nameOf = opeRight.nameOf;
	   parameter = opeRight.parameter;
	   preOf=pre;
	   postOf=post})::(modifyOperationForChoice listLeft tRight name astdLeft varList)   
  |((hLeft::tLeft),listLeft) ->
    let (nameLeft,opeLeft) = hLeft in
    let opeLeftList,opeNonLeft = seperateOperation opeLeft.nameOf listRight in 
    let pre,post = createPrePostChoice [hLeft] opeLeftList name astdLeft varList in
    (name,{nameOf = opeLeft.nameOf;
	   parameter = opeLeft.parameter;
	   preOf=pre;
	   postOf=post})::(modifyOperationForChoice tLeft opeNonLeft name astdLeft varList)

let rec modifyOperationForKleene name subAstd varList ope =
  let (nameOpe,opeOpe) = ope in
  let pre1 = let initPreOf = initPred (opeOpe.preOf) varList and
		 finalSub = Or (final subAstd varList,
				Equality (Variable ("State_" ^ name),
					  Constant "notStarted"))
	     in
	     begin
	       match initPreOf with
	       |True -> finalSub
	       |_-> And(finalSub,initPreOf)
	     end and

      (* And (Or (final subAstd varList, *)
      (* 				      Equality (Variable ("State_" ^ name), *)
      (* 						       Constant "notStarted")), *)
      (* 			   initPred (opeOpe.preOf) varList) and *)
      pre2 = And (Equality (Variable ("State_" ^ name),
			    Constant "started"),
		  opeOpe.preOf) in
  let post = Select [pre1, Parallel [Affectation (Variable ("State_" ^ name),
						  Constant "started");
				     initSub varList (opeOpe.postOf)];
		     pre2, opeOpe.postOf] in
  (name,{nameOf = opeOpe.nameOf;
	 parameter = opeOpe.parameter;
	 preOf = simplifyPred (Or (pre1,pre2));
	 postOf = simplifySub post});;
(* match listOpe with *)
(*  |[] -> [] *)
(*  |(nameOpe,opeOpe)::t -> *)
(*    let pre1 = let initPreOf = initPred (opeOpe.preOf) varList and *)
(* 		   finalSub = Or (final subAstd varList, *)
(* 					 Equality (Variable ("State_" ^ name), *)
(* 							  Constant "notStarted")) *)
(* 	       in *)
(* 	       begin *)
(* 		 match initPreOf with *)
(* 		 |True -> finalSub *)
(* 		 |_-> And(finalSub,initPreOf) *)
(* 	       end and *)

(*      (\* And (Or (final subAstd varList, *\) *)
(*      (\* 				      Equality (Variable ("State_" ^ name), *\) *)
(*      (\* 						       Constant "notStarted")), *\) *)
(*      (\* 			   initPred (opeOpe.preOf) varList) and *\) *)
(* 	pre2 = And (Equality (Variable ("State_" ^ name), *)
(* 					    Constant "started"), *)
(* 			   opeOpe.preOf) in *)
(*    let post = Select [pre1, Parallel [Affectation (Variable ("State_" ^ name), *)
(* 									 Constant "started"); *)
(* 						     initSub (opeOpe.postOf) varList]; *)
(* 			      pre2, opeOpe.postOf] in *)
(*    (name,{nameOf = opeOpe.nameOf; *)
(* 	   parameter = opeOpe.parameter; *)
(* 	   preOf = simplifyPred (Or (pre1,pre2)); *)
(* 	   postOf = simplifySub post})::(modifyOperationsForKleene t name subAstd varList);; *)

let rec isInSyncSet name syncList = match syncList with
  |[] -> false
  |h::t -> (h = name) || isInSyncSet name t;;

let createPrePostSync listLeft listRight syncList = match (listLeft,listRight) with
  |[],_ -> failwith "Shouldn't Happend"
  |h1::h2::t,_ -> failwith "Shouldn't Happend"
  |_,h1::h2::t -> failwith "Shouldn't Happend"
  |[(nameLeft,opeLeft)],[] -> 
    if isInSyncSet opeLeft.nameOf syncList then
      failwith "Shouldn't Happend"
    else (opeLeft.preOf, Select ([(opeLeft.preOf,opeLeft.postOf)]))
  |[(nameLeft,opeLeft)],[(nameRight,opeRight)] ->
    if isInSyncSet opeLeft.nameOf syncList then
      (And (opeLeft.preOf,
	    opeRight.preOf),
       Parallel [opeLeft.postOf;opeRight.postOf])
    else
      (Or (opeLeft.preOf,
	   opeRight.preOf),
       Select [(opeLeft.preOf,opeLeft.postOf);
	       (opeRight.preOf,opeRight.postOf)])

let rec modifyOperationsForSynchro opeListLeft opeListRight syncSet name = match (opeListLeft,opeListRight) with
  |[],[] -> []
  |[],(nameRight,opeRight)::tail ->
    if isInSyncSet opeRight.nameOf syncSet 
    then failwith "Shouldn't Happend"
    else
      (name,{nameOf = opeRight.nameOf;
	     parameter = opeRight.parameter;
	     preOf = opeRight.preOf;
	     postOf = Select ([(opeRight.preOf,opeRight.postOf)])})::
	modifyOperationsForSynchro opeListLeft tail syncSet name
  |(nameLeft,opeLeft)::tailLeft,listRight ->
    let opeLeftList,opeNonLeft = seperateOperation opeLeft.nameOf listRight in
    let pre,post = createPrePostSync [nameLeft,opeLeft] opeLeftList syncSet in
    (name,{nameOf = opeLeft.nameOf;
	   parameter = opeLeft.parameter;
	   preOf = pre;
	   postOf = post})::(modifyOperationsForSynchro tailLeft opeNonLeft syncSet name)

let createPrePostFork listLeft listRight syncList predicate = match (listLeft,listRight) with
  |[],_ -> failwith "Shouldn't Happend"
  |h1::h2::t,_ -> failwith "Shouldn't Happend"
  |_,h1::h2::t -> failwith "Shouldn't Happend"
  |[(nameLeft,opeLeft)],[] -> 
    if isInSyncSet opeLeft.nameOf syncList then
      failwith "Shouldn't Happend"
    else (opeLeft.preOf, Select ([(opeLeft.preOf,opeLeft.postOf)]))
  |[(nameLeft,opeLeft)],[(nameRight,opeRight)] ->
    if isInSyncSet opeLeft.nameOf syncList then
      (Implies(predicate,
	       And (opeLeft.preOf,
		    opeRight.preOf)),
       Parallel [opeLeft.postOf;opeRight.postOf])
    else
      (Or (opeLeft.preOf,
	   opeRight.preOf),
       Select [(opeLeft.preOf,opeLeft.postOf);
	       (opeRight.preOf,opeRight.postOf)])

let rec modifyOperationsForFork opeListLeft opeListRight syncSet name predicate = match (opeListLeft,opeListRight) with
  |[],[] -> []
  |[],(nameRight,opeRight)::tail ->
    if isInSyncSet opeRight.nameOf syncSet 
    then failwith "Shouldn't Happend"
    else
      (name,{nameOf = opeRight.nameOf;
	     parameter = opeRight.parameter;
	     preOf = opeRight.preOf;
	     postOf = Select ([(opeRight.preOf,opeRight.postOf)])})::
	modifyOperationsForFork opeListLeft tail syncSet name predicate
  |(nameLeft,opeLeft)::tailLeft,listRight ->
    let opeLeftList,opeNonLeft = seperateOperation opeLeft.nameOf listRight in
    let pre,post = createPrePostFork [nameLeft,opeLeft] opeLeftList syncSet predicate in
    (name,{nameOf = opeLeft.nameOf;
	   parameter = opeLeft.parameter;
	   preOf = pre;
	   postOf = post})::(modifyOperationsForFork tailLeft opeNonLeft syncSet name predicate)

let modifyOperationForQChoice name var listVar operation = 
  let nameSubAstd,ope = operation in
  let pre1 = And (Equality (Variable ("State_" ^ name),
			    Constant "notChosen"),
		  initPred (ope.preOf) listVar)
    and
      post1 = Parallel [Affectation (Variable ("State_" ^ name),
				     Constant "chosen");
			Affectation (Variable ("Value_" ^ name),
				     Variable var);
			initSub listVar (ope.postOf)]
    and
      pre2 = And (Equality (Variable ("State_" ^ name),
			    Constant "chosen"),
		  And (Equality (Variable var,
				 Variable ("Value_" ^ name)),
		       ope.preOf))
    and
      post2 = ope.postOf
  in
  let modifiedPreOf = Or (pre1,pre2)
  and modifiedPostOf = Select [(pre1,post1);(pre2,post2)] in
  (nameSubAstd,{nameOf = ope.nameOf;
		parameter = ope.parameter;
		preOf = modifiedPreOf;
		postOf = modifiedPostOf})

let quantifyLambdaAff var ovl = let (str1,pred,str2)=ovl in (str1,predMap (quantifiedVariable var) pred,str2)

let rec quantifyPost var set sub = match sub with
  |Select li -> Select (List.rev_map (quantifySelectCase var set) li)
  |Affectation (va1,va2) ->
    begin
      match va2 with
      |CartesianP li -> Affectation (va1,CartesianP (set::li))
      |_ -> Affectation (quantifiedVariable var va1,quantifiedVariable var va2)
    end
  |Parallel li -> Parallel (List.rev_map (quantifyPost var set) li)
  |AffectationLambda (var1,li) -> AffectationLambda (var::var1,List.rev_map (quantifyLambdaAff var) li)
  |CallB _ -> sub
  |Any (var1,pred,substitution) -> Any (var1,(predMap (quantifiedVariable var) pred),quantifyPost var set substitution)
and quantifySelectCase var set ca = let (pred,sub) = ca in
				(predMap (quantifiedVariable var) pred,quantifyPost var set sub)

let quantifiedOpe ope var domain =
  {nameOf = ope.nameOf;
   parameter = ope.parameter;
   preOf = predMap (quantifiedVariable var) ope.preOf;
   postOf = quantifyPost var domain ope.postOf}


let andPred pred casePred = let (bSet,pred1,sub) = casePred in
			    match pred1 with
			    |True -> (bSet,pred,sub)
			    |_ ->(bSet,And (pred,pred1),sub)

let rec getName var = match var with 
  |Variable str -> str
  |Constant str -> str
  |_-> failwith "no name"

let rec casePredicate sub = match sub with
  |Select li -> casePredicateSelect li
  |Affectation (bSet1,bSet2) -> [([getName bSet1],True,sub)]
  |Parallel li -> casePredicatePara li
  |AffectationLambda(var1,set) -> [var1,True,sub]
  |_ -> failwith "Fail Case Predicate"
and casePredicateSelect li = match li with
  |[] -> []
  |(pred,sub)::t -> (List.rev_map (andPred pred) (casePredicate sub)) @ (casePredicateSelect t)
and casePredicatePara li = match li with
  |[] -> []
  |h::t -> casePredicate h @ casePredicatePara t

(*
 This operation is used to regroup the variables. casePList is a list of list. Each element of the list contains all the cases where one variable is modified
 Arguments:
 - case : One modification case (a tuple (variable, predicate, elementary substitution))
 - casePList : A list of list of modification cases
 *)
					       
let rec addVarPreAffect case casePList = match casePList with
  |[] -> [case]::[]
  |(h::t)::st -> let (varC,predC,affC) = case and
		     (varH,predH,affH) = h in
		 if varH = varC then (case::h::t)::st
		 else (h::t)::(addVarPreAffect case st)
  |[]::_ -> failwith "Shouldn't add empty List"

let rec regroupByVariable caseP = match caseP with
  |[] -> []
  |h::t -> addVarPreAffect h (regroupByVariable t);;

let makeOvl varQ domainQ case ovl = 
  let (varC,pred,affect) = case in
  let (varO,li) = ovl in
  match affect with
  |Affectation (bSet1,bSet2) ->
    begin
      let cond= match pred with
	|True -> In (Constant varQ,Constant domainQ)
	|_ -> And (In (Constant varQ,Constant domainQ),pred)
      in
      match bSet2 with
      |Variable st -> (varO,(varQ,cond,st)::li)
      |Constant st -> (varO,(varQ,cond,st)::li)
      |_ -> failwith "bad Affectation"
    end
  |_ -> failwith "badSub"

let getVar caseP = match caseP with
  |[] -> failwith "noVar"
  |(var,pred,affect)::t -> var

let makeOneOvl varQ domainQ caseP =
  let varA = getVar caseP in
  let (var,li) = (List.fold_right (makeOvl varQ domainQ) caseP (varA,[])) in
  AffectationLambda (var,li)

let rec quantifyPostQSync var domain sub = match sub with
  |AffectationLambda (var1,li) -> AffectationLambda (var1,List.rev_map (quantifyLambdaAff var) li)
  |Parallel li -> Parallel (List.rev_map (quantifyPostQSync var domain) li)
  |_ -> failwith "An operation translated for QSync only contains AffectationLambda and Parallel"

		    
let modifyPostOfForQSync post var domain =
  quantifyPostQSync var domain (Parallel (List.rev_map (makeOneOvl var domain) (regroupByVariable (casePredicate post))))

let andPredicateAffectationLambdaElement pred1 element =
  let (str1,pred2,str2) = element in
  (str1,And (pred1,pred2),str2)

let makeOvlQFork varQ domainQ predicate case ovl = 
  let (varC,pred,affect) = case in
  let (varO,li) = ovl in
  match affect with
  |Affectation (bSet1,bSet2) ->
    let cond = match pred with
      |True -> And (In (Constant varQ, Constant domainQ),predicate)
      |_ -> And (In (Constant varQ,Constant domainQ),And(predicate,pred))
    in
    begin
      match bSet2 with
      |Variable st -> (varO,(varQ,cond,st)::li)
      |Constant st -> (varO,(varQ,cond,st)::li)
      |_ -> failwith "bad Affectation"
    end
  |_ -> failwith "badSub"

let makeOneOvlQFork varQ domainQ predicate caseP = 
  let varA = getVar caseP in
  let (var,li) = (List.fold_right (makeOvlQFork varQ domainQ predicate) caseP (varA,[])) in
  AffectationLambda (var,li)

let modifyPostOfForQFork post var domain predicate =
  quantifyPostQSync var domain (Parallel (List.rev_map (makeOneOvlQFork var domain predicate) (regroupByVariable (casePredicate post))))

let synchroOpe ope var domain =
  {nameOf = ope.nameOf;
   parameter = ope.parameter;
   preOf = Forall(var,
		  In (QVar var, Constant domain),
		  predMap (quantifiedVariable var) ope.preOf);
   postOf = modifyPostOfForQSync ope.postOf var domain}

let synchroOpeQFork ope var domain predicate_list =
  {nameOf = ope.nameOf;
   parameter = ope.parameter;
   preOf = Forall(var,
		  And(In (QVar var, Constant domain),
		      translatePredicateList predicate_list),
		  predMap (quantifiedVariable var) ope.preOf);
   postOf = modifyPostOfForQFork ope.postOf var domain (translatePredicateList predicate_list)}
    

let rec isAParameter var params = match params with
  |[] -> false
  |(param,typ)::q -> if param=var then true else isAParameter var q

let anyOpe ope var domain =
  let predicate = And(In (QVar var, Constant domain),
		      predMap (quantifiedVariable var) ope.preOf)
  in
  {nameOf = ope.nameOf;
   parameter = ope.parameter;
   preOf = 
     Exists(var,predicate);
   postOf = Any(var,
		predicate,
		quantifyPost var domain ope.postOf);}

let modifyOperationForQSync syncSet var domain ope = 
  let (name,ope) = ope in
  if isInSyncSet ope.nameOf syncSet then
    (name,synchroOpe ope var domain)
  else
    if (isAParameter var ope.parameter)
    then
      (name,quantifiedOpe ope var domain)
    else
      (name,anyOpe ope var domain)

let modifyOperationForQFork syncSet var domain predicate_list ope =
  let (name,ope) = ope in
  if isInSyncSet ope.nameOf syncSet then
    (name,synchroOpeQFork ope var domain predicate_list)
  else
    if (isAParameter var ope.parameter)
    then
      (name,quantifiedOpe ope var domain)
    else
      (name,anyOpe ope var domain)

(*match listOpe with
  |[] -> []
  |(name,ope)::opeListTail ->
    if isInSyncSet ope.nameOf syncSet then
      (name,synchroOpe ope var domain)::(modifyOperationForQSync opeListTail syncSet var domain)
    else
      (name,quantifiedOpe ope var)::(modifyOperationForQSync opeListTail syncSet var domain)
 *)	   

let rec addEnumerateSetToSetList nameOfSet valueListOfSet setList = match setList with
  |[] -> [nameOfSet,valueListOfSet]
  |(name,values)::t -> if name = nameOfSet then setList else (name,values)::(addEnumerateSetToSetList nameOfSet valueListOfSet t);;

let quantifiedInit domain init = match init with
  |AffectationInit (bSet1,bSet2) ->
    let newbSet2 =
      begin
	match bSet2 with
	|Variable str -> failwith "initialisation with a variable"
	|Constant str -> CartesianP [domain;str]
	|Function _ -> failwith "initialisation with a function"
	|EnumerateSet _ -> failwith "initialisation with an enumerate set"
	|CartesianP li -> CartesianP (domain::li)
	|QVar _ -> failwith "initialisation with a quantification variable"
      end
    in
    AffectationInit(bSet1,newbSet2)
  |AnyInit (str,pred,bSet1,bSet2) ->
    let newbSet2 = 
      begin
	match bSet2 with
	|Variable str -> failwith "initialisation with a variable"
	|Constant str -> CartesianP [domain;str]
	|Function _ -> failwith "initialisation with a function"
	|EnumerateSet _ -> failwith "initialisation with an enumerate set"
	|CartesianP li -> CartesianP (domain::li)
	|QVar _ -> failwith "initialisation with a quantification variable"
      end
    in AnyInit (str,pred,bSet1,newbSet2)

let modifyOperationForGuard gu name varList ope =
  let name,operation = ope in
  let pre1,post1 =
    (And (And (gu,
	       Equality (Variable ("State_" ^ name),
			 Constant ("notChecked"))),
	  initPred operation.preOf varList),
     Parallel [Affectation (Variable ("State_" ^ name),
			    Constant ("checked"));
	       initSub varList operation.postOf]) and
      pre2,post2 =
	(And (Equality (Variable ("State_" ^ name),
			Constant ("checked")),
	      operation.preOf),
	 operation.postOf) in
  name,{nameOf = operation.nameOf;
	parameter = operation.parameter;
	preOf = Or (pre1,pre2);
	postOf = Select ([(pre1,post1);(pre2,post2)]);}
	 
let quantifiedVariableInVarList domain elem = let (var,typ,init) = elem in 
					      (var,domain::typ,quantifiedInit domain init);;

let rec setListFusion listSet1 listSet2 = match listSet1 with
  |[] -> listSet2
  |(nameOfSet,valuesOfSet)::t -> setListFusion t (addEnumerateSetToSetList nameOfSet valuesOfSet listSet2)

let rec simpl_sub sub = match sub with
  |Select [gu,act] -> simpl_sub act
  |_ -> sub;;

let simpl simplOn op = match op with
  |name,operation ->
    (name,{nameOf = operation.nameOf;
	   parameter = operation.parameter;
	   preOf = operation.preOf;
	   postOf = if simplOn
		    then simpl_sub operation.postOf
		    else operation.postOf;})
					       
let rec translate_aux simplOn astd = match astd with
  |Elem _ -> ([],[],[])
  |Automata(name,state_list,transition_list,shallowFinal_list,deepFinal_list,initialState) ->
    let setList,varList,opeList = translateStateList simplOn state_list name in
    let opeListNew = addOperationFromTransitionList astd transition_list opeList varList in
    (setList,
     ("State_"^ name,
      ["AutState_" ^ name],
       AffectationInit (Variable ("State_" ^ name),
			Constant initialState))::varList,
      List.rev_map (simpl simplOn) opeListNew)
  |Sequence (name,astdFst,astdSnd) ->
    let setListFst,varListFst,opeListFst = translate_aux simplOn astdFst in
    let setListSnd,varListSnd,opeListSnd = translate_aux simplOn astdSnd in
    ((addEnumerateSetToSetList "SequenceState" ["fst";"snd"] (setListSnd@setListFst)),
     ("State_"^name,
      ["SequenceState"],
      AffectationInit (Variable ("State_" ^ name),
		       Constant "fst"))::(varListFst@varListSnd),
     List.rev_map (simpl simplOn)
		  (modifyOperationForSequence opeListFst opeListSnd name astdFst (varListFst@varListSnd)))
  |Choice (name,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux simplOn astdLeft and
	setListRight,varListRight,opeListRight = translate_aux simplOn astdRight in
    ((addEnumerateSetToSetList "ChoiceState" ["rightS";"leftS";"none"] (setListFusion setListLeft setListRight)),
     ("State_"^name,
      ["ChoiceState"],
      AffectationInit (Variable ("State_" ^ name),
		       Constant "none"))::(varListRight@varListLeft),
     List.rev_map (simpl simplOn)
		  (modifyOperationForChoice opeListLeft opeListRight name astdLeft (varListLeft@varListRight)))
  |Kleene (name,subAstd) ->
    let setList,varList,opeList = translate_aux simplOn subAstd in
    (addEnumerateSetToSetList "KleeneState" ["started";"notStarted"] setList,
     ("State_" ^ name,
      ["KleeneState"],
      AffectationInit (Variable ("State_" ^ name),
		       Constant "notStarted"))::varList,
     List.rev_map (simpl simplOn) (List.rev_map (modifyOperationForKleene name subAstd varList) opeList))
  |Synchronisation (name,syncList,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux simplOn astdLeft and
	setListRight,varListRight,opeListRight = translate_aux simplOn astdRight in
    (setListFusion setListRight setListLeft,
     varListRight@varListLeft,
     List.rev_map (simpl simplOn)
		  (modifyOperationsForSynchro opeListRight opeListLeft syncList name))
  |Fork (name,syncList,predicate_list,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux simplOn astdLeft and
	setListRight,varListRight,opeListRight = translate_aux simplOn astdRight in
    (setListFusion setListRight setListLeft,
     varListRight@varListLeft,
     List.rev_map (simpl simplOn)
		  (modifyOperationsForFork opeListRight opeListLeft syncList name (translatePredicateList predicate_list)))
  |QChoice (name,var,domain,subAstd) ->
    let setList,varList,opeList = translate_aux simplOn subAstd in
    (addEnumerateSetToSetList domain [] (addEnumerateSetToSetList "QChoiceSet" ["chosen";"notChosen"] setList),
     (("State_" ^ name,
       ["QChoiceSet"],
       AffectationInit (Variable ("State_" ^ name),
			Constant "notChosen"))::
	("Value_" ^ name,
	 [domain],
	 AnyInit ("xx",
		  In (Variable "xx",
		      Constant domain),
		  Variable ("Value_" ^ name),
		  Variable "xx"))::
	  varList),
     List.rev_map (simpl simplOn)
		  (List.rev_map (modifyOperationForQChoice name var varList) opeList))
  |QSynchronisation(name,var,domain,syncSetList,subAstd) ->
    let setList,varList,opeList = translate_aux simplOn subAstd in
    (setList,
     List.rev_map (quantifiedVariableInVarList domain) varList,
     List.rev_map (simpl simplOn)
		  (List.rev_map (modifyOperationForQSync syncSetList var domain) opeList))
  |QFork(name,var,domain,predicate_list,synchSetList,subAstd) ->
    let setList,varList,opeList = translate_aux simplOn subAstd in
    (setList,
     List.rev_map (quantifiedVariableInVarList domain) varList,
     List.rev_map (simpl simplOn)
		  (List.rev_map (modifyOperationForQFork synchSetList var domain predicate_list) opeList))
  |Guard(name,predicateList,subAstd) ->
    let setList,varList,opeList = translate_aux simplOn subAstd in
    (addEnumerateSetToSetList "guardState" ["checked";"notChecked"] setList,
     ("State_" ^ name,
      ["guardState"],
      AffectationInit (Variable ("State_" ^ name),
		       Constant "notChecked"))
     ::varList,
     List.rev_map (simpl simplOn)
		  (List.rev_map (modifyOperationForGuard (translatePredicateList predicateList) name varList) opeList))
and translateStateList simplOn stateList nameTranslatedAstd = match stateList with
  |h::t -> let (setListOfH,varListOfH,opeListOfH) = translate_aux simplOn h in
	   let (setListOfT,varListOfT,opeListOfT) = translateStateList simplOn t nameTranslatedAstd
	   in ((addStateToStateList (get_name h) nameTranslatedAstd (setListOfH@setListOfT)),varListOfH@varListOfT,opeListOfT@opeListOfH)
  |[] -> ([],[],[]);;

let rec getInfoFromVarList varList = match varList with
  |[] -> ([],[],[])
  |(name,invList,init)::t -> let nameList,invList_list,initList = getInfoFromVarList t in
			     (name::nameList,((name,invList)::invList_list),init::initList);;

let rec typeParameters param = match param with
  |[] -> raise NoParam
  |[param,typ] -> In (Variable param,
		      Constant typ)
  |(param,typ)::t -> And ( In (Variable param,
			       Constant typ),
			   typeParameters t)

let finalizeOpe nocalls op =
  {nameOf = op.nameOf;
   parameter = op.parameter;
   preOf =
     begin
       try And(typeParameters op.parameter,
	       op.preOf)
       with
       |NoParam -> op.preOf
     end;
   postOf =
     if nocalls
     then op.postOf
     else
       begin
	 match op.postOf with
	 |Parallel li -> Parallel (CallB ((op.nameOf ^ "_act"),List.map fst op.parameter)::li)
	 |_ -> Parallel [CallB ((op.nameOf ^ "_act"),List.map fst op.parameter);op.postOf]
       end;
  }

let translate astd name refine sees includes nocalls inv ass simpl =
  let setsList,varList,opeList = translate_aux simpl astd in
  let variables,invariants,initialisation=getInfoFromVarList varList in
  let machine = {machine = if refine="" then Machine name else (Refinement (name,refine));
		 sees = if sees="" then NoSeenMachine else SeenMachine sees;
		 includes = if includes="" then NoIncludedMachine else IncludedMachine includes;
		 sets = setsList;
		 variables = variables;
		 assertions = ass;
		 invariants = {typage = invariants;
			       invariantsPreuve = inv;};
		 init = initialisation;
		 operations = List.rev_map (finalizeOpe nocalls) (List.rev_map snd opeList)} in
  print_machine machine;;

