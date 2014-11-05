exception NotFound of string;;
exception InitIsAny of ASTD_B.predicateB;;
exception TrueGuard of ASTD_B.substitutionB;;

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
			if op.ASTD_B.nameOf = name
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
  |ASTD_astd.Elem nameElem -> if nameElem = name then astd else raise (NotFound name)
  |ASTD_astd.Automata (nameAut,stateList,_,_,_,_)-> if nameAut = name then astd else getAstdFromStateList name stateList
  |ASTD_astd.Kleene(nameKle,subAstd) -> if nameKle = name then astd else getAstdFromName name subAstd
and getAstdFromStateList name stateList = match stateList with
  |[] -> raise (NotFound name)
  |h::t -> try getAstdFromName name h with
    |NotFound _ -> getAstdFromStateList name t;;

(*
  This operation returns an affectation list representing the fact that we initialize all the state variables in the ASTD nameInitialState
  Arguments :
  - nameOfState : name of the state that we want to initialize
  - astd : the ASTD in which we initialize the state. This arguments is needed because we need to search for the ASTD corresponding to the state "nameOfState"
*)

let rec initializeAllVariable nameOfState astd = 
  let initialAstd = getAstdFromName nameOfState astd in match initialAstd with
    |ASTD_astd.Elem _ -> []
    |ASTD_astd.Automata (name,_,_,_,_,init) -> (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								    ASTD_B.Constant init))::(initializeAllVariable init astd)
    |ASTD_astd.Kleene(name,subAstd) -> (ASTD_B.Affectation (ASTD_B.Variable("State_" ^ name),
							    ASTD_B.Constant "notStarted"))::(initializeAllVariable (ASTD_astd.get_name subAstd) astd);;

let rec lastElem li = match li with
  |[] -> failwith "Empty list : no last elem"
  |[t] -> t
  |h::t -> lastElem t

let rec initValueOfVar listVar var1 =
  let name = match var1 with
    |ASTD_B.Constant str -> str
    |ASTD_B.Variable str -> str
    |ASTD_B.EnumerateSet li -> failwith "Not a Proper Variable"
    |ASTD_B.Function (name,param) -> name
  in
  match listVar with
  |[] -> name
  |(nameVar,typeList,valueVar)::t -> 
    if nameVar = name then
      begin
	match valueVar with
	| ASTD_B.AffectationInit (var1,var2) -> 
	  begin
	    match var2 with
	    | ASTD_B.Constant str -> str
	    | ASTD_B.Variable str -> failwith "initializing a Variable with a variable"
	    | ASTD_B.CartesianP li ->  lastElem li
	    | _ -> failwith "Unbound initial Value"
	  end
	| AnyInit (var,pred,_,_) -> raise (InitIsAny pred)
      end
    else initValueOfVar t (Variable name)



let rec initPredSimpl pred listVar = match pred with
  |ASTD_B.And (pred1,pred2) ->
    let initPredSimpl1 = initPredSimpl pred1 listVar and
	initPredSimpl2 = initPredSimpl pred2 listVar in
(*    ASTD_B.And (initPredSimpl1,initPredSimpl2)*)
   begin
      match initPredSimpl1,initPredSimpl2 with
      |(ASTD_B.False,_) -> ASTD_B.False
      |(ASTD_B.True,_) -> initPredSimpl2
      |(_,ASTD_B.True) -> initPredSimpl1
      |(_,ASTD_B.False) -> ASTD_B.False
      |(_,_) -> ASTD_B.And (initPredSimpl1, initPredSimpl2)
    end

(*    let initPredSimpl1 = initPredSimpl pred1 listVar in
    begin
      match initPredSimpl1 with
      |ASTD_B.True -> initPredSimpl pred2 listVar
      |ASTD_B.False -> ASTD_B.False
      |_ -> let initPredSimpl2 = initPredSimpl pred2 listVar in
	    begin
	      match initPredSimpl2 with
	      |ASTD_B.True -> initPredSimpl1
	      |ASTD_B.False -> ASTD_B.False
	      |_ -> ASTD_B.And (initPredSimpl1,initPredSimpl2)
	    end
    end*)
  |ASTD_B.Or (pred1,pred2) ->
    let initPredSimpl1 = initPredSimpl pred1 listVar and
	initPredSimpl2 = initPredSimpl pred2 listVar in
    begin
      match initPredSimpl1,initPredSimpl2 with
     |(ASTD_B.True,_) -> ASTD_B.True
      |(ASTD_B.False,_) -> initPredSimpl2
      |(_,ASTD_B.False) -> initPredSimpl1
      |(_,ASTD_B.True) -> ASTD_B.True
      |(_,_) -> ASTD_B.Or (initPredSimpl1, initPredSimpl2)
    end
  |ASTD_B.BPred s -> BPred s
  |ASTD_B.Equality (var1,val1) ->
    begin
      try
	let value1 = initValueOfVar listVar var1
	and value2 = ASTD_B.strOfValue val1 in
	if value1 = value2 then ASTD_B.True else ASTD_B.False
      with
      | InitIsAny pred -> pred
    end
  |ASTD_B.In (var1,val1) -> ASTD_B.In (ASTD_B.Constant (initValueOfVar listVar var1), val1)
  |ASTD_B.True -> ASTD_B.True
  |ASTD_B.Implies (pred1,pred2) -> ASTD_B.Implies (initPredSimpl pred1 listVar,initPredSimpl pred2 listVar)
  |ASTD_B.False -> ASTD_B.False
  |ASTD_B.Exists(var,predicate) -> 
    let initPredicate = initPredSimpl predicate listVar in
    begin
      match initPredicate with
      |ASTD_B.False -> ASTD_B.False
      |ASTD_B.True -> ASTD_B.True
      |_ -> ASTD_B.Exists(var, initPredicate)
    end
  |ASTD_B.Forall(var,pred1,pred2) ->
    let initPredicate2 = initPredSimpl pred2 listVar in
    begin
      match initPredicate2 with
      |ASTD_B.False -> ASTD_B.False
      |ASTD_B.True -> ASTD_B.True
      |_ -> ASTD_B.Forall (var,
			   initPredSimpl pred1 listVar,
			   initPredicate2)
    end
let rec initPredBrut pred listVar = match pred with
  |ASTD_B.And (pred1,pred2) ->
    let initPredBrut1 = initPredBrut pred1 listVar and
	initPredBrut2 = initPredBrut pred2 listVar in ASTD_B.And(initPredBrut1,initPredBrut2)
  |ASTD_B.Or (pred1,pred2) ->
    let initPredBrut1 = initPredBrut pred1 listVar and
	initPredBrut2 = initPredBrut pred2 listVar in
    ASTD_B.Or(initPredBrut1,initPredBrut2)
  |ASTD_B.BPred s -> BPred s
  |ASTD_B.Equality (var1,val1) ->
    begin
      try
	let value1 = initValueOfVar listVar var1
	and value2 = ASTD_B.strOfValue val1 in
	ASTD_B.Equality(ASTD_B.Constant value1,ASTD_B.Constant value2)
      with
      | InitIsAny pred -> pred
    end
  |ASTD_B.In (var1,val1) -> ASTD_B.In (ASTD_B.Constant (initValueOfVar listVar var1), val1)
  |ASTD_B.True -> ASTD_B.True
  |ASTD_B.Implies (pred1,pred2) -> ASTD_B.Implies (initPredBrut pred1 listVar,initPredBrut pred2 listVar)
  |ASTD_B.False -> ASTD_B.False

let initPred pred listVar = initPredSimpl pred listVar

let initPredAffectationLambdaElement listVar elem =
  let str1,pred,str2 = elem in
  str1,(initPred pred listVar),str2

let rec initSub sub listVar = match sub with
  |ASTD_B.Affectation (_,_) -> sub
  |ASTD_B.Select listSelect -> begin
			       try ASTD_B.Select (initSubSelectList listSelect listVar) with
			       |TrueGuard sub -> sub
			     end
  |ASTD_B.Parallel listPara -> ASTD_B.Parallel (initSubParaList listPara listVar)
  |ASTD_B.Call _ -> sub
  |ASTD_B.Any(string, pred, substit) ->
    let initSubstit = initSub substit listVar in
    begin
      match initSubstit with
      |Select [] -> Select []
      |_ -> ASTD_B.Any (string , initPred pred listVar, initSubstit)
    end
  |ASTD_B.AffectationLambda (var,li) -> ASTD_B.AffectationLambda (var,List.rev_map (initPredAffectationLambdaElement listVar) li)
 (* ASTD_B.Any (string,initPred pred listVar, initSub substit listVar) *)

and initSubSelectList listSelect listVar = match listSelect with
  |[] -> []
  |(gu,post)::t -> let initGu = initPred gu listVar in
		   begin
		     match initGu with
		     |ASTD_B.True -> raise (TrueGuard (initSub post listVar))
		     |ASTD_B.False -> initSubSelectList t listVar
		     |_ -> (initGu,initSub post listVar)::(initSubSelectList t listVar)
		   end
and initSubParaList listPara listVar = match listPara with
  |[] -> []
  |head::tail -> (initSub head listVar) :: (initSubParaList tail listVar)

let replaceVariable str1 str2 bSet = match bSet with 
  |ASTD_B.Variable var -> if var = str1 then ASTD_B.Variable str2 else bSet
  |_ -> bSet

let quantifiedVariable param bSet = match bSet with
  |ASTD_B.Constant c -> bSet
  |ASTD_B.Variable v -> Function (v,[param])
  |ASTD_B.Function (v,paramList) -> Function (v,param::paramList)
  |ASTD_B.EnumerateSet _ -> bSet

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
  |ASTD_astd.Elem e -> ASTD_B.True
  |ASTD_astd.Automata (name,_,_,sFinal,dFinal,_) -> 
    begin
      match sFinal,dFinal with
      |[],[] -> failwith "No Final State"
      |t::q,[] -> ASTD_B.In(ASTD_B.Variable ("State_" ^ name),
			    ASTD_B.EnumerateSet sFinal)
      |[],t::q -> ASTD_B.And(ASTD_B.In(ASTD_B.Variable ("State_"^name),
				       ASTD_B.EnumerateSet dFinal),
			     dFinalStateCond dFinal astd listVar)
      |t1::q1,t2::q2 -> (ASTD_B.Or(ASTD_B.In(ASTD_B.Variable ("State_" ^ name),
					     ASTD_B.EnumerateSet sFinal),
				   ASTD_B.In(ASTD_B.Variable ("State_"^name),
					     ASTD_B.EnumerateSet dFinal)))
    end
  |ASTD_astd.Sequence (name,astdFst,astdSnd) -> ASTD_B.And (final astdSnd listVar,
							    Implies (Equality (Variable ("State_" ^ name),
									       Constant "fst"),
								     final astdFst listVar))
  |ASTD_astd.Choice(name,astdLeft,astdRight) -> 
    ASTD_B.And (ASTD_B.Implies (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						 ASTD_B.Constant "none"),
				ASTD_B.Or (initPred (final astdLeft listVar) listVar,
					   initPred (final astdRight listVar) listVar)),
		ASTD_B.And (ASTD_B.Implies (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
							     ASTD_B.Constant "leftS"),
					    final astdLeft listVar),
			    ASTD_B.Implies (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
							     ASTD_B.Constant "rightS"),
					    final astdRight listVar)))
  |ASTD_astd.Kleene(name,subAstd) -> ASTD_B.Or (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
								  ASTD_B.Constant "notStarted"),
						 final subAstd listVar)
  |ASTD_astd.Synchronisation (name,labelList,astdLeft,astdRight) ->
    ASTD_B.And (final astdLeft listVar,
		final astdRight listVar)
  |ASTD_astd.QChoice (name,var,domain,subAstd) -> 
    ASTD_B.And (ASTD_B.Implies (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						 ASTD_B.Constant "notChosen"),
				ASTD_B.Exists ("vv",
					       ASTD_B.And (ASTD_B.In (ASTD_B.Constant "vv",
								      ASTD_B.Constant domain),
							   ASTD_B.predMap (replaceVariable var "vv") (initPred (final subAstd listVar) listVar)))),
		ASTD_B.Implies (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						 ASTD_B.Constant "chosen"),
				ASTD_B.predMap (replaceVariable var "vv") (final subAstd listVar)))
  |ASTD_astd.QSynchronisation(name,var,domain,_,subAstd) ->
    Forall(var,(In(Variable var,Constant domain)),ASTD_B.predMap (quantifiedVariable var) (final subAstd listVar))
  |ASTD_astd.Fork (name,var,domain,_,predicate,subAstd) ->
    Forall(var,(In(Variable var,Constant domain)),ASTD_B.predMap (quantifiedVariable var) (final subAstd listVar))
and dFinalStateCond dFinal astd listVar = match dFinal with
  |[] -> failwith "No DFinal State"
  |[t] -> ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
					  ASTD_B.Constant t),
			  final (getAstdFromName t astd) listVar)
  |t::q -> ASTD_B.And(ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
						      ASTD_B.Constant t),
				      final (getAstdFromName t astd) listVar),
		      dFinalStateCond q astd listVar);;

(*
  This operation Translate the list of predicate in the guard of the ASTD into a B predicate.
  Argument :
  - astdPredicate : The astd predicate we want to translate
*)

let rec translatePredicateList astdPredicate = match astdPredicate with
  |[] -> ASTD_B.True
  |[t] -> 
    begin
      match t with
      |ASTD_predicate.IASTDPredicate _ -> failwith "This predicate is not supported"
      |ASTD_predicate.BPredicate str -> ASTD_B.BPred str
    end
  |h::t ->
    begin
      match h with
      |ASTD_predicate.IASTDPredicate _ -> failwith "This predicate is not supported"
      |ASTD_predicate.BPredicate str -> ASTD_B.And(ASTD_B.BPred str,translatePredicateList astdPredicate)
    end

(*
  This operation transform an arrow into a couple (precondition, postcondition). The precondition is a B predicate corresponding to the preOf of the function. The postcondition is a substitution corresponding to the thenOf of the function.
  Arguments :
  - translatedAstd : the ASTD we are translating
  - transition : the arrow we are translating
*)

let transformTransition translatedAstd listVar transition= 
  let name = ASTD_astd.get_name translatedAstd
  in match transition with
  |ASTD_arrow.Local(fromState,toState,astdTransition,astdPredicate,finale) ->
    ((let cAll = (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),
				   ASTD_B.Constant fromState))
      in let preOf = (if finale 
	then (ASTD_B.And(cAll,
			 final (getAstdFromName fromState translatedAstd) listVar))
	else cAll)
	 in
	 let gu = translatePredicateList astdPredicate in
	 if gu = ASTD_B.True then preOf
	 else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Constant toState))
     in ASTD_B.Parallel (tAll::(initializeAllVariable toState translatedAstd)))
  |ASTD_arrow.From_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
    ((let cAll = (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),
				   ASTD_B.Constant throughState))
      in let cFromSub = ASTD_B.Equality(ASTD_B.Variable("State_" ^ throughState),
					ASTD_B.Constant fromState)
	 in let preOf = (if finale
	   then (ASTD_B.And(ASTD_B.And(cAll,cFromSub),
			    final (getAstdFromName fromState translatedAstd) listVar))
	   else ASTD_B.And(cAll,cFromSub))
	    in
	    let gu = translatePredicateList astdPredicate in
	    if gu = ASTD_B.True then preOf
	    else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Constant toState))
     in ASTD_B.Parallel (tAll::(initializeAllVariable toState translatedAstd)))  
  |ASTD_arrow.To_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
    ((let cAll = ASTD_B.Equality(ASTD_B.Variable("State_" ^ name),
				 ASTD_B.Constant fromState)
      in let preOf = (if finale
	then (ASTD_B.And(cAll,
			 final (getAstdFromName fromState translatedAstd) listVar))
	else cAll)
	 in
	 let gu = translatePredicateList astdPredicate in
	 if gu = ASTD_B.True then preOf
	 else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Constant throughState))
     in let tToSub = (ASTD_B.Affectation (ASTD_B.Variable("State_" ^ throughState),
					  ASTD_B.Constant toState))
	in
	begin
	  match toState with
	  |"H1" -> ASTD_B.Parallel (tAll::(initializeAllVariable throughState translatedAstd))
	  |"H2" -> ASTD_B.Parallel ([tAll])
	  |_ -> ASTD_B.Parallel (tAll::tToSub::(initializeAllVariable toState translatedAstd))
	end)

(*
  This fuction returns the conjunction of the preconditions of the operations in the subList
  Arguments :
  - subList : The list of the operations
*)

let rec getPreOf subList = match subList with
  |[] -> failwith "fail preOf"
  |[(gu,act)] -> gu
  |(gu,act)::t -> ASTD_B.Or (gu, getPreOf t);;



let transformSubOperation name elem = 
  let (name1,operation) = elem in
  (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
				ASTD_B.Constant name1),
	       operation.ASTD_B.preOf),
   operation.ASTD_B.postOf);;

(*
  This operation transform the list of transition in operations, and merges it with the list of allready translated operations. It takes 5 arguments :
  - astd : The current translated astd
  - nameOperation : The name of the operation
  - hOperationList : The list of operations translated in the subAstd
  - hTransitionList : The transition list of the ASTD labelled with nameOperatoin
  - translatedAstd : The global translated Astd
*)

let merge astd nameOperation hOperationList hTransitionList listVar param=
  let subList = ((List.rev_map (transformTransition astd listVar) hTransitionList)@(List.rev_map (transformSubOperation (ASTD_astd.get_name astd)) hOperationList))
  in let preOf = getPreOf subList
     in (ASTD_astd.get_name astd,{ASTD_B.nameOf = nameOperation;
				  ASTD_B.parameter =param;
				  ASTD_B.preOf=preOf;
				  ASTD_B.postOf=ASTD_B.Select subList});;
 
let rec toStringParamList param = match param with
  |[] -> []
  |h::t -> match h with
    |ASTD_term.Var s -> s::(toStringParamList t)
    |_ -> failwith "Unbound Parameter"

let rec getParamFromTransition h = 
  match h with
  |ASTD_transition.Transition (name,param) -> toStringParamList param

let modifyOperationOfSubAstd astd ope =
  let name = ASTD_astd.get_name astd in
  let (nameOpe,opeOpe) = ope in
  (name,{ASTD_B.nameOf = opeOpe.ASTD_B.nameOf;
	 ASTD_B.parameter = opeOpe.ASTD_B.parameter;
	 ASTD_B.preOf = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						     ASTD_B.Constant nameOpe),
				    opeOpe.preOf);
	 ASTD_B.postOf = ASTD_B.Select [(ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						     ASTD_B.Constant nameOpe),
				    opeOpe.preOf),
					 opeOpe.postOf)]})

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
    let pre1 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "fst"), 
			    opeFst.ASTD_B.preOf )) in
    (pre1,
     ASTD_B.Select [(pre1,opeFst.ASTD_B.postOf)])
  |[nameFst,opeFst],[nameSnd,opeSnd] -> 
    let pre1,pre2,pre3 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
						       ASTD_B.Variable "fst"), 
				      opeFst.ASTD_B.preOf ),
			  ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						       ASTD_B.Variable "snd"),
				      ASTD_B.And (final astdFst varList,initPred opeSnd.ASTD_B.preOf varList)), 
			  ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						       ASTD_B.Variable "snd"),
				      opeSnd.ASTD_B.preOf))
    in
    (ASTD_B.Or(ASTD_B.Or (pre1,pre2),pre3),
     ASTD_B.Select [(pre1,opeFst.ASTD_B.postOf);
		    (pre2,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "snd"));
					   initSub (opeSnd.ASTD_B.postOf) varList]);
		    (pre3,opeSnd.ASTD_B.postOf)])
  |[],[nameSnd,opeSnd] ->
    let pre2,pre3 = (
      ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
				   ASTD_B.Variable "snd"),
		  ASTD_B.And (final astdFst varList,initPred opeSnd.ASTD_B.preOf varList)), 
      ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
				   ASTD_B.Variable "snd"),
		  opeSnd.ASTD_B.preOf))
    in
    (ASTD_B.Or(pre2,pre3),
     ASTD_B.Select [(pre2,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "snd"));
					   initSub (opeSnd.ASTD_B.postOf) varList]);
		    (pre3,opeSnd.ASTD_B.postOf)])

let rec modifyOperationForSequence listFst listSnd name astdFst varList = match (listFst,listSnd) with
  |[],[] -> []
  |[],(hSnd::tSnd) -> 
    let (nameSnd,opeSnd) = hSnd in
    let pre,post = createPrePostSeq [] [hSnd] name astdFst varList in
    (name,{ASTD_B.nameOf = opeSnd.ASTD_B.nameOf;
	   ASTD_B.parameter = opeSnd.ASTD_B.parameter;
	   ASTD_B.preOf=pre;
	   ASTD_B.postOf=post})::(modifyOperationForSequence listFst tSnd name astdFst varList)   
  |((hFst::tFst),listSnd) ->
    let (nameFst,opeFst) = hFst in
    let opeFstList,opeNonFst = seperateOperation opeFst.ASTD_B.nameOf listSnd in 
    let pre,post = createPrePostSeq [hFst] opeFstList name astdFst varList in
    (name,{ASTD_B.nameOf = opeFst.ASTD_B.nameOf;
	   ASTD_B.parameter = opeFst.ASTD_B.parameter;
	   ASTD_B.preOf=pre;
	   ASTD_B.postOf=post})::(modifyOperationForSequence tFst opeNonFst name astdFst varList)

let createPrePostChoice lOpeLeft lOpeRight name astdLeft varList= match (lOpeLeft,lOpeRight) with
  |_,h1::h2::t -> failwith "Shouln't Happend"
  |h1::h2::t,_ -> failwith "Shouln't Happend"
  |[],[] -> failwith "Shouldn't Happend"
  |[(nameLeft,opeLeft)],[] ->
    let pre1 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "none"), 
			    initPred opeLeft.ASTD_B.preOf varList )) and
	pre3 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "leftS"), 
			    opeLeft.ASTD_B.preOf))
    in
    (ASTD_B.Or (pre1,pre3),
     ASTD_B.Select [(pre1,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "leftS"));
					   initSub (opeLeft.ASTD_B.postOf) varList]);
		    (pre3,opeLeft.ASTD_B.postOf)])
  |[nameLeft,opeLeft],[nameRight,opeRight] -> 
    let pre1 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "none"), 
			    initPred opeLeft.ASTD_B.preOf varList)) and
	pre2 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "none"), 
			    initPred opeRight.ASTD_B.preOf varList)) and
	pre3 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "leftS"), 
			    opeLeft.ASTD_B.preOf)) and
	pre4 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "rightS"), 
			    opeRight.ASTD_B.preOf)) in
    (ASTD_B.Or (ASTD_B.Or (pre1,pre2),ASTD_B.Or (pre3,pre4)),
     ASTD_B.Select [(pre1,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "leftS"));
					   initSub (opeLeft.ASTD_B.postOf) varList]);
		    (pre2,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "rightS"));
					   initSub (opeRight.ASTD_B.postOf) varList]);
		    (pre3,opeLeft.ASTD_B.postOf);
		    (pre4,opeRight.ASTD_B.postOf)])
  |[],[nameRight,opeRight] ->
    let pre2 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "none"), 
			    initPred opeRight.ASTD_B.preOf varList )) and
	pre4 = (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), 
					     ASTD_B.Variable "rightS"), 
			    opeRight.ASTD_B.preOf))
    in
    (ASTD_B.Or (pre2,pre4),
     ASTD_B.Select [(pre2,ASTD_B.Parallel [(ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								ASTD_B.Constant "rightS"));
					   initSub (opeRight.ASTD_B.postOf) varList]);
		    (pre4,opeRight.ASTD_B.postOf)])


let rec modifyOperationForChoice listLeft listRight name astdLeft varList = match (listLeft,listRight) with
  |[],[] -> []
  |[],(hRight::tRight) -> 
    let (nameRight,opeRight) = hRight in
    let pre,post = createPrePostChoice [] [hRight] name astdLeft varList in
    (name,{ASTD_B.nameOf = opeRight.ASTD_B.nameOf;
	   ASTD_B.parameter = opeRight.ASTD_B.parameter;
	   ASTD_B.preOf=pre;
	   ASTD_B.postOf=post})::(modifyOperationForChoice listLeft tRight name astdLeft varList)   
  |((hLeft::tLeft),listLeft) ->
    let (nameLeft,opeLeft) = hLeft in
    let opeLeftList,opeNonLeft = seperateOperation opeLeft.ASTD_B.nameOf listRight in 
    let pre,post = createPrePostChoice [hLeft] opeLeftList name astdLeft varList in
    (name,{ASTD_B.nameOf = opeLeft.ASTD_B.nameOf;
	   ASTD_B.parameter = opeLeft.ASTD_B.parameter;
	   ASTD_B.preOf=pre;
	   ASTD_B.postOf=post})::(modifyOperationForChoice tLeft opeNonLeft name astdLeft varList)

let rec modifyOperationForKleene name subAstd varList ope =
  let (nameOpe,opeOpe) = ope in
  let pre1 = let initPreOf = initPred (opeOpe.ASTD_B.preOf) varList and
		 finalSub = ASTD_B.Or (final subAstd varList,
				       ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
							ASTD_B.Constant "notStarted"))
	     in
	     begin
	       match initPreOf with
	       |ASTD_B.True -> finalSub
	       |_-> ASTD_B.And(finalSub,initPreOf)
	     end and

      (* ASTD_B.And (ASTD_B.Or (final subAstd varList, *)
      (* 				      ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), *)
      (* 						       ASTD_B.Constant "notStarted")), *)
      (* 			   initPred (opeOpe.ASTD_B.preOf) varList) and *)
      pre2 = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
					  ASTD_B.Constant "started"),
			 opeOpe.ASTD_B.preOf) in
  let post = ASTD_B.Select [pre1, ASTD_B.Parallel [ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
								       ASTD_B.Constant "started");
						   initSub (opeOpe.ASTD_B.postOf) varList];
			    pre2, opeOpe.ASTD_B.postOf] in
  (name,{ASTD_B.nameOf = opeOpe.ASTD_B.nameOf;
	 ASTD_B.parameter = opeOpe.ASTD_B.parameter;
	 ASTD_B.preOf = ASTD_B.simplifyPred (ASTD_B.Or (pre1,pre2));
	 ASTD_B.postOf = ASTD_B.simplifySub post});;
 (* match listOpe with *)
 (*  |[] -> [] *)
 (*  |(nameOpe,opeOpe)::t -> *)
 (*    let pre1 = let initPreOf = initPred (opeOpe.ASTD_B.preOf) varList and *)
 (* 		   finalSub = ASTD_B.Or (final subAstd varList, *)
 (* 					 ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), *)
 (* 							  ASTD_B.Constant "notStarted")) *)
 (* 	       in *)
 (* 	       begin *)
 (* 		 match initPreOf with *)
 (* 		 |ASTD_B.True -> finalSub *)
 (* 		 |_-> ASTD_B.And(finalSub,initPreOf) *)
 (* 	       end and *)

 (*      (\* ASTD_B.And (ASTD_B.Or (final subAstd varList, *\) *)
 (*      (\* 				      ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), *\) *)
 (*      (\* 						       ASTD_B.Constant "notStarted")), *\) *)
 (*      (\* 			   initPred (opeOpe.ASTD_B.preOf) varList) and *\) *)
 (* 	pre2 = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name), *)
 (* 					    ASTD_B.Constant "started"), *)
 (* 			   opeOpe.ASTD_B.preOf) in *)
 (*    let post = ASTD_B.Select [pre1, ASTD_B.Parallel [ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name), *)
 (* 									 ASTD_B.Constant "started"); *)
 (* 						     initSub (opeOpe.ASTD_B.postOf) varList]; *)
 (* 			      pre2, opeOpe.ASTD_B.postOf] in *)
 (*    (name,{ASTD_B.nameOf = opeOpe.ASTD_B.nameOf; *)
 (* 	   ASTD_B.parameter = opeOpe.ASTD_B.parameter; *)
 (* 	   ASTD_B.preOf = ASTD_B.simplifyPred (ASTD_B.Or (pre1,pre2)); *)
 (* 	   ASTD_B.postOf = ASTD_B.simplifySub post})::(modifyOperationsForKleene t name subAstd varList);; *)

let rec isInSyncSet name syncList = match syncList with
  |[] -> false
  |h::t -> (h = name) || isInSyncSet name t;;

let createPrePostSync listLeft listRight syncList = match (listLeft,listRight) with
  |[],_ -> failwith "Shouldn't Happend"
  |h1::h2::t,_ -> failwith "Shouldn't Happend"
  |_,h1::h2::t -> failwith "Shouldn't Happend"
  |[(nameLeft,opeLeft)],[] -> 
    if isInSyncSet opeLeft.ASTD_B.nameOf syncList then
      failwith "Shouldn't Happend"
    else (opeLeft.ASTD_B.preOf, ASTD_B.Select ([(opeLeft.ASTD_B.preOf,opeLeft.ASTD_B.postOf)]))
  |[(nameLeft,opeLeft)],[(nameRight,opeRight)] ->
    if isInSyncSet opeLeft.ASTD_B.nameOf syncList then
      (ASTD_B.And (opeLeft.ASTD_B.preOf,
		   opeRight.ASTD_B.preOf),
       ASTD_B.Parallel [opeLeft.ASTD_B.postOf;opeRight.ASTD_B.postOf])
    else
      (ASTD_B.Or (opeLeft.ASTD_B.preOf,
		  opeRight.ASTD_B.preOf),
       ASTD_B.Select [(opeLeft.ASTD_B.preOf,opeLeft.ASTD_B.postOf);
		      (opeRight.ASTD_B.preOf,opeRight.ASTD_B.postOf)])

let rec modifyOperationsForSynchro opeListLeft opeListRight syncSet name = match (opeListLeft,opeListRight) with
  |[],[] -> []
  |[],(nameRight,opeRight)::tail ->
    if isInSyncSet opeRight.ASTD_B.nameOf syncSet 
    then failwith "Shouldn't Happend"
    else
      (name,{ASTD_B.nameOf = opeRight.ASTD_B.nameOf;
	     ASTD_B.parameter = opeRight.ASTD_B.parameter;
	     ASTD_B.preOf = opeRight.ASTD_B.preOf;
	     ASTD_B.postOf = Select ([(opeRight.ASTD_B.preOf,opeRight.ASTD_B.postOf)])})::
	modifyOperationsForSynchro opeListLeft tail syncSet name
  |(nameLeft,opeLeft)::tailLeft,listRight ->
    let opeLeftList,opeNonLeft = seperateOperation opeLeft.ASTD_B.nameOf listRight in
    let pre,post = createPrePostSync [nameLeft,opeLeft] opeLeftList syncSet in
    (name,{ASTD_B.nameOf = opeLeft.ASTD_B.nameOf;
	   ASTD_B.parameter = opeLeft.ASTD_B.parameter;
	   ASTD_B.preOf = pre;
	   ASTD_B.postOf = post})::(modifyOperationsForSynchro tailLeft opeNonLeft syncSet name)

let modifyOperationForQChoice name var listVar operation = 
  let nameSubAstd,ope = operation in
  let pre1 = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
					  ASTD_B.Constant "notChosen"),
			 initPred (ope.ASTD_B.preOf) listVar)
  and
      post1 = ASTD_B.Parallel [ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
						   ASTD_B.Constant "chosen");
			       ASTD_B.Affectation (ASTD_B.Variable ("Value_" ^ name),
						   ASTD_B.Variable var);
			       initSub (ope.ASTD_B.postOf) listVar]
  and
      pre2 = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
					  ASTD_B.Constant "chosen"),
			 ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable var,
						      ASTD_B.Variable ("Value_" ^ name)),
				     ope.ASTD_B.preOf))
  and
      post2 = ope.ASTD_B.postOf
  in
  let modifiedPreOf = ASTD_B.Or (pre1,pre2)
  and modifiedPostOf = ASTD_B.Select [(pre1,post1);(pre2,post2)] in
  (nameSubAstd,{ASTD_B.nameOf = ope.ASTD_B.nameOf;
		ASTD_B.parameter = ope.ASTD_B.parameter;
		ASTD_B.preOf = modifiedPreOf;
		ASTD_B.postOf = modifiedPostOf})

let quantifyLambdaAff var ovl = let (str1,pred,str2)=ovl in (str1,ASTD_B.predMap (quantifiedVariable var) pred,str2)

let rec quantifyPost var sub = match sub with
  |ASTD_B.Select li -> ASTD_B.Select (List.rev_map (quantifySelectCase var) li)
  |ASTD_B.Affectation (va1,va2) -> ASTD_B.Affectation (quantifiedVariable var va1,quantifiedVariable var va2)
  |ASTD_B.Parallel li -> ASTD_B.Parallel (List.rev_map (quantifyPost var) li)
  |ASTD_B.AffectationLambda (var1,li) -> ASTD_B.AffectationLambda (var1,List.rev_map (quantifyLambdaAff var) li)
and quantifySelectCase var ca = let (pred,sub) = ca in
				(ASTD_B.predMap (quantifiedVariable var) pred,quantifyPost var sub)

let quantifiedOpe ope var domain =
  {ASTD_B.nameOf = ope.ASTD_B.nameOf;
   ASTD_B.parameter = ope.ASTD_B.parameter;
   ASTD_B.preOf = ASTD_B.And (ASTD_B.In (Variable var,Constant domain),
			      ASTD_B.predMap (quantifiedVariable var) ope.ASTD_B.preOf);
   ASTD_B.postOf = quantifyPost var ope.ASTD_B.postOf}


let andPred pred casePred = let (bSet,pred1,sub) = casePred in
			    match pred1 with
			    |ASTD_B.True -> (bSet,pred,sub)
			    |_ ->(bSet,ASTD_B.And (pred,pred1),sub)

let rec getName var = match var with 
  |ASTD_B.Variable str -> str
  |ASTD_B.Constant str -> str
  |_-> failwith "no name"

let rec casePredicate sub = match sub with
  |ASTD_B.Select li -> casePredicateSelect li
  |ASTD_B.Affectation (bSet1,bSet2) -> [(getName bSet1,ASTD_B.True,sub)]
  |ASTD_B.Parallel li -> casePredicatePara li
and casePredicateSelect li = match li with
  |[] -> []
  |(pred,sub)::t -> (List.rev_map (andPred pred) (casePredicate sub)) @ (casePredicateSelect t)
and casePredicatePara li = match li with
  |[] -> []
  |h::t -> casePredicate h @ casePredicatePara t

let rec addVarPreAffect case casePList = match casePList with
  |[] -> [case]::[]
  |(h::t)::st -> let (varC,predC,affC) = case and
      (varH,predH,affH) = h in
		 if varH = varC then (case::h::t)::st
		 else (h::t)::(addVarPreAffect case st)

let rec regroupByVariable caseP = match caseP with
  |[] -> []
  |h::t -> addVarPreAffect h (regroupByVariable t);;

let makeOvl varQ domainQ case ovl = 
  let (varC,pred,affect) = case in
  let (varO,li) = ovl in
  match affect with
  |ASTD_B.Affectation (bSet1,bSet2) ->
    begin
      match bSet2 with
      |ASTD_B.Variable st -> (varO,(varQ,ASTD_B.And (In (Constant varQ,Constant domainQ),pred),st)::li)
      |ASTD_B.Constant st -> (varO,(varQ,ASTD_B.And (In (Constant varQ,Constant domainQ),pred),st)::li)
      |_ -> failwith "bad Affectation"
    end
  |_ -> failwith "badSub"

let getVar caseP = match caseP with
  |[] -> failwith "noVar"
  |(var,pred,affect)::t -> var

let makeOneOvl varQ domainQ caseP =
  let varA = getVar caseP in
  let (var,li) = (List.fold_right (makeOvl varQ domainQ) caseP (varA,[])) in
  ASTD_B.AffectationLambda (var,li)

let modifyPostOfForQSync post var domain =
  quantifyPost var (ASTD_B.Parallel (List.rev_map (makeOneOvl var domain) (regroupByVariable (casePredicate post))))

let andPredicateAffectationLambdaElement pred1 element =
  let (str1,pred2,str2) = element in
  (str1,ASTD_B.And (pred1,pred2),str2)

let makeOvlFork varQ domainQ predicate case ovl = 
  let (varC,pred,affect) = case in
  let (varO,li) = ovl in
  match affect with
  |ASTD_B.Affectation (bSet1,bSet2) ->
    begin
      match bSet2 with
      |ASTD_B.Variable st -> (varO,(varQ,ASTD_B.And (In (Constant varQ,Constant domainQ),ASTD_B.And(predicate,pred)),st)::li)
      |ASTD_B.Constant st -> (varO,(varQ,ASTD_B.And (In (Constant varQ,Constant domainQ),ASTD_B.And(predicate,pred)),st)::li)
      |_ -> failwith "bad Affectation"
    end
  |_ -> failwith "badSub"

let makeOneOvlFork varQ domainQ predicate caseP = 
  let varA = getVar caseP in
  let (var,li) = (List.fold_right (makeOvlFork varQ domainQ predicate) caseP (varA,[])) in
  ASTD_B.AffectationLambda (var,li)

let modifyPostOfForFork post var domain predicate =
  quantifyPost var (ASTD_B.Parallel (List.rev_map (makeOneOvlFork var domain predicate) (regroupByVariable (casePredicate post))))

let synchroOpe ope var domain =
  {ASTD_B.nameOf = ope.ASTD_B.nameOf;
   ASTD_B.parameter = ope.ASTD_B.parameter;
   ASTD_B.preOf = Forall(var,
			 In (Variable var, Constant domain),
			 ASTD_B.predMap (quantifiedVariable var) ope.ASTD_B.preOf);
   ASTD_B.postOf = modifyPostOfForQSync ope.ASTD_B.postOf var domain}

let synchroOpeFork ope var domain predicate_list =
  {ASTD_B.nameOf = ope.ASTD_B.nameOf;
   ASTD_B.parameter = ope.ASTD_B.parameter;
   ASTD_B.preOf = Forall(var,
			 ASTD_B.And(In (Variable var, Constant domain),
				    translatePredicateList predicate_list),
			 ASTD_B.predMap (quantifiedVariable var) ope.ASTD_B.preOf);
   ASTD_B.postOf = modifyPostOfForFork ope.ASTD_B.postOf var domain (translatePredicateList predicate_list)}
			 

let rec isAParameter var params = match params with
  |[] -> false
  |t::q -> if t=var then true else isAParameter var q

let anyOpe ope var domain =
  let predicate = ASTD_B.And(ASTD_B.In (Variable var, Constant domain),
			     ASTD_B.predMap (quantifiedVariable var) ope.ASTD_B.preOf)
  in
  {ASTD_B.nameOf = ope.ASTD_B.nameOf;
   ASTD_B.parameter = ope.ASTD_B.parameter;
   ASTD_B.preOf = 
     ASTD_B.Exists(var,predicate);
   ASTD_B.postOf = ASTD_B.Any(var,
			      predicate,
			      quantifyPost var ope.ASTD_B.postOf);}

let modifyOperationForQSync syncSet var domain ope = 
  let (name,ope) = ope in
  if isInSyncSet ope.ASTD_B.nameOf syncSet then
    (name,synchroOpe ope var domain)
  else
    if (isAParameter var ope.parameter)
    then
      (name,quantifiedOpe ope var domain)
    else
      (name,anyOpe ope var domain)

let modifyOperationForFork syncSet var domain predicate_list ope =
  let (name,ope) = ope in
  if isInSyncSet ope.ASTD_B.nameOf syncSet then
  (name,synchroOpeFork ope var domain predicate_list)
   else
    if (isAParameter var ope.parameter)
    then
      (name,quantifiedOpe ope var domain)
    else
      (name,anyOpe ope var domain)

(*match listOpe with
  |[] -> []
  |(name,ope)::opeListTail ->
    if isInSyncSet ope.ASTD_B.nameOf syncSet then
      (name,synchroOpe ope var domain)::(modifyOperationForQSync opeListTail syncSet var domain)
    else
      (name,quantifiedOpe ope var)::(modifyOperationForQSync opeListTail syncSet var domain)
*)	   

let rec addEnumerateSetToSetList nameOfSet valueListOfSet setList = match setList with
  |[] -> [nameOfSet,valueListOfSet]
  |(name,values)::t -> if name = nameOfSet then setList else (name,values)::(addEnumerateSetToSetList nameOfSet valueListOfSet t);;

let quantifiedInit domain init = match init with
  |ASTD_B.AffectationInit (bSet1,bSet2) ->
    let newbSet2 =
    begin
      match bSet2 with
      |ASTD_B.Variable str -> failwith "initialisation with a variable"
      |ASTD_B.Constant str -> ASTD_B.CartesianP [domain;str]
      |ASTD_B.Function _ -> failwith "initialisation with a function"
      |ASTD_B.EnumerateSet _ -> failwith "initialisation with an enumerate set"
      |ASTD_B.CartesianP li -> ASTD_B.CartesianP (domain::li)
    end
    in
    ASTD_B.AffectationInit(bSet1,newbSet2)
  |ASTD_B.AnyInit (str,pred,bSet1,bSet2) ->
    let newbSet2 = 
    begin
      match bSet2 with
      |ASTD_B.Variable str -> failwith "initialisation with a variable"
      |ASTD_B.Constant str -> ASTD_B.CartesianP [domain;str]
      |ASTD_B.Function _ -> failwith "initialisation with a function"
      |ASTD_B.EnumerateSet _ -> failwith "initialisation with an enumerate set"
      |ASTD_B.CartesianP li -> ASTD_B.CartesianP (domain::li)
    end
    in ASTD_B.AnyInit (str,pred,bSet1,newbSet2)

let quantifiedVariableInVarList domain elem = let (var,typ,init) = elem in 
				     (var,domain::typ,quantifiedInit domain init);;

let rec setListFusion listSet1 listSet2 = match listSet1 with
  |[] -> listSet2
  |(nameOfSet,valuesOfSet)::t -> setListFusion t (addEnumerateSetToSetList nameOfSet valuesOfSet listSet2)

let rec translate_aux astd = match astd with
  |ASTD_astd.Elem _ -> ([],[],[])
  |ASTD_astd.Automata(name,state_list,transition_list,shallowFinal_list,deepFinal_list,initialState) ->
    let setList,varList,opeList = translateStateList state_list name in
    let opeListNew = addOperationFromTransitionList astd transition_list opeList varList in
    setList,
    ("State_"^ name,
     ["AutState_" ^ name],
     ASTD_B.AffectationInit (ASTD_B.Variable ("State_" ^ name),
			     ASTD_B.Constant initialState))::varList,
    opeListNew
  |ASTD_astd.Sequence (name,astdFst,astdSnd) ->
    let setListFst,varListFst,opeListFst = translate_aux astdFst in
    let setListSnd,varListSnd,opeListSnd = translate_aux astdSnd in
    ((addEnumerateSetToSetList "SequenceState" ["fst";"snd"] (setListSnd@setListFst)),
     ("State_"^name,
      ["SequenceState"],
      ASTD_B.AffectationInit (ASTD_B.Variable ("State_" ^ name),
			      ASTD_B.Constant "fst"))::(varListFst@varListSnd),
     (modifyOperationForSequence opeListFst opeListSnd name astdFst (varListFst@varListSnd)))
  |ASTD_astd.Choice (name,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux astdLeft and
	setListRight,varListRight,opeListRight = translate_aux astdRight in
    ((addEnumerateSetToSetList "ChoiceState" ["rightS";"leftS";"none"] (setListFusion setListLeft setListRight)),
     ("State_"^name,
      ["ChoiceState"],
      ASTD_B.AffectationInit (ASTD_B.Variable ("State_" ^ name),
			      ASTD_B.Constant "none"))::(varListRight@varListLeft),
     modifyOperationForChoice opeListLeft opeListRight name astdLeft (varListLeft@varListRight))
  |ASTD_astd.Kleene (name,subAstd) ->
    let setList,varList,opeList = translate_aux subAstd in
    (addEnumerateSetToSetList "KleeneState" ["started";"notStarted"] setList,
     ("State_" ^ name,
      ["KleeneState"],
      ASTD_B.AffectationInit (ASTD_B.Variable ("State_" ^ name),
			      ASTD_B.Constant "notStarted"))::varList,
     List.rev_map (modifyOperationForKleene name subAstd varList) opeList)
  |ASTD_astd.Synchronisation (name,syncList,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux astdLeft and
	setListRight,varListRight,opeListRight = translate_aux astdRight in
    (setListRight@setListLeft,
     varListRight@varListLeft,
     modifyOperationsForSynchro opeListRight opeListLeft syncList name)
  |ASTD_astd.QChoice (name,var,domain,subAstd) ->
    let setList,varList,opeList = translate_aux subAstd in
    (addEnumerateSetToSetList domain [] (addEnumerateSetToSetList "QChoiceSet" ["chosen";"notChosen"] setList),
     (("State_" ^ name,
       ["QChoiceSet"],
       AffectationInit (Variable ("State_" ^ name),
			Constant "notChosen"))::
	 ("Value_" ^ name,
	  [domain],
	  AnyInit ("xx",
		   In (ASTD_B.Variable "xx",
		       Constant domain),
		   Variable ("Value_" ^ name),
		   Variable "xx"))::
	 varList),
     List.rev_map (modifyOperationForQChoice name var varList) opeList)
  |ASTD_astd.QSynchronisation(name,var,domain,syncSetList,subAstd) ->
    let setList,varList,opeList = translate_aux subAstd in
    (setList,
     List.rev_map (quantifiedVariableInVarList domain) varList,
     List.rev_map (modifyOperationForQSync syncSetList var domain) opeList)
  |ASTD_astd.Fork(name,var,domain,predicate_list,synchSetList,subAstd) ->
    let setList,varList,opeList = translate_aux subAstd in
    (setList,
     List.rev_map (quantifiedVariableInVarList domain) varList,
     List.rev_map (modifyOperationForFork synchSetList var domain predicate_list) opeList)
and translateStateList stateList nameTranslatedAstd = match stateList with
  |h::t -> let (setListOfH,varListOfH,opeListOfH) = translate_aux h in
	   let (setListOfT,varListOfT,opeListOfT) = translateStateList t nameTranslatedAstd
	   in ((addStateToStateList (ASTD_astd.get_name h) nameTranslatedAstd (setListOfH@setListOfT)),varListOfH@varListOfT,opeListOfT@opeListOfH)
  |[] -> ([],[],[]);;

let rec getInfoFromVarList varList = match varList with
  |[] -> ([],[],[])
  |(name,invList,init)::t -> let nameList,invList_list,initList = getInfoFromVarList t in
			     (name::nameList,((name,invList)::invList_list),init::initList);;

let callOpe op =
  {ASTD_B.nameOf = op.ASTD_B.nameOf;
   ASTD_B.parameter = op.ASTD_B.parameter;
   ASTD_B.preOf = op.ASTD_B.preOf;
   ASTD_B.postOf =
     match op.postOf with
     |ASTD_B.Parallel li -> ASTD_B.Parallel (Call ((op.nameOf ^ "_act"),op.parameter)::li)
     |_ -> ASTD_B.Parallel [Call ((op.nameOf ^ "_act"),op.parameter);op.postOf];
  }

let translate astd name refine sees includes = let setsList,varList,opeList = translate_aux astd in
				      let variables,invariants,initialisation=getInfoFromVarList varList in
				      let machine = {ASTD_B.machine = if refine="" then Machine name else (Refinement (name,refine));
						     ASTD_B.sees = if sees="" then NoSeenMachine else SeenMachine sees;
						     ASTD_B.includes = if includes="" then NoIncludedMachine else IncludedMachine includes;
						     ASTD_B.sets = setsList;
						     ASTD_B.variables = variables;
						     ASTD_B.invariants = invariants;
						     ASTD_B.init = initialisation;
						     ASTD_B.operations = List.rev_map callOpe (List.rev_map snd opeList)} in
				      ASTD_B.print_machine machine;;

