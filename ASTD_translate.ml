exception NotFound of string;;

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
								    ASTD_B.Variable init))::(initializeAllVariable init astd);;

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

let rec final astd = match astd with
  |ASTD_astd.Elem e -> ASTD_B.True
  |ASTD_astd.Automata (name,_,_,sFinal,dFinal,_) -> 
    match sFinal,dFinal with
    |[],[] -> failwith "No Final State"
    |t::q,[] -> ASTD_B.In(ASTD_B.Variable ("State_" ^ name),
			  ASTD_B.EnumerateSet sFinal)
    |[],t::q -> And(ASTD_B.In(ASTD_B.Variable ("State_"^name),
			      ASTD_B.EnumerateSet dFinal),
		    dFinalStateCond dFinal astd)
    |t1::q1,t2::q2 -> (ASTD_B.Or(ASTD_B.In(ASTD_B.Variable ("State_" ^ name),
					   ASTD_B.EnumerateSet sFinal),
				 ASTD_B.In(ASTD_B.Variable ("State_"^name),
					   ASTD_B.EnumerateSet dFinal)))
and dFinalStateCond dFinal astd = match dFinal with
  |[] -> failwith "No DFinal State"
  |[t] -> ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
					  ASTD_B.Variable t),
			  final (getAstdFromName t astd))
  |t::q -> ASTD_B.And(ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
						      ASTD_B.Variable t),
				      final (getAstdFromName t astd)),
		      dFinalStateCond q astd);;

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

let transformTransition translatedAstd transition = 
  let name = ASTD_astd.get_name translatedAstd
  in match transition with
  |ASTD_arrow.Local(fromState,toState,astdTransition,astdPredicate,finale) ->
    ((let cAll = (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),
				   ASTD_B.Variable fromState))
      in let preOf = (if finale 
	then (ASTD_B.And(cAll,
			 final (getAstdFromName fromState translatedAstd)))
	else cAll)
	 in
	 let gu = translatePredicateList astdPredicate in
	 if gu = ASTD_B.True then preOf

	 else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Variable toState))
     in ASTD_B.Parallel (tAll::(initializeAllVariable toState translatedAstd)))
  |ASTD_arrow.From_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
    ((let cAll = (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),
				   ASTD_B.Variable throughState))
      in let cFromSub = ASTD_B.Equality(ASTD_B.Variable("State_" ^ throughState),
					ASTD_B.Variable fromState)
	 in let preOf = (if finale
	   then (ASTD_B.And(ASTD_B.And(cAll,cFromSub),
			    final (getAstdFromName fromState translatedAstd)))
	   else ASTD_B.And(cAll,cFromSub))
	    in
	    let gu = translatePredicateList astdPredicate in
	    if gu = ASTD_B.True then preOf

	    else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Variable toState))
     in ASTD_B.Parallel (tAll::(initializeAllVariable toState translatedAstd)))  
  |ASTD_arrow.To_sub (fromState,toState,throughState,astdTransition,astdPredicate,finale) ->
    ((let cAll = ASTD_B.Equality(ASTD_B.Variable("State_" ^ name),
				 ASTD_B.Variable fromState)
      in let preOf = (if finale
	then (ASTD_B.And(cAll,
			 final (getAstdFromName fromState translatedAstd)))
	else cAll)
	 in
	 let gu = translatePredicateList astdPredicate in
	 if gu = ASTD_B.True then preOf
	 else ASTD_B.And(preOf,gu)),
     let tAll = (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
				     ASTD_B.Variable throughState))
     in let tToSub = (ASTD_B.Affectation (ASTD_B.Variable("State_" ^ throughState),
					  ASTD_B.Variable toState))
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



let transformSubOperation name elem = let (name1,operation) = elem in (ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),ASTD_B.Variable name1),operation.ASTD_B.preOf),operation.ASTD_B.postOf);;

(*
  This operation transform the list of transition in operations, and merges it with the list of allready translated operations. It takes 5 arguments :
  - name : The name of the current ASTD
  - nameOperation : The name of the operation
  - hOperationList : The list of operations translated in the subAstd
  - hTransitionList : The transition list of the ASTD labelled with nameOperatoin
  - translatedAstd : The global translated Astd
*)

let merge astd nameOperation hOperationList hTransitionList =
  let subList = ((List.rev_map (transformTransition astd) hTransitionList)@(List.rev_map (transformSubOperation (ASTD_astd.get_name astd)) hOperationList))
  in let preOf = getPreOf subList
     in (ASTD_astd.get_name astd,{ASTD_B.nameOf = nameOperation;
				  ASTD_B.parameter =[];
				  ASTD_B.preOf=preOf;
				  ASTD_B.postOf=ASTD_B.Select subList});;

(*
  This operation construct the new operation list of the translation. It gives an operation list.
  It takes 4 arguments :
  - name : it's the name of the automata that is translated
  - transition_list : The list of the transition of the translated automata
  - opeList : the list of operation of the sub ASTD
  - translatedAstd : the principal translated ASTD
  The idea is to get all the transitions and the operations that have 
*)

let rec addOperationFromTransitionList astd transition_list opeList = match transition_list with
  |[] -> opeList
  |h::t -> let hOperationList,otherOpeList = 
	     seperateOperation (ASTD_arrow.get_label_transition h) opeList in
	   let hTransitionList, otherTransitionList =
	     seperateTransition (ASTD_arrow.get_label_transition h) transition_list in
	   (merge astd (ASTD_arrow.get_label_transition h) hOperationList hTransitionList)::
	     (addOperationFromTransitionList astd otherTransitionList otherOpeList);;

let rec addEnuerateSetToSetList nameOfSet valueListOfSet setList = match setList with
  |[] -> [nameOfSet,valueListOfSet]
  |(name,values)::t -> if name = nameOfSet then setList else (name,values)::(addEnuerateSetToSetList nameOfSet valueListOfSet t);;

let rec translate_aux astd = match astd with
  |ASTD_astd.Elem _ -> ([],[],[])
  |ASTD_astd.Automata(name,state_list,transition_list,shallowFinal_list,deepFinal_list,initialState) ->
    let setList,varList,opeList = translateStateList state_list name in
    let opeListNew = addOperationFromTransitionList astd transition_list opeList in
    setList,("State_"^ name,["AutState_" ^ name],initialState)::varList,opeListNew
  |ASTD_astd.Sequence (name,astdFst,astdSnd) ->
    let setListFst,varListFst,opeListFst = translate_aux astdFst in
    let setListSnd,varListSnd,opeListSnd = translate_aux astdSnd in
    ((addEnuerateSetToSetList "SequenceState" ["fst";"snd"] setListSnd),varListSnd,opeListSnd)
and translateStateList stateList nameTranslatedAstd = match stateList with
  |h::t -> let (setListOfH,varListOfH,opeListOfH) = translate_aux h in
	   let (setListOfT,varListOfT,opeListOfT) = translateStateList t nameTranslatedAstd
	   in ((addStateToStateList (ASTD_astd.get_name h) nameTranslatedAstd (setListOfH@setListOfT)),varListOfH@varListOfT,opeListOfT@opeListOfH)
  |[] -> ([],[],[]);;

let rec getInfoFromVarList varList = match varList with
  |[] -> ([],[],[])
  |(name,invList,init)::t -> let nameList,invList_list,initList = getInfoFromVarList t in
			     (name::nameList,((name,invList)::invList_list),(name,[],init)::initList);;


let translate astd = let setsList,varList,opeList = translate_aux astd in
		     let variables,invariants,initialisation=getInfoFromVarList varList in
		     let machine = {ASTD_B.machine = "toto";
				    ASTD_B.sets = setsList;
				    ASTD_B.variables = variables;
				    ASTD_B.invariants = invariants;
				    ASTD_B.initialisation = initialisation;
				    ASTD_B.operations = List.rev_map snd opeList} in
		     ASTD_B.print_machine machine;;

