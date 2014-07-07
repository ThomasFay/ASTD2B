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

let rec initValueOfVar var1 listVar =
  let name = match var1 with
    |ASTD_B.Constant str -> str
    |ASTD_B.Variable str -> str
    |ASTD_B.EnumerateSet li -> failwith "Not a Proper Variable"
  in
  match listVar with
  |[] -> name
  |(nameVar,typeList,valueVar)::t -> if nameVar = name then valueVar else initValueOfVar (Variable name) t

let rec initPred pred listVar = match pred with
  |ASTD_B.And (pred1,pred2) -> ASTD_B.And (initPred pred1 listVar,initPred pred2 listVar)
  |ASTD_B.Or (pred1,pred2) -> ASTD_B.Or (initPred pred1 listVar ,initPred pred2 listVar)
  |ASTD_B.BPred s -> BPred s
  |ASTD_B.Equality (var1,val1) -> ASTD_B.Equality (ASTD_B.Constant (initValueOfVar var1 listVar), val1)
  |ASTD_B.In (var1,val1) -> ASTD_B.In (ASTD_B.Constant (initValueOfVar var1 listVar), val1)
  |ASTD_B.True -> ASTD_B.True
  |ASTD_B.Implies (pred1,pred2) -> ASTD_B.Implies (initPred pred1 listVar,initPred pred2 listVar)

let rec initSub sub listVar = match sub with
  |ASTD_B.Affectation (_,_) -> sub
  |ASTD_B.Select listSelect -> ASTD_B.Select (initSubSelectList listSelect listVar)
  |ASTD_B.Parallel listPara -> ASTD_B.Parallel (initSubParaList listPara listVar)
and initSubSelectList listSelect listVar = match listSelect with
  |[] -> []
  |(gu,post)::t -> (initPred gu listVar,initSub post listVar)::(initSubSelectList t listVar)
and initSubParaList listPara listVar = match listPara with
  |[] -> []
  |head::tail -> (initSub head listVar) :: (initSubParaList tail listVar)

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
  |ASTD_astd.Kleene(name,subAstd) -> ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
								  ASTD_B.Constant "notStarted"),
						 final subAstd listVar)
  |ASTD_astd.Synchronisation (name,labelList,astdLeft,astdRight) ->
    ASTD_B.And (final astdLeft listVar,
		final astdRight listVar)
and dFinalStateCond dFinal astd listVar = match dFinal with
  |[] -> failwith "No DFinal State"
  |[t] -> ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
					  ASTD_B.Variable t),
			  final (getAstdFromName t astd) listVar)
  |t::q -> ASTD_B.And(ASTD_B.Implies (ASTD_B.Equality(ASTD_B.Variable ("State_" ^ (ASTD_astd.get_name astd)),
						      ASTD_B.Variable t),
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
				   ASTD_B.Variable fromState))
      in let preOf = (if finale 
	then (ASTD_B.And(cAll,
			 final (getAstdFromName fromState translatedAstd) listVar))
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
			    final (getAstdFromName fromState translatedAstd) listVar))
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
			 final (getAstdFromName fromState translatedAstd) listVar))
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

let merge astd nameOperation hOperationList hTransitionList listVar =
  let subList = ((List.rev_map (transformTransition astd listVar) hTransitionList)@(List.rev_map (transformSubOperation (ASTD_astd.get_name astd)) hOperationList))
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

let rec addOperationFromTransitionList astd transition_list opeList listVar = match transition_list with
  |[] -> opeList
  |h::t -> let hOperationList,otherOpeList = 
	     seperateOperation (ASTD_arrow.get_label_transition h) opeList in
	   let hTransitionList, otherTransitionList =
	     seperateTransition (ASTD_arrow.get_label_transition h) transition_list in
	   (merge astd (ASTD_arrow.get_label_transition h) hOperationList hTransitionList listVar)::
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

let rec modifyOperationsForKleene listOpe name subAstd varList = match listOpe with
  |[] -> []
  |(nameOpe,opeOpe)::t ->
    let pre1 = ASTD_B.And (ASTD_B.Or (final subAstd varList,
				      ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
						       ASTD_B.Constant "notStarted")),
			   initPred (opeOpe.ASTD_B.preOf) varList) and
	pre2 = ASTD_B.And (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name),
					    ASTD_B.Constant "started"),
			   opeOpe.ASTD_B.preOf) in
    let post = ASTD_B.Select [pre1, ASTD_B.Parallel [ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
									 ASTD_B.Constant "started");
						     initSub (opeOpe.ASTD_B.postOf) varList];
			      pre2, opeOpe.ASTD_B.postOf] in
    (name,{ASTD_B.nameOf = opeOpe.ASTD_B.nameOf;
	   ASTD_B.parameter = opeOpe.ASTD_B.parameter;
	   ASTD_B.preOf = ASTD_B.Or (pre1,pre2);
	   ASTD_B.postOf = post})::(modifyOperationsForKleene t name subAstd varList);;

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


let rec addEnumerateSetToSetList nameOfSet valueListOfSet setList = match setList with
  |[] -> [nameOfSet,valueListOfSet]
  |(name,values)::t -> if name = nameOfSet then setList else (name,values)::(addEnumerateSetToSetList nameOfSet valueListOfSet t);;

let rec setListFusion listSet1 listSet2 = match listSet1 with
  |[] -> listSet2
  |(nameOfSet,valuesOfSet)::t -> setListFusion t (addEnumerateSetToSetList nameOfSet valuesOfSet listSet2)

let rec translate_aux astd = match astd with
  |ASTD_astd.Elem _ -> ([],[],[])
  |ASTD_astd.Automata(name,state_list,transition_list,shallowFinal_list,deepFinal_list,initialState) ->
    let setList,varList,opeList = translateStateList state_list name in
    let opeListNew = addOperationFromTransitionList astd transition_list opeList varList in
    setList,("State_"^ name,["AutState_" ^ name],initialState)::varList,opeListNew
  |ASTD_astd.Sequence (name,astdFst,astdSnd) ->
    let setListFst,varListFst,opeListFst = translate_aux astdFst in
    let setListSnd,varListSnd,opeListSnd = translate_aux astdSnd in
    ((addEnumerateSetToSetList "SequenceState" ["fst";"snd"] (setListSnd@setListFst)),("State_"^name,["SequenceState"],"fst")::(varListFst@varListSnd),(modifyOperationForSequence opeListFst opeListSnd name astdFst (varListFst@varListSnd)))
  |ASTD_astd.Choice (name,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux astdLeft and
	setListRight,varListRight,opeListRight = translate_aux astdRight in
    ((addEnumerateSetToSetList "ChoiceState" ["rightS";"leftS";"none"] (setListFusion setListLeft setListRight)),
     ("State_"^name,["ChoiceState"],"none")::(varListRight@varListLeft),
     modifyOperationForChoice opeListLeft opeListRight name astdLeft (varListLeft@varListRight))
  |ASTD_astd.Kleene (name,subAstd) ->
    let setList,varList,opeList = translate_aux subAstd in
    (addEnumerateSetToSetList "KleeneState" ["started";"notStarted"] setList,
     ("State_" ^ name, ["KleeneState"],"notStarted")::varList,
     modifyOperationsForKleene opeList name subAstd varList)
  |ASTD_astd.Synchronisation (name,syncList,astdLeft,astdRight) ->
    let setListLeft,varListLeft,opeListLeft = translate_aux astdLeft and
	setListRight,varListRight,opeListRight = translate_aux astdRight in
    (setListRight@setListLeft,
     varListRight@varListLeft,
     modifyOperationsForSynchro opeListRight opeListLeft syncList name)
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
		     let machine = {ASTD_B.machine = "MachineName";
				    ASTD_B.sets = setsList;
				    ASTD_B.variables = variables;
				    ASTD_B.invariants = invariants;
				    ASTD_B.initialisation = initialisation;
				    ASTD_B.operations = List.rev_map snd opeList} in
		     ASTD_B.print_machine machine;;

