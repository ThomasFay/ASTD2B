exception NotFound;;

let rec addStateToStateList nameOfTheState nameOfTheStateSet setList = match setList with
  |[] -> ["AutState_" ^ nameOfTheStateSet,[nameOfTheState]]
  |(name,stateList)::t -> if name = "AutState_" ^ nameOfTheStateSet
    then (name,nameOfTheState::stateList)::t
    else (name,stateList)::(addStateToStateList nameOfTheState nameOfTheStateSet t);;

let right co = let (a,b) = co in b;;

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

let rec getAstdFromName name astd = match astd with
  |ASTD_astd.Elem nameElem -> if nameElem = name then astd else raise NotFound
  |ASTD_astd.Automata (nameAut,stateList,_,_,_,_)-> if nameAut = name then astd else getAstdFromStateList name stateList
and getAstdFromStateList name stateList = match stateList with
  |[] -> raise NotFound
  |h::t -> try getAstdFromName name h with
    |NotFound -> getAstdFromStateList name t;;

let rec initializeAllVariable nameInitialState astd = 
  let initialAstd = getAstdFromName nameInitialState astd in match initialAstd with
    |ASTD_astd.Elem _ -> []
    |ASTD_astd.Automata (name,_,_,_,_,init) -> (ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
							   ASTD_B.Variable init))::(initializeAllVariable init astd);;

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

let transformTransition translatedAstd transition = let name = ASTD_astd.get_name translatedAstd
						    in match transition with
  |ASTD_arrow.Local(fromState,toState,astdTransition,astdPredicate,finale) ->
  ((if finale then (ASTD_B.And((ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),ASTD_B.Variable fromState)),final (getAstdFromName fromState translatedAstd))) else (ASTD_B.Equality (ASTD_B.Variable ("State_" ^ name ),ASTD_B.Variable fromState))) ,
   ASTD_B.Parallel 
     ((ASTD_B.Affectation (ASTD_B.Variable ("State_" ^ name),
			   ASTD_B.Variable toState))::(initializeAllVariable toState translatedAstd)));;

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


let rec translate_aux astd = match astd with
  |ASTD_astd.Elem _ -> ([],[],[])
  |ASTD_astd.Automata(name,state_list,transition_list,shallowFinal_list,deepFinal_list,initialState) ->
    let setList,varList,opeList = translateStateList state_list name in
    let opeListNew = addOperationFromTransitionList astd transition_list opeList in
    setList,("State_"^ name,["AutState_" ^ name],initialState)::varList,opeListNew
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
				    ASTD_B.operations = List.rev_map right opeList} in
		     ASTD_B.print_machine machine;;

