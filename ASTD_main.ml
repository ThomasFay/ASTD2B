let raffichage = ref 1
let rkappa_indirect = ref true
let rprint_final = ref false
let rstarting_choice_possible = ref false
let rplace_to_read = ref "TUnit/"
let rbdd = ref false
let rwait = ref false
let rdebug = ref true
let rsFile = ref ""
let riFile = ref ""
let refinement = ref ""
let name = ref ""
let sees = ref ""
let includes = ref ""
let nocalls = ref false
let invFile = ref ""
let starting = ref ""
let assertFile = ref ""
let simpl = ref false
let mini = ref false

let set_to_ref refInt value () = ignore ( refInt := value )

(* let debug_on () = ASTD_exec_first_bd.debug_on () ;  *)
(*                State2DB.debug_on ()  *)

let arg_spec = [
  "-i", Arg.Set_string riFile, "Input action list to execute";
  "-s", Arg.Set_string rsFile, "Input specification";
  "-db", Arg.Set rbdd, "Activates database storage for current state";
  "-hash", Arg.Clear rbdd, "Activates hastable storage for current state";
  "-nokappa", Arg.Clear rkappa_indirect, "Desactivates kappa indirect optimization";
  "-final", Arg.Set rprint_final, "Prints final state";
  "-read", Arg.Set_string rplace_to_read, "Input root for specification";
  "-wait", Arg.Set rwait, "Activates wait before trying to execute new action";
  "-v", Arg.Unit (set_to_ref raffichage 1), "Regular verbose level";
  "-vv", Arg.Unit (set_to_ref raffichage 2), "Intermediate verbose level";
  "-vvv", Arg.Unit (set_to_ref raffichage 3), "Maximum verbose level";
  "-refinement", Arg.Set_string refinement, "The translated ASTD is a refinement";
  "-name", Arg.Set_string name, "The name of the B machine";
  "-sees", Arg.Set_string sees, "The seen machine if there is one";
  "-includes", Arg.Set_string includes, "The included machine if necessary";
  "-nocalls", Arg.Set nocalls, "Do not call the data operations";
  "-invFile",Arg.Set_string invFile, "If necessary, add the file that contains the invariants";
  "-starting",Arg.Set_string starting, "+ name : chose the name of the starting ASTD. Default MAIN";
  "-assertFile", Arg.Set_string assertFile, "If necessary, add the file that contain assertions";
  "-simpl", Arg.Set simpl, "Simplify The Select substitutions";
  "-min", Arg.Set mini, "Minimize the ASTD (work in progress)"
  (* "-debug", Arg.Unit debug_on , "Activate debug output"; *)
]

let usage_msg = "iASTD : An ASTD interpretor \n"

let usage _ = Arg.usage arg_spec usage_msg; exit 1 

(* how-to get a specification *)
let get_structure (place) = print_endline ("Enter file name of the structure : "^place) ; 
                           try let name = (place^(input_line stdin))
                               in print_endline ("Reading from " ^ name) ;
                                  let structure=ASTD_parser.get_structure_from name 
					in print_endline "Read"; structure
                           with Sys_error s -> begin
                                               print_endline s ;
                                               print_endline "Reading from stdin." ;
                                               ASTD_parser.get_structure_from_stdin () 
                                               end 
;;

let get_structure_from_file (place) = try let structure=ASTD_parser.get_structure_from place in structure ;
                           with Sys_error s -> begin
                                               print_endline s ;
                                               print_endline "Reading from stdin." ;
                                               ASTD_parser.get_structure_from_stdin () 
                                               end 
;;
(*
let get_event_list (place) = print_endline ("Enter file name of the instructions : "^place) ; 
                           try let name = (place^(input_line stdin))
                               in print_endline ("Reading from " ^ name) ;
                                  let events=ASTD_parser.get_event_list_from name 
					in print_endline "Read"; events
                           with Sys_error s -> begin
                                               print_endline s ;
                                               print_endline "Reading from stdin." ;
                                               ASTD_parser.get_event_list_from_stdin () 
                                               end 
;;


let get_event_list_from_file (place) = try let events=ASTD_parser.get_event_list_from place in events ;
                           with Sys_error s -> begin
                                               print_endline s ;
                                               print_endline "Reading from stdin." ;
                                               ASTD_parser.get_event_list_from_stdin () 
                                               end 
;;
 *)

let get_starting_name (starting_choice_possible) =
	if starting_choice_possible
		then begin
			print_endline "Enter main ASTD's name" ; 
			let name=(input_line stdin)
                        in if "" = name
                               then "MAIN"
				else name
			end
		else "MAIN"


let rec get_invariants file =
  try
    let line = input_line (file) in
    line ^ "\n" ^ get_invariants file
  with
    End_of_file -> ""

let readInvFile file place =
  try match file with
      |"" -> ""
      |_ -> get_invariants (open_in (place ^ file))
  with
    Sys_error s -> ""

let rec get_assertions file =
  try
    let line = input_line (file) in
    line ^ "\n" ^ get_invariants file
  with
    End_of_file -> ""

let readAssertFile file place =
  try match file with
      |"" -> ""
      |_ -> get_invariants (open_in (place ^ file))
  with
    Sys_error s -> ""

let _ = Arg.parse arg_spec usage usage_msg;
  let (affichage,kappa_indirect,print_final, starting_choice_possible, place_to_read, bdd, wait, debug, sFile, iFile,refine,name,sees,includes,nocalls,invFile,starting,assertFile,simpl, mini)
      = (!raffichage,!rkappa_indirect,!rprint_final,!rstarting_choice_possible,!rplace_to_read,!rbdd,!rwait,!rdebug,!rsFile,!riFile,!refinement,!name,!sees,!includes,!nocalls,!invFile,!starting,!assertFile,!simpl, !mini)
  in
  begin if (sFile=="") then get_structure(place_to_read) else get_structure_from_file(place_to_read^sFile) ;
	let startingName = if starting = "" then "MAIN" else starting in
	let structure = if mini then (ASTD_minimize.minimize (ASTD_astd.get_astd startingName)) else (ASTD_astd.get_astd startingName)
	in 
	let invariants = readInvFile invFile place_to_read and assertions = readAssertFile assertFile place_to_read
	in
	let
	  nameBFile = (if (name == "") then "MachineName" else name)
	in
	print_endline(ASTD_translate.translate
			structure
			nameBFile
			refine
			sees
			includes
			nocalls
			invariants
			assertions
			simpl);
  end
;;
  

(*(**)
(*(* Main part *)*)
(*let _ = Arg.parse arg_spec usage usage_msg;*)
(*        print_endline "========================================" ;*)
(*        print_newline () ;*)
(*	let start_time=(Unix.gettimeofday())*)
(*	in let (affichage,kappa_indirect,print_final, starting_choice_possible, place_to_read, bdd, wait, debug, sFile, iFile) *)
(*    	= (!raffichage,!rkappa_indirect,!rprint_final,!rstarting_choice_possible,!rplace_to_read,!rbdd,!rwait,!rdebug,!rsFile,!riFile) *)
(*	in begin if (sFile=="") then get_structure(place_to_read) else get_structure_from_file(place_to_read^sFile) ;*)
(*	let structure=ASTD_astd.get_astd (get_starting_name (starting_choice_possible))	*)
(*	in print_endline "========================================" ;*)
(*	    let time1=(Unix.gettimeofday())*)
(*               in print_endline "========================================" ;*)
(*               print_endline "Main structure : " ;*)
(*               ASTD_astd.print structure "" ;*)
(*               print_newline () ;*)
(*               print_endline "========================================" ;*)
(*	if bdd*)
(**)
(*	then*)
(*		begin*)
(*		if kappa_indirect ;*)
(*		then*)
(*		       let (kappa_opt_list,dep_used_list)=ASTD_static_kappa_indirect.static_analysis structure*)
(*		       in let time2start = (Unix.gettimeofday())*)
(*		       in let analysed_struct=ASTD_static_kappa_indirect.register_static kappa_opt_list dep_used_list structure*)
(*		       in let time2end = (Unix.gettimeofday())*)
(*        	       in let state= (ASTD_exec_first_bd.init analysed_struct) ; *)
(*  	 	           in State2DB.initdb () ; ASTD_exec_first_bd.register_db "Main" None state structure ;  *)
(*    	 	          print_endline "========================================" ;*)
(*		  	  print_float(float_of_int (List.length kappa_opt_list));*)
(*			  print_endline "optimisations found" ;*)
(*            	          print_endline "========================================" ;*)
(*			  print_endline "========================================" ;*)
(*               	          print_endline "Starting state";*)
(*  		 	  ASTD_exec_first_bd.print (ASTD_exec_first_bd.get_db "Main") analysed_struct "" "Main";*)
(*             		  print_endline "========================================" ;*)
(**)
(**)
(*			  let opened_file = open_in (place_to_read^iFile)*)
(*			  in let raw =ref ""*)
(*			  in let new_state = ref (ASTD_exec_first_bd.init analysed_struct)*)
(*			  in let reg_time = ref 0.*)
(*			  in let executed_events = ref 0*)
(*			  in let cpt=ref 0*)
(*			  in begin*)
(*                                  (try begin while true *)
(*						do begin *)
(*							raw := input_line opened_file;*)
(*							let raw_spec=Lexing.from_string !raw*)
(*							in let small_list= ASTD_parser_rules.apply_event ASTD_lexer_rules.token raw_spec*)
(*							in begin *)
(*p								 let (a,b,c) = ASTD_exec_first_bd.execute_event_list affichage wait (State2DB.db2state "Main") analysed_struct small_list 0.*)
(*								 in begin*)
(*									new_state:= a;*)
(*									reg_time:= b +. !reg_time;*)
(*									executed_events:= c + !executed_events;*)
(*									cpt:=!cpt + 1*)
(*								    end*)
(*							end*)
(*						    end *)
(*						done;*)
(*						failwith "bizarre : true=false " *)
(*					end*)
(*						with _ -> print_endline "no more event to execute" );*)
(*               	           *)
(*				close_in opened_file ;*)
(**)
(**)
(*               	          	begin if print_final *)
(*					  then begin *)
(*						print_endline "========================================" ;*)
(*						print_endline "Final state"; ASTD_exec_first_bd.print !new_state structure "" "Main"; *)
(*        	        			print_endline "========================================" *)
(*						end*)
(*					else begin end*)
(*					end;*)
(*           			          let exec_time = (Unix.gettimeofday())-.time2end *)
(*					  in print_newline();*)
(*  	  				    print_float(time1-.start_time);*)
(*					    print_endline " seconds of READING";*)
(*  					    print_float(time2end-.time2start);*)
(*					    print_endline " seconds of Kappa indirect static analysis";*)
(*  					    print_float(exec_time);*)
(*					    print_endline " seconds of EXECUTION";*)
(*  					    print_endline ("for "^(string_of_int (!cpt))^" events");*)
(*	   			            print_float(exec_time/.(float_of_int (!cpt)));*)
(*		  			    print_endline " seconds of treatement per instruction";*)
(*						print_float(!reg_time/.(float_of_int (!executed_events)));*)
(*			                	print_endline " seconds of registration per instruction";*)
(*          	   			    print_newline()*)
(*			end*)
(*		else*)
(*		       let state = (ASTD_exec_first_bd.init structure) in *)
(*		           begin *)
(*                        State2DB.initdb () ;*)
(*		                ASTD_exec_first_bd.register_db "Main" None state structure ;  *)
(*        	            (*ASTD_exec_first_bd.print (ASTD_exec_first_bd.get_db "Main") structure "" "Main";*)*)
(**)
(**)
(*			  let opened_file = open_in (place_to_read^iFile)*)
(*			  in let raw =ref ""*)
(*			  in let new_state = ref state*)
(*			  in let reg_time = ref 0.*)
(*			  in let executed_events = ref 0*)
(*			  in let cpt = ref 0*)
(*			  in begin*)
(*                                  (try begin while true *)
(*						do begin *)
(*							raw := input_line opened_file;*)
(*							let raw_spec=Lexing.from_string !raw*)
(*							in let small_list= ASTD_parser_rules.apply_event ASTD_lexer_rules.token raw_spec*)
(*							in begin *)
(*								 let (a,b,c) = ASTD_exec_first_bd.execute_event_list affichage wait (State2DB.db2state "Main") structure small_list 0.*)
(*								 in begin*)
(*									new_state:= a;*)
(*									reg_time:= b +. !reg_time;*)
(*									executed_events:= c + !executed_events;*)
(*									cpt:=!cpt +1*)
(*								    end*)
(*							end*)
(*						    end *)
(*						done;*)
(*						failwith "bizarre : true=false " *)
(*					end*)
(*						with _ -> print_endline "no more event to execute" );*)
(*               	           *)
(*				close_in opened_file ;*)
(**)
(**)
(*                             begin if print_final *)
(*				            then begin *)
(*					            print_endline "========================================" ;*)
(*					            print_endline "Final state"; ASTD_exec_first_bd.print !new_state structure "" "Main";*)
(*                    	        		print_endline "========================================" *)
(*					            end *)
(*				            else begin end *)
(*			              end; *)
(*                    	          let exec_time = (Unix.gettimeofday())-.time1 *)
(*			              in print_newline();*)
(*              	 		    print_float(time1-.start_time);*)
(*			                print_endline " seconds of READING";*)
(*              			    print_float(exec_time);*)
(*			                print_endline " seconds of EXECUTION";*)
(*              			    print_endline ("for "^(string_of_int (!cpt))^" events");*)
(*		                        print_float(exec_time/.(float_of_int (!cpt)));*)
(*			                print_endline " seconds of treatement per instruction";*)
(*					print_float(!reg_time/.(float_of_int (!executed_events)));*)
(*			                print_endline " seconds of registration per instruction executed";*)
(*                    	  	    print_newline()*)
(*                         end*)
(*                    end*)
(*	end*)
(**)
(**)
(**)
(*	else *)
(*		begin*)
(*		if kappa_indirect ;*)
(*		then*)
(*		       let (kappa_opt_list,dep_used_list)=ASTD_static_kappa_indirect.static_analysis structure*)
(*		       in let time2start = (Unix.gettimeofday())*)
(*		       in let analysed_struct=ASTD_static_kappa_indirect.register_static kappa_opt_list dep_used_list structure*)
(*		       in let time2end = (Unix.gettimeofday())*)
(*        	       in let state= (ASTD_exec_first_hash.init analysed_struct)*)
(*      	 	       in print_endline "========================================" ;*)
(*		  	  print_float(float_of_int (List.length kappa_opt_list));*)
(*			  print_endline "optimisations found" ;*)
(*            	          print_endline "========================================" ;*)
(*			  print_endline "========================================" ;*)
(*               	          print_endline "Starting state";*)
(*  		 	  ASTD_exec_first_hash.print state analysed_struct "" "Main";*)
(*             		  print_endline "========================================" ;*)
(*			  let opened_file = open_in (place_to_read^iFile)*)
(*			  in let raw =ref ""*)
(*			  in let cpt = ref 0*)
(*			  in let temp_state=ref (ASTD_exec_first_hash.init analysed_struct)*)
(*			  in let new_state = (try begin while true do begin raw := input_line opened_file;*)
(*									let raw_spec=Lexing.from_string !raw*)
(*									in let small_list= ASTD_parser_rules.apply_event ASTD_lexer_rules.token raw_spec*)
(*									in begin *)
(*									 temp_state := ASTD_exec_first_hash.execute_event_list affichage !temp_state analysed_struct small_list;*)
(*									cpt:=!cpt +1*)
(*									end*)
(*								end done; failwith "no end found" end*)
(*						with _ -> print_endline "no more event to execute";!temp_state )*)
(*               	           *)
(*				in close_in opened_file ;*)
(*				begin if print_final *)
(*					  then begin *)
(*						print_endline "========================================" ;*)
(*						print_endline "Final state"; ASTD_exec_first_hash.print new_state structure "" "Main";*)
(*        	        			print_endline "========================================" *)
(*						end*)
(*					else begin end*)
(*					end;*)
(*           			          let exec_time = (Unix.gettimeofday())-.time2end *)
(*					  in print_newline();*)
(*  	  				    print_float(time1-.start_time);*)
(*					    print_endline " seconds of READING";*)
(*  					    print_float(time2end-.time2start);*)
(*					    print_endline " seconds of Kappa indirect static analysis";*)
(*  					    print_float(exec_time);*)
(*					    print_endline " seconds of EXECUTION";*)
(*  					    print_endline ("for "^(string_of_int (!cpt))^" events");*)
(*	   			            print_float(exec_time/.(float_of_int (!cpt)));*)
(*		  			    print_endline " seconds of treatement per instruction";*)
(*          	   			    print_newline()*)
(*		else*)
(*		       let state = (ASTD_exec_first_hash.init structure)*)
(*        	       in ASTD_exec_first_hash.print state structure "" "Main";*)
(**)
(*			  let opened_file = open_in (place_to_read^iFile)*)
(*			  in let raw =ref ""*)
(*			  in let cpt= ref 0*)
(*			  in let temp_state=ref (ASTD_exec_first_hash.init structure)*)
(*			  in let new_state = (try begin while true do begin raw := input_line opened_file;*)
(*									let raw_spec=Lexing.from_string !raw*)
(*									in let small_list= ASTD_parser_rules.apply_event ASTD_lexer_rules.token raw_spec*)
(*									in begin *)
(*									 temp_state := ASTD_exec_first_hash.execute_event_list affichage !temp_state structure small_list;*)
(*									cpt:=!cpt +1*)
(*									end*)
(*								end done; failwith "no end found" end*)
(*						with _ -> print_endline "no more event to execute";!temp_state )*)
(*               	           *)
(*				in close_in opened_file ;*)
(**)
(*                       		begin if print_final *)
(*				then begin *)
(*					print_endline "========================================" ;*)
(*					print_endline "Final state"; ASTD_exec_first_hash.print new_state structure "" "Main";*)
(*        	        		print_endline "========================================" *)
(*					end *)
(*				else begin end *)
(*			  end;*)
(*        	          let exec_time = (Unix.gettimeofday())-.time1 *)
(*			  in print_newline();*)
(*  	 		    print_float(time1-.start_time);*)
(*			    print_endline " seconds of READING";*)
(*  			    print_float(exec_time);*)
(*			    print_endline " seconds of EXECUTION";*)
(*  			    print_endline ("for "^(string_of_int (!cpt))^" events");*)
(*		            print_float(exec_time/.(float_of_int (!cpt)));*)
(*			    print_endline " seconds of treatement per instruction";*)
(*        	  	    print_newline()*)
(*             end     *)
(*	end*)
(*    ;; *)
(**)
(**)*)
