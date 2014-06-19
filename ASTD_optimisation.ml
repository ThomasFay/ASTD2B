type astd_name = string;;

type path = astd_name list

type dependency = (path * ASTD_variable.t list * ASTD_variable.t * ASTD_label.t list * ASTD_label.t list) 

type dep_path = Dep_path of (ASTD_variable.t*dependency*dep_path list)

type optimisation = (ASTD_label.t * path * ASTD_variable.t *dep_path)




 
    let val_debug = ref false;;
    let debug m = if (!val_debug) 
                            then (print_endline m )
                            else begin end;;
    let debug_on () = (val_debug := true);;



let _ASTD_kappa_table_ = Hashtbl.create 5 
;;


let register_kappa dep values value = debug "registering a kappa val" ;Hashtbl.add _ASTD_kappa_table_ (dep,values) value 
;;


let rec remove_all_kappa dep values = debug "removing a kappa val";
					if Hashtbl.mem _ASTD_kappa_table_ (dep,values) 
					then begin
						Hashtbl.remove _ASTD_kappa_table_ (dep,values);
						remove_all_kappa dep values
						end
					else begin end
;;




let rec apply_kappa_mod mod_to_apply= 
		let ((dep,values),value,add)=mod_to_apply
		in if add
			then register_kappa dep values value 
			else remove_all_kappa dep values 
;;



let rec apply_each_mod liste =
 match liste with
|h::t-> begin debug "apply kappa list in progress" ; apply_kappa_mod h; apply_each_mod t end
|[]->begin debug "apply kappa list end" end
;;




let get_kappa dep values = debug "searching a kappa val" ; Hashtbl.find _ASTD_kappa_table_ (dep,values) 
;;








let rec automatic_gestion_of_kappa_values env label dep_list value= match dep_list with
	|(path,var_met,var,prod,cons)::t->let values= List.map (ASTD_environment.find_value_of env) var_met
					in let opt=
					(begin if List.mem label prod then [(((path,var_met,var,prod,cons),values),value,true)] else [] end)
					@(begin if List.mem label cons then [(((path,var_met,var,prod,cons),values),value,false)] else [] end)
					@(automatic_gestion_of_kappa_values env label t value)
					in begin debug ("automatic_gestion of prod cons, nb of mod : "^(string_of_int (List.length opt))) ;opt end
						
	|[]->begin [] end




(**Garbage collector using cons*)

(*let garbage dep_list event
begin if List.mem label cons
								then begin print_endline "remove"
									remove_all_kappa (path,var_met,var,prod,cons) values
									end
								else begin end
							end;*)

