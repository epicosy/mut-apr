

open Printf


(* we copy all debugging output to a file and to stdout *)
let debug_out = ref stdout 
let debug fmt = 
  let k result = begin
	output_string !debug_out result ; 
	output_string stdout result ; 
	flush stdout ; 
    end in
  Printf.kprintf k fmt 
		 
(********************************************)

let my_int_of_string str =
  try 
      let res = ref 0 in 
      Scanf.sscanf str " %i" (fun i -> res := i) ;
      !res
  with _ -> begin 
	if String.lowercase str = "true" then 1
	else if String.lowercase str = "false" then 0 
	else failwith ("cannot convert to an integer: " ^ str)
    end  
		
(*****************************************)
let hashtbl_keys h = 
  Hashtbl.fold (fun key _ l -> key :: l) h []

(********************************)
let hashtbl_values h = 
  Hashtbl.fold (fun _ value l -> value :: l) h []

(*****************************)

(* let hashtbl_lst h = 
      Hashtbl.fold (fun key value lst -> (key, value) :: lst) h [] *)

(*********************************)
let hashtbl2list hash =
  Hashtbl.fold
      (fun key value init -> key :: value :: init)
      hash
      []
      
(***********************************)
(*convert hashtbl into list*)
let hashtbl2assoc_list h = 
  Hashtbl.fold (fun key value l -> (key, value) :: l) h []

(************************************)
(*function that compare two values in a list*)
let compare_fun (_,k1) (_,k2) = compare k1 k2 

(*********************************************) 
					
let main () =
  
  let filenames = ref [] in 
  let passTests = ref 1 in 
  let failTests = ref 1 in
  let faultTec = ref "" in  
  
  let usageMsg = "Prototype No-Specification Bug-Fixer\n" in 
  
  let argDescr = [
      "--pass", Arg.Set_int passTests, " number of passing tests";
      "--fail", Arg.Set_int failTests, " number of failing tests";
      "--fl",  Arg.Set_string faultTec, "fault localization technique"; 
  ] in 
  
  let handleArg str = filenames := str :: !filenames in 
  Arg.parse (Arg.align argDescr) handleArg usageMsg ; 
  
  let debug_str = "faultLoc.txt" in 
  debug_out := open_out debug_str ; 
  at_exit (fun () -> close_out !debug_out) ; 
  

  let fail_t = float_of_int !failTests in
  let pass_t = float_of_int !passTests in 
  let gpath_any = ref false in 
  let npath_any = ref false in   
 
  (**************************************************) 
  
  let gpath_ht = Hashtbl.create 255 in 
  let npath_ht = Hashtbl.create 255 in 
  let fullgpath_ht = Hashtbl.create 255 in 
  let fullnpath_ht = Hashtbl.create 255 in
  let ep = ref 0.0 in
  let ef = ref 0.0 in
  let nf = ref 0.0 in
  let np = ref 0.0 in
  let gpath_ex = Str.regexp "Gpath*" in
  let npath_ex = Str.regexp "Npath*" in
  
  
  (*iterate throug files Gpath and Npath*)
  List.iter ( fun fname ->
	      (*read Gpath and create hashtble for all Gpaths*)
	      if (Str.string_match gpath_ex fname 0) 
	      then begin
		      (*debug "It is a good path file: %s \n" fname;*)
		      
		      let gpath_str = fname in 
		      (try
			      let gpath_fin = open_in gpath_str in 
			      while true do
				  let line = input_line gpath_fin in
				  let i = my_int_of_string line in 
				  gpath_any := true ;
				  (*Create unique list: if item i is alrady in the has*)
				  if not (Hashtbl.mem gpath_ht i) 
				  then begin 
					  Hashtbl.add gpath_ht i 0.0
				      end;
				  
			      done ;
			      
			      
			  with _ -> ()
		      );
		      
		      Hashtbl.iter (fun k v -> 
				    if not (Hashtbl.mem fullgpath_ht k) 
				    then begin
					    Hashtbl.add fullgpath_ht k 1.0
					end else 
					let va = Hashtbl.find fullgpath_ht k in 
					ep := va +. 1.0 ; 
					Hashtbl.replace fullgpath_ht k !ep
							
				   )gpath_ht;
		      
		  (*debug "%s is read and hashtbl is created \n" gpath_str; 
									let gpath_ht_size = Hashtbl.length gpath_ht in  
									debug "%s hashtble size %d \n" gpath_str gpath_ht_size ; 
									Hashtbl.iter (debug "%d\t%f\n") gpath_ht; *)
		      
		  (**************************************)
		  (*check if stmID in the hashtbles 
									if (Hashtbl.mem gpath_ht stmtID) then 
										ep := !ep +. 1.0 ;
										debug " stmtId: %d , ep : %f \n" stmtID !ep; *)
		  end
		       
	      (*read Npath and create hashtble for all Npaths*)
	      else if (Str.string_match npath_ex fname 0) 
	      then begin
		      (*debug "It is a bad path file: %s \n " fname;*)
		      let npath_str = fname in 
		      let npath_any = ref false in 
		      
		      (try
			      let npath_fin = open_in npath_str in 
			      while true do
				  let line = input_line npath_fin in
				  let i = my_int_of_string line in 
				  npath_any := true ;
				  (*if item i is alrady in the has*)
				  if not (Hashtbl.mem npath_ht i) 
				  then begin 
					  Hashtbl.add npath_ht i 0.0
				      end; 
			      done ;
			  with _ -> ()
		      ) ; 
		      
		      Hashtbl.iter (fun k v -> 
				    if not (Hashtbl.mem fullnpath_ht k) 
				    then begin
					    Hashtbl.add fullnpath_ht k 1.0
					end else 
					let va = Hashtbl.find fullnpath_ht k in 
					ef := va +. 1.0 ; 
					Hashtbl.replace fullnpath_ht k !ef
							
				   )npath_ht;
		      
		  (*debug "%s is read and hashtbl is created \n" npath_str; 
									let npath_ht_size = Hashtbl.length npath_ht in   
									debug "%s hashtble size %d \n" npath_str npath_ht_size ; 
									Hashtbl.iter (debug "%d\t%f\n") npath_ht;*)
		      
		  (**************************************)
		  (*check if stmID in the hashtbles 
									if (Hashtbl.mem npath_ht stmtID) then 
										ef := !ef +. 1.0 ;
										debug " stmtId: %d , ef : %f \n" stmtID !ef; *)
		  end;					
	      
	      (****************************************) 
	      
	      Hashtbl.clear gpath_ht ;
	      Hashtbl.clear npath_ht
			    
	    )!filenames ;  
  
  
  
  (*debug "***************************************************" ;
									let fullgpath_ht_size = Hashtbl.length fullgpath_ht in 
									debug "\n fullgood hashtble size %d \n" fullgpath_ht_size ; 
									Hashtbl.iter (debug "%d\t%f\n") fullgpath_ht;
									debug "**************************************************";
									
									
									debug "***************************************************" ;
									let fullnpath_ht_size = Hashtbl.length fullnpath_ht in 
									debug "\n fullbad hashtble size %d \n" fullnpath_ht_size ; 
									Hashtbl.iter (debug "%d\t%f\n") fullnpath_ht;
									debug "**************************************************";*)
  
  
  
  (*read fullpath and create hashtble for fullpath *)
  let path_str = "fullpath"  in  (*cat .goopath path > path  *)
  let path_ht = Hashtbl.create 255 in 
  (try
	  let path_fin = open_in path_str in 
	  while true do
              let line = input_line path_fin in
              let i = my_int_of_string line in 
              npath_any := true ;
              (*if item i is alrady in the has*)
              if not (Hashtbl.mem path_ht i ) then begin 
						      Hashtbl.add path_ht i 0.0;
						  end ;      
	  done ;
      with _ -> ()
  ) ; 
  (*debug "%s is read and hashtbl is created \n" path_str; 
  let path_ht_size = Hashtbl.length path_ht in   
  debug "fullpath hashtble size %d \n" path_ht_size ; 
   Hashtbl.iter (printf "%d\t%f\n") path_ht; *)
  
  
  (*List of keys *)
  let sus_ht= Hashtbl.create 225 in 
  (*debug "flaot of int %f" fail_t ;*)
  let m = ref 0 in
  let keys_lst = hashtbl_keys path_ht in
  (*debug "print list of keys \n"  ; *)

  
  
  List.iter ( fun k -> 
              let exe_pass = ref 0.0 in
              let exe_fail = ref 0.0 in
              let stmtID = List.nth keys_lst !m in
              m := !m + 1 ; 
	      if Hashtbl.mem fullgpath_ht stmtID
	      then begin
		      let vp = Hashtbl.find fullgpath_ht stmtID in 
		      exe_pass := vp ; 
		  (*debug "exe_pass for stmt: %d is %f \n " stmtID !exe_pass;*)
		  end; 
	      
	      if Hashtbl.mem fullnpath_ht stmtID 
	      then begin
		      let vf= Hashtbl.find fullnpath_ht stmtID in
		      exe_fail := vf;
		  (*debug "exe_fail for stmt: %d is %f \n " stmtID !exe_fail;*)
		  end;
	      
	      
	      (* compute sus score *)
	      nf := fail_t -. !exe_fail;
	      np := pass_t -. !exe_pass;	
	      let sus = ref 0.0 in
	      (*** Jaccard **)	     
	      if !faultTec = "Jaccard" 
	      then begin
		      if !exe_fail = 0.0 then 
			  sus := 0.0 
		      else
			  sus := !exe_fail /. (fail_t +. !exe_pass) ;   (** we implement Jaccard, we only use the stmtID with sus > 0  **)
		      (*debug "sus for stmt %d is %f \n " stmtID !sus;*)
		     (* if !sus > 0.0 then*)
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end 
	      (*** Optimal ***)
	      else if !faultTec = "Optimal" 
	      then begin
		      if !nf > 0.0 then 
			  sus := -1.0  
		      else if !nf = 0.0 then
			  sus := !np ;  
		      (*debug "sus for stmt %d is %f \n " stmtID !sus;*)
		       (*if !sus >= 0.0 then*)
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;

		  end
	      (** Ochiai**)
	      else if !faultTec = "Ochiai"
	      then begin
		      if !exe_fail = 0.0 then 
			  sus := 0.0 
		      else 
			  sus := !exe_fail /. sqrt(fail_t *. (!exe_fail +. !exe_pass)) ;  
		      (*debug "sus for stmt %d is %f \n " stmtID !sus;*)
		      (*if !sus > 0.0 then*) 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;

		  end  
	      else if !faultTec = "Ta"
	      then begin
		      if !exe_fail = 0.0 then 
			  sus := 0.0 
		      else 
			  sus := (!exe_fail /. fail_t) /. ( (!exe_fail /. fail_t) +. (!exe_pass +. pass_t) ) ;  
		      (*debug "sus for stmt %d is %f \n " stmtID !sus;*)
		      (*if !sus > 0.0 then*) 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end 
	      else if !faultTec = "Optimalp"
	      then begin
		     if !exe_fail = 0.0 && !exe_pass = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := !exe_fail -. (!exe_pass /. (!exe_pass +. !np +. 1.0)) ;  
		      (*if !sus >= 0.0 then*) 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Ample" (*does zero count in this case ?*)
	      then begin
		     if !exe_fail = 0.0 && !exe_pass = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := abs_float ((!exe_fail /. (!exe_fail +. !nf)) -. (!exe_pass /. (!exe_pass +. !np))) ;  
		      (*if !sus > 0.0 then*)
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Ample2" (*does zero count in this case ?*)
	      then begin
		     if !exe_fail = 0.0 && !exe_pass = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := (!exe_fail /. (!exe_fail +. !nf)) -. (!exe_pass /. (!exe_pass +. !np)) ;  
		      (*if !sus > 0.0 then*) 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Wong1" (*does zero count in this case ?*)
	      then begin
		     if !exe_fail = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := !exe_fail ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Wong2" (*does zero count in this case ?*)
	      then begin
		     if !exe_fail = 0.0 && !exe_pass = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := !exe_fail -. !exe_pass ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Wong3"   (*does zero count in this case ?*)
	      then begin
		      let h = ref 0.0 in

		      if !exe_pass <= 2.0 then
			  h := !exe_pass
		      else if !exe_pass > 2.0 && !exe_pass <= 10.0 then
			  h := 2.0 +. 0.1 *. (!exe_pass -. 2.0)
		      else if !exe_pass > 10.0 then
			  h := 2.8 +. 0.001 *. (!exe_pass -. 10.0);

  		     if !exe_fail = 0.0  && !h = 0.0 then 
		      sus := 0.0 
		     else 
		       sus := !exe_fail -. !h ;  
		      (*if !sus > 0.0 then *)
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Kul"   (*Kulcynskil *)
	      then begin
		     if !exe_fail = 0.0 then 
			  sus := 0.0
		     else 
		       sus := !exe_fail /. (!nf +. !exe_pass) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	     
	      else if !faultTec = "Russ"   (*Russell and Rao*)
	      then begin
		     if !exe_fail = 0.0 then 
			  sus := 0.0
		     else 
		       sus := !exe_fail /. (!exe_fail +. !nf +. !exe_pass +. !np) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end   
	      else if !faultTec = "Sdice"   (*Sorenseon Dice*)
	      then begin
		     if !exe_fail = 0.0 then 
			  sus := 0.0
		     else 
		       sus := (2.0 *. !exe_fail) /. (!exe_fail +. !nf +. !exe_pass) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end 
	      else if !faultTec = "Dice"   (*Dice*)
	      then begin
		     if !exe_fail = 0.0 then 
			  sus := 0.0
		     else 
		       sus := 2.0 *. !exe_fail /. (!exe_fail +. !nf +. !exe_pass ) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end  
	      else if !faultTec = "Kul2"   (*Kulcynskil *)
	      then begin
		     if !exe_fail = 0.0 then 
			  sus := 0.0
		     else 
		       sus := 0.5 *. ((!exe_fail /. (!exe_fail +. !nf)) /. (!exe_fail /. (!exe_fail +. !exe_pass))) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "SimpleMatch"   (*Simple Matching*)
	      then begin
		     if !exe_fail = 0.0 && !np = 0.0 then 
			  sus := 0.0
		     else 
		       sus := ( (!exe_fail +. !np) /. (!exe_fail +. !nf +. !exe_pass +. !np) ) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "M1"   
	      then begin
		     if !exe_fail = 0.0 && !np = 0.0 then 
			  sus := 0.0
		     else 
		       sus := (!exe_fail +. !np) /. (!nf +. !exe_pass ) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "M2"   
	      then begin
		     if !exe_fail = 0.0  then 
			  sus := 0.0
		     else 
		       sus := !exe_fail  /. (!exe_fail +. !np +. 2.0 *. (!nf +. !exe_pass)) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	       else if !faultTec = "Roger"   
	      then begin
		     if !exe_fail = 0.0 && !np = 0.0 then 
			  sus := 0.0
		     else 
		       sus := (!exe_fail +. !np)  /. (!exe_fail +. !np +. 2.0 *. (!nf +. !exe_pass)) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Hamm" (*Hamming*)   
	      then begin
		     if !exe_fail = 0.0 && !np = 0.0 then 
			  sus := 0.0
		     else 
		       sus := !exe_fail +. !np  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Hamman" (*Hamman*)   
	      then begin
		      sus := (!exe_fail +. !np -. !nf -. !exe_pass ) /. (!exe_fail +. !nf +. !exe_pass +. !np)  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Ochiai2"    
	      then begin
		      if !exe_fail = 0.0 && !np = 0.0 then 
			  sus := 0.0
		     else if (!exe_fail +. !exe_pass) = 0.0 || (!np +. !nf) = 0.0 || (!exe_fail +. !nf) = 0.0  || (!exe_pass +. !np) = 0.0 then
			 sus := 0.0
		     else
		      sus := (!exe_fail *. !np ) /. (sqrt ( (!exe_fail +. !exe_pass) *. (!np +. !nf) *. (!exe_fail +. !nf) *. (!exe_pass +. !np) ) );  
		      (*if !sus > 0.0 then*) 
			if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Geo"    (*Geometric Mean*)
	      then begin
		      sus := ((!exe_fail *. !np ) -. (!nf -. !exe_pass)) /. sqrt ((!exe_fail +. !exe_pass) *. (!np +. !nf) *. (!exe_fail +. !nf) *. (!exe_pass +. !np)) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Arith"    (*Arithmetic Mean*)
	      then begin
		      sus := ((2.0 *. !exe_fail *. !np ) -. (2.0 *. !nf *. !exe_pass)) /. (((!exe_fail +. !exe_pass) *. (!np +. !nf)) +. ((!exe_fail +. !nf) *. (!exe_pass +. !np)))  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Choen"    
	      then begin
		      sus := ((2.0 *. !exe_fail *. !np ) -. (2.0 *. !nf *. !exe_pass)) /. ((!exe_fail +. !exe_pass) *. (!np +. !nf) *. (!exe_fail +. !nf) *. (!exe_pass +. !np))  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
		  else if !faultTec = "Scot"    
	      then begin
		      sus := ((4.0 *. !exe_pass *. !np ) -. (4.0 *. !nf *. !exe_pass)) -. ((!nf -. !exe_pass) *. (!nf -. !exe_pass)) /. ((2.0 *. !exe_fail +. !nf +. !exe_pass) *. (2.0 *. !np +. !nf +. !exe_pass))  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Fle" (*Fleiss*)    
	      then begin
		      sus := ((4.0 *. !exe_fail *. !np ) -. (4.0 *. !nf *. !exe_pass) -. ((!nf -. !exe_pass) *.(!nf -. !exe_pass))) /. 
				 ((2.0 *. !exe_fail +. !nf +. !exe_pass) +. (2.0 *. !np +. !nf +. !exe_pass) )  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Harmonic" (*Harmonic Mean*)    
	      then begin
		      sus := ((!exe_fail *. !np) -. (!nf *. !exe_pass)) *. ( ((!exe_fail +. !exe_pass) *. (!np +. !nf)) +. ((!exe_fail +. !nf) *. (!exe_pass +. !np))) /. 
				 ((!exe_fail +. !exe_pass) *. (!np +. !nf) *. (!exe_fail +. !nf) *. (!exe_pass +. !np))  ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Euc" (*Euclid*)    
	      then begin
		      sus := sqrt (!exe_fail +. !np ) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Rogo1"    
	      then begin
		      sus := 0.5 *. ((!exe_pass /. ( (2.0 *. !exe_fail ) +. !nf +. !exe_pass) ) +. (!np /. ((2.0 *. !np) +. !nf +. !exe_pass))) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Rogo2"    
	      then begin
		      sus := 0.25 *. ( (!exe_pass /. (!exe_fail +. !exe_pass)) +. (!exe_fail /. (!exe_fail +. !nf)) +. (!np /. (!np +. !exe_pass)) +. (!np /. (!np +. !nf))) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "And" (*Anderberg*)    
	      then begin
		      if !exe_fail = 0.0 then
			  sus := 0.0 
		      else
		      sus :=  !exe_fail /. (!exe_fail +. 2.0 *. (!nf +. !exe_pass)) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	       else if !faultTec = "Sokal"    
	      then begin
		      if !exe_fail = 0.0 && !np = 0.0 then
			  sus := 0.0 
		      else
		      sus :=  (2.0 *. (!exe_fail +. !np)) /. (2.0 *. (!exe_fail +. !np) +. !nf +. !exe_pass ) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else if !faultTec = "Good" (*Goodman *)    
	      then begin
		      sus :=  ( (2.0 *. !exe_fail) -. !nf -. !exe_pass ) /. ((2.0 *. !exe_fail) +. !nf +. !exe_pass) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	     (* else if !faultTec = "Over" (* Overlap *)    
	      then begin
		      if !exe_fail = 0.0 then
			  sus := 0.0 
		      else
		      sus :=  ( (2.0 *. !exe_fail) -. !nf -. !exe_pass ) /. ((2.0 *. !exe_fail) +. !nf +. !exe_pass) ;  
		      if !sus > 0.0 then 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end*)
		       else if !faultTec = "Zo" (*Zoltar *)    
	      then begin
		      if !exe_fail = 0.0 then
			  sus := 0.0 
		      else
		      sus :=  ( !exe_fail /. (!exe_fail +. !nf +. !exe_pass +. ((10000.0 *. !nf *. !exe_pass) /. !exe_fail))) ;  
		      (*if !sus > 0.0 then*) 
			  if not (Hashtbl.mem sus_ht stmtID) then
			      Hashtbl.add sus_ht stmtID !sus ;
		  end
	      else 
     		  debug "faultTec is not know \n";
	      ()
		  
	    ) keys_lst ; 
  
  
  

  (*Hashtbl.iter (debug "%d\t%f\n") sus_ht; *)
  
  
  (*debug "print list ordered \n"  ; *)
  
  let suslst = List.rev (List.sort compare_fun (hashtbl2assoc_list sus_ht)) in
  List.iter
      (fun (key, value) ->
       let value = Hashtbl.find sus_ht key in
       debug "%d \t" key; 
       debug " %f \n" value;
       
      ) suslst ; 
  
  
;;

    main ();;
