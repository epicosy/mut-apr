
(* we copy all debugging output to a file and to stdout *)
(*let debug_out = ref stdout 
let debug fmt = 
  let k result = begin
    output_string !debug_out result ; 
    output_string stdout result ; 
    flush stdout ; 
  end in
  Printf.kprintf k fmt*) 



let filename = ref ""
let listSuspicious = ref []
let min_compute (object_list:(float) list) =
    let min = ref (List.nth object_list 0) in
    List.iter (fun x ->
        if x < !min then min := x;
    ) object_list;
    !min

let max_compute (object_list:(float) list) =
    let min = ref (List.nth object_list 0) in
    List.iter (fun x ->
        if x > !min then min := x;
    ) object_list;
    !min

let main () = begin

  let usageMsg = "计算统计信息\n" in 
  let argDescr = [
   (*"-f", Arg.Set_string func_name, "X use as object function name";*)

  ] in ();

  let handleArg str = filename := str in 
  Arg.parse (Arg.align argDescr) handleArg usageMsg ; 
  (*let start = Unix.gettimeofday () in *)

  if !filename <> "" then begin

	let statics_string = (Filename.chop_extension !filename) ^ "-normalized.txt" in(*构造并打开输出文件*)
        let flag_open = [Open_creat;Open_append] in
	let statics_file = Pervasives.open_out_gen flag_open 0o666 statics_string in

	let space_regexp = Str.regexp "[ \t]+" in
	(*let maxSuspiciousness = ref 0.0 in*)

	(*提取最小值*)
	let fin = open_in !filename in(*读取统计文件*)
	try 
	   while true do(*开始后续行处理*)
	     let string_of_file = input_line fin in
	     let words = Str.split space_regexp string_of_file in (*Str.bounded_split*) (*debug "ni:%s\n" (List.nth words 0);*)
	     listSuspicious := 	(float_of_string (List.nth words 1)) :: !listSuspicious;
	   done;
	with  _ ->
             close_in fin;
	let minSuspiciousness = min_compute !listSuspicious in
	let maxSuspiciousness = max_compute !listSuspicious in
	let betweenSuspiciousness = maxSuspiciousness -. minSuspiciousness in

	(*计算兵书出新可疑值*)
        if betweenSuspiciousness <> 0.0 then
		let fin = open_in !filename in(*读取统计文件*)
		try
			while true do(*开始后续行处理*)
				let string_of_file = input_line fin in	
				let words = Str.split space_regexp string_of_file in
				let new_suspicious =  ((float_of_string (List.nth words 1)) -. minSuspiciousness) /. betweenSuspiciousness in
				if new_suspicious <> 0.0 then
					  (*let cmd = "grep -w Statement_ID " ^ statics_string ^ "  >& /dev/null" in (* 如果statistic.txt没有头文件的话，打印一行头文件*)
        					(match Unix.system cmd with
         						| Unix.WEXITED(0) ->  ()
        						 | _ -> Printf.fprintf statics_file  "%-12s %s\n" "Statement_ID" "Suspiciousness";);*)
					Printf.fprintf statics_file  "%-7s %10.6f\n" (List.nth words 0) new_suspicious;(*输出第一行*)
			done;		
		with  x_temp -> ();
	else failwith "!!!betweenSuspicious is 0!!!!!!!!!!!!!!!!!!!!!\n"; 	
  end

(*
  if !filename <> "" then begin
	(*统计列表************************)
	let list_time_compile = ref [] in
	let list_time_goodtest = ref [] in
	let list_time_badtest = ref [] in
	let list_time_sizediff = ref [] in
	let list_time_mutation = ref [] in
	let list_time_fitness = ref [] in
	let list_time_others = ref [] in
	let list_time_Total_se = ref [] in
	let list_time_check_time = ref [] in
	let list_time_Total = ref [] in
	let list_time_compile_count = ref [] in
	let list_time_fitness_count = ref [] in
	let list_time_compile_tried_count = ref [] in
	let space_regexp = Str.regexp "[ \t]+" in
	(*统计列表************************)

  	let fin = open_in !filename in(*读取统计文件*)
	try while true do
		let string_of_file = input_line fin in
		if string_of_file <> "" && string_of_file.[0] <> '#' then (*允许注释和空行，但必须在此将此类行忽略*)
		   begin
			let words = Str.split space_regexp string_of_file in (*Str.bounded_split*) (*debug "ni:%s\n" (List.nth words 0);*)
			if ( List.length words <> 13 ) then failwith "!!!length failed"; 
			list_time_compile := (List.nth words 0) :: !list_time_compile;
			list_time_goodtest := (List.nth words 1) :: !list_time_goodtest;
			list_time_badtest := (List.nth words 2) :: !list_time_badtest;
			list_time_sizediff := (List.nth words 3) :: !list_time_sizediff;
			list_time_mutation := (List.nth words 4) :: !list_time_mutation;
			list_time_fitness := (List.nth words 5) :: !list_time_fitness;
			list_time_others := (List.nth words 6) :: !list_time_others;

			list_time_Total_se := (List.nth words 7) :: !list_time_Total_se;
			list_time_check_time := (List.nth words 8) :: !list_time_check_time;

			list_time_Total := (List.nth words 9) :: !list_time_Total;
			list_time_compile_count := (List.nth words 10) :: !list_time_compile_count;
			list_time_fitness_count := (List.nth words 11) :: !list_time_fitness_count;
			list_time_compile_tried_count := (List.nth words 12) :: !list_time_compile_tried_count;			
		   end
	    done;
	with  x_temp -> begin
	     match x_temp with
              | (Failure "!!!length failed") -> 
                  raise x_temp;
	      | _ -> ();
             close_in fin;
            end;
	(*debug "length:%d\n" (List.length !list_time_compile);*)(* 计算总值*)
	let total_time_compile = total_compute !list_time_compile in 
	let total_time_goodtest = total_compute !list_time_goodtest in 
	let total_time_badtest = total_compute !list_time_badtest in 
	(*let total_time_sizediff = total_compute !list_time_sizediff in 
	let total_time_mutation = total_compute !list_time_mutation in 
	let total_time_fitness = total_compute !list_time_fitness in *)
	let total_time_others = total_compute !list_time_others in 

	let total_time_Total_se = total_compute !list_time_Total_se in 
	let total_time_check_time = total_compute !list_time_check_time in 

	let total_time_Total = total_compute !list_time_Total in 
	let total_time_compile_count = total_compute !list_time_compile_count in 
	let total_time_fitness_count = total_compute !list_time_fitness_count in
 	let total_time_compile_tried_count = total_compute !list_time_compile_tried_count in 
	
	let avg_time_compile = total_time_compile /. total_time_compile_count in (* 计算均值值*) 
	let avg_time_goodtest = total_time_goodtest /. total_time_compile_count in 
	let avg_time_badtest = total_time_badtest /. total_time_compile_count in
	let sum_per_validation =  avg_time_compile +. avg_time_goodtest +. avg_time_badtest in
	(*let avg_time_sizediff = total_time_sizediff /. list_time_compile_count in 
	let avg_time_mutation = total_time_mutation /. list_time_compile_count in  
	let avg_time_fitness = total_time_fitness /. list_time_compile_count in *)
	let avg_time_others = total_time_others /. (float (List.length !list_time_compile)) in 
	let avg_time_Total_se = total_time_Total_se /. (float (List.length !list_time_compile)) in 
	let avg_time_check_time = total_time_check_time /. (float (List.length !list_time_compile)) in 
	let avg_time_Total = total_time_Total /. (float (List.length !list_time_compile)) in 

	let statics_string = (Filename.chop_extension !filename) ^ "-sum.txt" in
        let flag_open = [Open_creat;Open_append] in
	let statics_file = Pervasives.open_out_gen flag_open 0o666 statics_string in

(* 统计总量******************************)
let sepstar = "*********************************************************************" in
Printf.fprintf statics_file "%s\n%s\n" sepstar "Total Statistic:";

Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_Total(s)" total_time_Total;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_Total_se(s)" total_time_Total_se;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_compile(s)" total_time_compile;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_goodtest(s)" total_time_goodtest;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_badtest(s)" total_time_badtest;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_check_time(s)" total_time_check_time;
Printf.fprintf statics_file "\t%s\n" "##########################################";
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "success count" (float (List.length !list_time_compile));
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_compile_count" total_time_compile_count ;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_fitness_count" total_time_fitness_count ;
Printf.fprintf statics_file  "\t%-30s: %10.3f\n" "total_time_compile_tried_count" total_time_compile_tried_count ;

Printf.fprintf statics_file "%s\n" sepstar;
(* 统计总量******************************)

	Printf.fprintf statics_file "%10s %10s %10s %10s %10s %10s %10s %10s %19s %19s %19s\n"(*运行可打印数据头*)  
          "compile" "good test" "bad test" "sum_three"  "others" "Total_se" "check_time" "Total" "sum_compile_count" "sum_fitness_count" "compile_tried_count";
  	Printf.fprintf statics_file "%10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %19.0f %19.0f %19.0f\n"
 	  avg_time_compile avg_time_goodtest avg_time_badtest sum_per_validation avg_time_others avg_time_Total_se avg_time_check_time avg_time_Total total_time_compile_count total_time_fitness_count total_time_compile_tried_count;

  end *)
end ;;

main () ;; 
