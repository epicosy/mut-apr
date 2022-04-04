(* Disjoint Timings *) 
type t = {
  name : string; 
  start : float ;
  mutable holes : float ; 
} 


let stack = ref [] 

let totals = Hashtbl.create 255 
let invocations = Hashtbl.create 255 

let load_started = ref (Unix.gettimeofday ())

let clear () = 
  Hashtbl.clear totals ; 
  Hashtbl.clear invocations ; 
  stack := [] ;
  load_started := Unix.gettimeofday () 

let time name f a = 
  let start = Unix.gettimeofday () in 
  Hashtbl.replace invocations name 
    (let x = try Hashtbl.find invocations name with Not_found -> 0 in x+1) ;
  let record = {
    name = name ;
    start = start ;
    holes = 0. ;
  } in
  stack := record :: !stack ;
  let finished () = 
    let myrec = List.hd !stack in
    let now = Unix.gettimeofday () in 
    let my_delta = (now -. myrec.start) in 
    let my_time = my_delta -. (myrec.holes) in 
    stack := List.tl !stack ; 
    begin 
    match !stack with
    | [] -> ()
    | below :: others -> below.holes <- below.holes +. my_delta
    end ;
    let sofar = try Hashtbl.find totals name with Not_found -> 0.0 in 
    Hashtbl.replace totals name (sofar +. my_time) 
  in 
  try
    let res = f a in
    finished () ; 
    res 
  with e -> 
    finished () ;
    raise e 

let hashtbl_to_list ht =
  let lst = ref [] in
  Hashtbl.iter (fun  a b -> lst := (a,b) :: !lst) ht ;
  !lst

let print chn msg =
  let flag_open = [Open_creat;Open_append] in
(*let statics_file = Pervasives.open_out "./statistic.txt" in*)
  let statics_file = Pervasives.open_out_gen flag_open 0o666 "./statistic.txt" in
  let lst = hashtbl_to_list totals in
  let total = List.fold_left (fun acc (ename,et) -> acc +. et) 0.0 lst in 
  let sorted = List.sort (fun (a,at) (b,bt) -> compare at bt) lst in 
  Printf.fprintf chn "  %-30s %8s %7s = %s\n"  
    "Activity Name" "Count" "Seconds" "Percent of Total Time" ;

(*********************************统计要的数据到staticas.txt****************************************)
  (*try 
    let fin = open_in "./statics.txt" in 
    let count = ref 0 in
    (try while true do
      let line = input_line fin in
      ignore line ;
      incr count; 
        Printf.fprintf statics_file "%10s %10s %10s %10s %10s %10s %10s %15s %15s\n"  
          "compile" "good test" "bad test" "size diff" "mutation" "fitness" "Total" "compile_count" "fitness_count";
    done ;  with _ -> begin close_in fin ; end) (**0.的作用是与函数返回值匹配*)
  with _ ->
        Printf.fprintf statics_file "%10s %10s %10s %10s %10s %10s %10s %15s %15s\n"  
          "compile" "good test" "bad test" "size diff" "mutation" "fitness" "Total" "compile_count" "fitness_count";*)


if chn = stdout then begin

  let compile_time = Hashtbl.find totals "compile" in
  let good_test_time = Hashtbl.find totals "good test" in
  let bad_test_time = Hashtbl.find totals "bad test" in
  let size_diff_time = Hashtbl.find totals "size diff" in
  let mutation_time = Hashtbl.find totals "mutation" in
  let fitness_time = try Hashtbl.find totals "fitness" with Not_found -> 0.0 in(*一直不懂为什么下面被注释的代码不起作用*)
  let check_time = try Hashtbl.find totals "check" with Not_found -> 0.0 in(*一直不懂为什么下面被注释的代码不起作用*)
  let total_se = total -. check_time in 
  
let others_time = total-.bad_test_time -. good_test_time -. compile_time -. check_time in
   (*let fitness_time = Hashtbl.find totals "fitness" in*)
  (*let fitness_time = ref 0. in(*注意以后加try的时候一定先把变量提出后在进行，也就是ref*)
  try(**注意当一次就变异成功时，totals并没有关于fitness的时间，其实际为0*)
    fitness_time := ( Hashtbl.find totals "fitness" )
  with Not_found ->  fitness_time := 0.*)
  let compile_tried = Hashtbl.find invocations "compile" in (*尝试编译次数，实际为去掉cache后的次数*)
  let compile_count = Hashtbl.find invocations "bad test" in (*实际编译次数等于bad test执行次数*)
  Hashtbl.replace invocations "compile" compile_count;
  let fitness_count = Hashtbl.find invocations "fitness" in

  let cmd = "grep -w compile  statistic.txt >& /dev/null" in (* 如果statistic.txt没有头文件的话，打印一行头文件*)
        (match Unix.system cmd with
         | Unix.WEXITED(0) ->  ()
         | _ -> Printf.fprintf statics_file "%10s %10s %10s %10s %10s %10s %10s %10s %10s %10s %15s %15s %15s\n"(*运行可打印数据头*) 
          "compile" "good test" "bad test" "size diff" "mutation" "fitness" "others" "Total_se" "check_time" "Total" "compile_count" "fitness_count" "compile_tried";);
  (*Printf.fprintf statics_file "%10s %10s %10s %10s %10s %10s %10s %10s %10s %10s %15s %15s %15s\n"(*运行可打印数据头*) 
          "compile" "good test" "bad test" "size diff" "mutation" "fitness" "others" "Total_se" "check_time" "Total" "compile_count" "fitness_count" "compile_tried";*)
  Printf.fprintf statics_file "%10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %10.3f %15d %15d %15d\n"
 compile_time good_test_time bad_test_time size_diff_time mutation_time fitness_time others_time total_se check_time total compile_count fitness_count compile_tried;

end;
(*************************************************************************)
(*********************************统计要的数据到staticas.txt****************************************)

  List.iter (fun (l,t) ->
    let perc = (100.0 *. t /. total) in 
    if perc > 0.01 then 
      Printf.fprintf chn "  %-30s %8d %7.3f = %g%%\n" l 
        (Hashtbl.find invocations l) t perc 
  ) sorted ;

  let now = Unix.gettimeofday () in 
  let delta = now -. (!load_started) in 

  (try 
   let check_time = Hashtbl.find totals "check" in
   let total_se = total -. check_time in
  Printf.fprintf chn "  %-30s          %7.3f = %g%%\n" "Seach Patch" total_se (100. *. total_se /. total)   
  with _ -> ());

  Printf.fprintf chn "  %-30s          %7.3f = %g%% (avg CPU usage)\n" "TOTAL" total (100. *. total /. delta);

 

(*
(* Disjoint Timings *)

type t = { mutable start : float; 
           mutable above_me : float ;
         }

                                        (* The stack of current path through 
                                         * the hierarchy. The first is the 
                                         * leaf. *)

let stack : (int,(t list)) Hashtbl.t = 
  Hashtbl.create 31
  (*
  Array.init num_thread (fun _ -> 
    [ { start = 0.0 ; above_me = 0.0 ; } ] 
  ) 
  *)

let record = Hashtbl.create 31
(* Array.init num_thread (fun _ -> 
    Hashtbl.create 127 
  )  *) 

let update_record idx name duration =
  let record_idx = 
    try Hashtbl.find record idx 
    with Not_found -> begin 
      let res = Hashtbl.create 127 in
      Hashtbl.add record idx res ;
      res
    end 
  in 
  let sofar = 
    if Hashtbl.mem record_idx name then
      Hashtbl.find record_idx name 
    else 
      0.0
  in
  Hashtbl.replace record_idx name (sofar +. duration)

let time name f a =
  let idx = 0 (* (Thread.id (Thread.self ())) *) in 
  let stack_idx = 
    try Hashtbl.find stack idx
    with Not_found -> begin
      let res = [ { start = 0.0 ; above_me = 0.0 ; } ] in
      Hashtbl.add stack idx res ;
      res
    end
  in 
  let stack_idx = 
    { start = (Unix.times ()).Unix.tms_utime ; above_me = 0.0} 
    :: stack_idx
  in
  Hashtbl.replace stack idx stack_idx ; 
  try 
    let result = f a in
    let later = (Unix.times ()).Unix.tms_utime in
    let r = List.hd stack_idx in
    Hashtbl.replace stack idx (List.tl stack_idx) ;
    let above_me = List.hd stack_idx in 
    let duration = later -. (r.start +. r.above_me) in
    above_me.above_me <- above_me.above_me +. r.above_me +. duration ;
    update_record idx name duration ;
    result 
  with e -> begin
    let later = (Unix.times ()).Unix.tms_utime in
    let r = List.hd stack_idx in
    Hashtbl.replace stack idx (List.tl stack_idx) ;
    let above_me = List.hd stack_idx in 
    let duration = later -. (r.start +. r.above_me) in
    above_me.above_me <- above_me.above_me +. r.above_me +. duration ;
    update_record idx name duration ;
    raise e 
  end 

let print chn msg = 
  Hashtbl.iter (fun idx record -> 
    let l = ref [] in 
    let total = ref 0.0 in 
    Hashtbl.iter (fun name time ->
      total := !total +. time ; 
      l := (name,time) :: !l 
    ) record ;
    let l = List.sort (fun (a,b) (c,d) -> compare b d) !l in 
    List.iter (fun (l,t) ->
      Printf.fprintf chn "%d %-30s %7.3f = %g%%\n" idx l t (100.0 *. t /. !total)
    ) l ;
    Printf.fprintf chn "%d %-30s %7.3f\n" idx "TOTAL" !total 
  ) record 

(* XXXYYZ
 *
 * [ { s = 0 ; a = 0; } ]
 * [ { s = 0 ; a = 0; } ; { s = 3 ; a = 0; } ]
 * [ { s = 0 ; a = 0; } ; { s = 3 ; a = 0; } ; { s = 5 ; a = 0 } ]
 * [ { s = 0 ; a = 0; } ; { s = 3 ; a = 1; } ] ( Z = 1 )
 * [ { s = 0 ; a = 3; } ; ] ( Z = 1 ; Y = 2 )
 * ( X = 3 ; Y = 2 ; Z = 1 ) 
 *)
 *)
