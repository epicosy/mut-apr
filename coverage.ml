(* Transform a C program to print out all of the statements it visits
 * to stderr. Basically, this computes statement coverage a la standard
 * testing. 
 *
 * This is used as a first step in Weimer's Genetic Programming approach to
 * evolving a program variant that adheres to some testcases. 
 *
 * You apply 'coverage' to a single C file (use CIL to combine a big
 * project into a single C file) -- say, foo.c. This produces:
 *
 * foo.ast  -- a serialized CIL AST of the *original* program
 *
 * foo.ht   -- a hashtable mapping from numbers to
 *             'statements' in the *original* foo.c
 *
 * 'stdout' -- an *instrumented* version of foo.c that prints out
 *             each 'statement' reached at run-time into
 *             the file foo.path
 *
 * Typical usage: 
 *
 *   ./coverage foo_comb.c > foo_coverage.c 
 *) 
open Pervasives
open Printf
open Cil
open Pretty

let lval va = Lval((Var va), NoOffset)
let fprintf_va = makeVarinfo true "fprintf" (TVoid [])
let fopen_va = makeVarinfo true "fopen" (TVoid [])
let fflush_va = makeVarinfo true "fflush" (TVoid [])
let memset_va = makeVarinfo true "memset" (TVoid [])
let stderr_va = makeVarinfo true "_coverage_fout" (TPtr(TVoid [], []))
let fopen = lval (makeVarinfo true "fopen" (TVoid []))
let fclose = lval (makeVarinfo true "fclose" (TVoid []))
let fprintf = Lval((Var fprintf_va), NoOffset)
let fopen = Lval((Var fopen_va), NoOffset)
let fflush = Lval((Var fflush_va), NoOffset)
let stderr = Lval((Var stderr_va), NoOffset)
let memset = Lval((Var memset_va), NoOffset)
let counter = ref 1 
let gloalVar = ref []
let multithread_coverage = ref false(*是否多线程，防止写入被覆盖*)
let uniq_coverage = ref false
let uniq_array_va = ref
  (makeGlobalVar "___coverage_array" (TArray(charType,None,[])))


(*注意Hashtbl.t表只有当文中已引用过时，方可创建*)
let massive_hash_table = Hashtbl.create 8000 
let id_fun_hash_table = Hashtbl.create 8000 (*id语句与函数对照表*)
let fun_GLvar_hash_table = Hashtbl.create 8000 (*(函数名, (全局and局部变量名)list) Hashtbl.t *)
let stmt_var_hash_table = Hashtbl.create 8000 (*(语句id, (局部变量名)list) Hashtbl.t *)

(* 
 * Here is the list of CIL statementkinds that we consider as
 * possible-to-be-modified
 * (i.e., nodes in the AST that we may mutate/crossover via GP later). 
 *)
let can_trace sk = match sk with
  | Instr _ 
  | Return _  
  | If _ 
  | Loop _
  | Goto _ 
  -> true
 
  | Break _ 
  | Continue _ 
  | Switch _ 
  | Block _ 
  | TryFinally _ 
  | TryExcept _ 
  -> false 

let get_next_count () = 
  let count = !counter in 
  incr counter ;
  count 

let debug_out = ref stdout 
let debug fmt = 
  let k result = begin
    output_string !debug_out result ; 
    flush stdout ; 
  end in
  Printf.kprintf k fmt 


let compare_list (list1:(string)list) (list2:(string)list) =(*list1是否包含在list2中*)
  let flag = ref true in
     List.iter (fun x->
        if (not (List.mem x list2)) then
           flag := false
     ) list1;
  !flag
  

(* This makes a deep copy of an arbitrary Ocaml data structure *) 
let copy (x : 'a) = 
  let str = Marshal.to_string x [] in
  (Marshal.from_string str 0 : 'a) 
  (* Cil.copyFunction does not preserve stmt ids! Don't use it! *) 

(*打印无行代码的文件2012.06.04**************************************************************************)
class noLineCilPrinterClass = object
  inherit defaultCilPrinterClass as super 
  method pGlobal () (g:global) : Pretty.doc = 
    match g with 
    | GVarDecl(vi,l) when
      (not !printCilAsIs && Hashtbl.mem Cil.builtinFunctions vi.vname) -> 
      (* This prevents the printing of all of those 'compiler built-in'
       * commented-out function declarations that always appear at the
       * top of a normal CIL printout file. *) 
      Pretty.nil 
    | _ -> super#pGlobal () g

  method pLineDirective ?(forcefile=false) l = 
    Pretty.nil
end 
(*打印无行代码的文件**************************************************************************)
let noLineCilPrinter = new noLineCilPrinterClass
(*打印无行代码的文件**************************************************************&&&&&&&&&&&&*)

class numToZeroVisitor = object
  inherit nopCilVisitor
  method vstmt s = s.sid <- 0 ; DoChildren
end 
let my_zero = new numToZeroVisitor
let old_coverage_bug = ref false 

(* 
 * This visitor changes empty statement lists (e.g., the else branch in if
 * (foo) { bar(); } ) into dummy statements that we can modify later. 
 *)
class emptyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      if b.bstmts = [] then 
        mkBlock [ mkEmptyStmt () ] 
      else b 
    ))
end 

(* This visitor makes every instruction into its own statement. *)
class everyVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      let stmts = List.map (fun stmt ->
        match stmt.skind with
        | Instr([]) -> [stmt] 
        | Instr(first :: rest) -> 
            ({stmt with skind = Instr([first])}) ::
            List.map (fun instr -> mkStmtOneInstr instr ) rest 
        | other -> [ stmt ] 
      ) b.bstmts in
      let stmts = List.flatten stmts in
      { b with bstmts = stmts } 
    ))
end 

(* This visitor walks over the C program AST and builds the hashtable that
 * maps integers to statements. *) 
class numVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      List.iter (fun b -> 
        if can_trace b.skind then begin
          let count = get_next_count () in 
          b.sid <- count ;
          let rhs = 
            if not !old_coverage_bug then begin 
              let bcopy = copy b in
              let bcopy = visitCilStmt my_zero bcopy in 
              bcopy.skind
            end else b.skind
          in 
          Hashtbl.add massive_hash_table count rhs
          (* the copy is because we go through and update the statements
           * to add coverage information later *) 
        end else begin
          b.sid <- 0; 
        end ;
      ) b.bstmts ; 
      b
    ) )
end



(*&&&&&&&&&&&&&&&&&&&&&&&&&遍历函数模块，并生成id与相应函数对应表&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&*)
class my_funcVisitor (fundec : Cil.fundec)
			= object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost (b,(fun b ->
	begin
	List.iter (fun s ->
	   if s.sid > 0 then
(********************************************************)
          (*debug "函数中语句sid： %d\n" s.sid ;*)
(********************************************************)
	Hashtbl.add id_fun_hash_table s.sid fundec.svar.vname;
	  ) b.bstmts ;
         b 
	end 
))
end 

 (* maps integers to statements. *) 
class id_funVisitor = object
  inherit nopCilVisitor
  method vfunc f = 
    ChangeDoChildrenPost(f,(fun f ->
	  let myfun_vistor = new my_funcVisitor f  in
	  visitCilFunction myfun_vistor f;
	  f
    ) )
end
(*&&&&&&&&&&&&&&&&&&&&&&&&&遍历指定的函数块，并将指定函数语句加入到path中(by qiyuhua)&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&*)

(*########################################遍历指定的函数块，生成stmt_var_hash_table哈希表############################*)
class varinfoVisitor (id_list) (*编译变量，保存变量名*)
			= object
  inherit nopCilVisitor
  method vvrbl va = 
    (*setref := StringSet.add va.vname !setref ;*)
    (*Hashtbl.add stmt_var_hash_table *)
    id_list := (va.vname) :: !id_list;
    SkipChildren 
end 


class stmt_varVisitor  = object(*生成stmt_var_hash_table表*)
  inherit nopCilVisitor
  method vstmt s = 
     if ( (not (Hashtbl.mem stmt_var_hash_table s.sid)) && (s.sid <> 0)) then(*判断是否已保存该语句id*)
       begin
	 let id_list = ref [] in
	 let mystmt_vistor = new varinfoVisitor id_list in
	 visitCilStmt mystmt_vistor s;
	 Hashtbl.add stmt_var_hash_table s.sid !id_list;
      end;
    DoChildren
end 
(*########################################遍历指定的函数块，生成stmt_var_hash_table哈希表############################*)

(*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@生成全局变量名列表@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
class globalVarVisitor (gloalVar) = object
  inherit nopCilVisitor
  method vglob g = 
    List.iter (fun g -> match g with
    | GEnumTag(ei,_)
    | GEnumTagDecl(ei,_) -> 
       gloalVar := ei.ename :: !gloalVar 
    | GVarDecl(v,_) 
    | GVar(v,_,_) -> 
       gloalVar := v.vname :: !gloalVar 
    | _ -> () 
    ) [g] ; 
    DoChildren
end
(*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@生成全局变量名列表@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)

(*￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥遍历语法树，生成函数对应的变量名哈希表fun_GLvar_hash_table￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥*)

class func_var_Visitor = object
  inherit nopCilVisitor
  method vfunc fd = 
    ChangeDoChildrenPost (fd,(fun fd ->
	if (not (Hashtbl.mem fun_GLvar_hash_table fd.svar.vname)) then(*判断是否已保存该语句id*)
	 begin
	  let varlist = ref [] in
          List.iter (fun v ->
            varlist := v.vname :: !varlist 
          ) (fd.sformals @ fd.slocals);
	  Hashtbl.add fun_GLvar_hash_table fd.svar.vname (!varlist @ !gloalVar);
	 end;
	fd;	
))
end 
(*￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥遍历语法树，生成函数对应的变量名哈希表fun_GLvar_hash_table￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥￥*)


(* This visitor walks over the C program AST and modifies it so that each
 * statment is preceeded by a 'printf' that writes that statement's number
 * to the .path file at run-time. *) 
(*class covVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      let result = List.map (fun stmt -> 
        if stmt.sid > 0 then begin
          let str = Printf.sprintf "%d\n" stmt.sid in
          let str_exp = Const(CStr(str)) in 
          let instr = Call(None,fprintf,[stderr; str_exp],!currentLoc) in 
          let instr2 = Call(None,fflush,[stderr],!currentLoc) in 
          let skind = Instr([instr;instr2]) in
          let newstmt = mkStmt skind in 
          [ newstmt ; stmt ] 
        end else [stmt] 
      ) b.bstmts in 
      { b with bstmts = List.flatten result } 
    ) )
end *)
(**新的可输出path路径的信息*****************************************************************************)
let make_call lval fname args = Call(lval, fname, args, !currentLoc)
class covVisitor coverage_outname = 
object
  inherit nopCilVisitor

  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      let result = List.map (fun stmt -> 
        if stmt.sid > 0 then begin
          let str = Printf.sprintf "%d\n" stmt.sid in 
          let print_num = 
            make_call None fprintf [stderr; Const(CStr(str));] (*输出fprintf函数语句*)
          in
          let instrs = 
            if !multithread_coverage then begin
              let lval = (Some(Var(stderr_va), NoOffset)) in
              let args = [Const(CStr(coverage_outname)); Const(CStr("a"))] in
              let fopen_fout = make_call lval fopen args in
              let close_fout = make_call None fclose [stderr] in
                [fopen_fout;print_num;close_fout]
            end else 
              let flush = make_call None fflush [stderr] in
                [print_num; flush]
          in
          let skind = 
            if !uniq_coverage then begin
                (* asi = array_sub_i = array[i] *) 
              let iexp = Const(CInt64(Int64.of_int stmt.sid,IInt,None)) in 
              let asi_lval = (Var(!uniq_array_va)), (Index(iexp,NoOffset)) in
              let asi_exp = Lval(asi_lval) in 
              let bexp = BinOp(Eq,asi_exp,zero,ulongType) in
              let set_instr = Set(asi_lval,one,!currentLoc) in 
              let skind = Instr(instrs @[set_instr]) in
              let newstmt = mkStmt skind in 
                If(bexp,mkBlock [newstmt],mkBlock [],!currentLoc)
            end else 
              Instr(instrs)
          in
          let newstmt = mkStmt skind in 
            [ newstmt ; stmt ] 
        end else [stmt] 
      ) b.bstmts in 
        { b with bstmts = List.flatten result } 
    ) )

  method vfunc f = 
    if not !multithread_coverage then begin
      let outfile = Var(stderr_va), NoOffset in
      let fout_args = [Const(CStr(coverage_outname)); Const(CStr("wb"))] in
      let make_fout = make_call (Some(outfile)) fopen fout_args in
      let additional_instrs =
        if !uniq_coverage then begin
          let uniq_array_exp = Lval(Var(!uniq_array_va),NoOffset) in 
          let sizeof_uniq_array = SizeOfE(uniq_array_exp) in 
            [Call(None,memset,
                  [uniq_array_exp;zero;sizeof_uniq_array],!currentLoc)] 
        end else []
      in
      let new_stmt = Cil.mkStmt (Instr (make_fout :: additional_instrs)) in
      let ifknd = 
        If(BinOp(Eq,Lval(outfile), Cil.zero, Cil.intType),
           { battrs = [] ; bstmts = [new_stmt] }, 
           { battrs = []; bstmts = [] }, !currentLoc)
      in
    let ifstmt = Cil.mkStmt(ifknd) in
    ChangeDoChildrenPost(f,
                 (fun f ->
                   f.sbody.bstmts <- ifstmt :: f.sbody.bstmts;
                   f))
    end else DoChildren

end 

(**新的可输出path路径的信息*****************************************************************************)





(*let uniq_array_va = ref 
  (makeGlobalVar "___coverage_array" (TArray(charType,None,[])))*)

(* This visitor walks over the C program AST and modifies it so that each
 * statment is printed _at most once_ when visited. *) 
class uniqCovVisitor = object
  inherit nopCilVisitor
  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      let result = List.map (fun stmt -> 
        if stmt.sid > 0 then begin
          let str = Printf.sprintf "%d\n" stmt.sid in
          (* asi = array_sub_i = array[i] *) 
          let iexp = Const(CInt64(Int64.of_int stmt.sid,IInt,None)) in 
          let asi_lval = (Var(!uniq_array_va)), (Index(iexp,NoOffset)) in
          let asi_exp = Lval(asi_lval) in 
          let bexp = BinOp(Eq,asi_exp,zero,ulongType) in

          let str_exp = Const(CStr(str)) in 
          let instr = Call(None,fprintf,[stderr; str_exp],!currentLoc) in 
          let instr2 = Call(None,fflush,[stderr],!currentLoc) in 
          let instr3 = Set(asi_lval,one,!currentLoc) in 
          let skind = Instr([instr;instr2;instr3]) in
          let newstmt = mkStmt skind in 
          let the_if = If(bexp,mkBlock [newstmt],mkBlock [],!currentLoc) in 
          let if_stmt = mkStmt the_if in 
          [ if_stmt ; stmt ] 
        end else [stmt] 
      ) b.bstmts in 
      { b with bstmts = List.flatten result } 
    ) )
end 

(*let my_cv = new covVisitor*)
let my_uniq_cv = new uniqCovVisitor
let my_num = new numVisitor
let my_empty = new emptyVisitor
let my_every = new everyVisitor
let my_fun = new id_funVisitor
let my_stmt_v = new stmt_varVisitor
let my_fun_v = new func_var_Visitor
let my_golal_v = new globalVarVisitor gloalVar


let main () = begin
  let usageMsg = "Prototype No-Specification Bug-Fixer\n" in 
  let do_cfg = ref false in 
  let do_empty = ref false in 
  let do_every = ref false in 
  let do_uniq = ref false in 
  let filenames = ref [] in 
  let fixfun = ref false(*控制是否生成fix localization，即.fixfun文件，注意生成时间较长*) in

  let argDescr = [
    "--calls", Arg.Set do_cfg, " convert calls to end basic blocks";
    "--empty", Arg.Set do_empty, " allow changes to empty blocks";
    "--uniq", Arg.Set do_uniq, " print each visited stmt only once";
    "--every-instr", Arg.Set do_every, " allow changes between every statement";
    "--old_bug", Arg.Set old_coverage_bug, " compatibility with old hideous bug";
    "--fixfun", Arg.Set fixfun, " produce the fix localization file .fixfun, maybe very slow";

    "--mt-cov", Arg.Set multithread_coverage, "  instrument for coverage with locks.  Avoid if possible.";
    "--uniq", Arg.Set uniq_coverage, "  print each visited stmt only once";
    "--uniq-cov", Arg.Set uniq_coverage, "  print each visited stmt only once";
  ] in 
  let handleArg str = filenames := str :: !filenames in 
  Arg.parse (Arg.align argDescr) handleArg usageMsg ; 

  Cil.initCIL () ; 
  List.iter (fun arg -> 
    begin
      let file = Frontc.parse arg () in 
      if !do_every then begin
        visitCilFileSameGlobals my_every file ; 
      end ; 
      if !do_cfg then begin
        Partial.calls_end_basic_blocks file 
      end ; 
      if (!do_empty) then begin
        visitCilFileSameGlobals my_empty file ; 
      end; 

      visitCilFileSameGlobals my_num file ; 
      let ast = arg ^ ".ast" in 
      let fout = open_out_bin ast in 
      Marshal.to_channel fout (file) [] ;
      close_out fout ; 

(*输出id和函数对应表*)
      visitCilFileSameGlobals my_fun file ; (*输出id与函数对照表*)
      let idfun = arg ^ ".idfun" in 
      let fout = open_out_bin idfun in 
      Marshal.to_channel fout (id_fun_hash_table) [] ;
      close_out fout ;
      
(*………………………………………………………………………………生成对应的fun_id_hash_table哈希表…………………………………………………………………………………………………………………………………………………………*)
   if !fixfun then begin

      visitCilFileSameGlobals my_golal_v file; (*生成全局变量对应listbiao*)

      visitCilFileSameGlobals my_stmt_v file ; (*生成语句id与包含变量对应表*)

      visitCilFileSameGlobals my_fun_v file ; (*生成函数名与包含局部和全局变量对应表*)


      let fun_id_hash_table = Hashtbl.create 8000 in(*创建函数与可替换的语句id对应表*)
	 
     (* **)
      Hashtbl.iter (fun funname varlist_fun-> (*迭代比较前两个表中的list内容，查看是否包含，如包含，进行导入操作*)
         let idlist = ref [] in
         Hashtbl.iter (fun stmtid varlist_stmt->

	    (*debug 
             if stmtid=722 then begin
              debug "********************%d\n" stmtid;
              List.iter (fun x-> debug "%d: %s\n" stmtid x)  varlist_stmt; exit 0 end;*)

		if (compare_list varlist_stmt varlist_fun) then(*比较两个list，查看是否包含*)
		    idlist := stmtid :: !idlist
	  ) stmt_var_hash_table;
            (* 
	     debug "%s:\n" funname;
             List.iter (fun x-> debug "%s\n" x) !gloalVar;
	     debug "********************\n";exit 0; *)
         Hashtbl.add fun_id_hash_table funname !idlist
      ) fun_GLvar_hash_table;

      let idfun = arg ^ ".fixfun" in 
      let fout = open_out_bin idfun in 
      Marshal.to_channel fout (fun_id_hash_table) [] ;
      close_out fout; 
  end else begin
      let idfun = arg ^ ".fixfun" in 
      let fout = open_out_bin idfun in
      let  fun_id_hash_table = Hashtbl.create 80 in
      Hashtbl.add fun_id_hash_table "qiyuhua" [1];
      Marshal.to_channel fout (fun_id_hash_table) [] ;
      end;
(*………………………………………………………………………………生成对应的fun_id_hash_table哈希表…………………………………………………………………………………………………………………………………………………………*)


      if !do_uniq then begin
        let size = 1 + !counter in 
        let size_exp = (Const(CInt64(Int64.of_int size,IInt,None))) in 
        uniq_array_va := (makeGlobalVar "___coverage_array"
          (TArray(charType, Some(size_exp), []))) ;
        let new_global = GVarDecl(!uniq_array_va,!currentLoc) in 
        file.globals <- new_global :: file.globals ; 
        visitCilFileSameGlobals my_uniq_cv file ; 

        let uniq_array_exp = Lval(Var(!uniq_array_va),NoOffset) in 
        let sizeof_uniq_array = SizeOfE(uniq_array_exp) in 
        let fd = Cil.getGlobInit file in 
        let instr = Call(None,memset,
          [uniq_array_exp;zero;sizeof_uniq_array],!currentLoc) in 
        let new_stmt = Cil.mkStmt (Instr[instr]) in 
        fd.sbody.bstmts <- new_stmt :: fd.sbody.bstmts ; 

      end else begin
        let coverage_outname = "./" ^ arg ^ ".path" in(* 输出带路径信息*)
	let my_cv = new covVisitor coverage_outname in
        visitCilFileSameGlobals my_cv file ; 
      end ; 

      let new_global = GVarDecl(stderr_va,!currentLoc) in 
      file.globals <- new_global :: file.globals ; 

      (*let fd = Cil.getGlobInit file in 
      let lhs = (Var(stderr_va),NoOffset) in 
      let data_str = arg ^ ".path" in 
      let str_exp = Const(CStr(data_str)) in 
      let str_exp2 = Const(CStr("wb")) in 
      let instr = Call((Some(lhs)),fopen,[str_exp;str_exp2],!currentLoc) in 
      let new_stmt = Cil.mkStmt (Instr[instr]) in 
      fd.sbody.bstmts <- new_stmt :: fd.sbody.bstmts ; *)
      iterGlobals file (fun glob ->
        (*dumpGlobal defaultCilPrinter stdout glob ;*)
        dumpGlobal noLineCilPrinter stdout glob
      ) ; 
      let ht = arg ^ ".ht" in 
      let fout = open_out_bin ht in 
      Marshal.to_channel fout (!counter,massive_hash_table) [] ;
      close_out fout ; 
    end 
  ) !filenames ; 

end ;;

main () ;;
