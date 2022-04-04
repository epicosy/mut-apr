
(* 
 * Weimer's Genetic Programming Prototype 
 *
 * Given a C program and a path through that program, modify the program
 * using genetic programming to produce variants. Test each variant against
 * some testcases to determine fitness. 
 *)
open Printf
open Cil

let version = "Fatmah Assiri: MUT-APR-FL-BF Jan. 2014"
let fixloc = ref false(*是否调用fixloc表*)
let mutation_max = ref 30 (*单次允许最大变异次数*)
let check_num = ref 0 (*验证全部正测试用例次数*)
let check_all = ref false(*是否进行全部正测试用例验证*)
let faultLoc = ref false(*是否提供fault localization接口*)
let faultpath = ref "faultloc.path"(*是否提供fault localization接口*)

(* We'll use integers to map to 'statements' in the C program/AST. *) 
type stmt_id = int 

(* We'll maintain mappings from stmt_id's to real CIL statements. *) 
type stmt_map = (stmt_id, Cil.stmtkind) Hashtbl.t 

(* We'll keep a 'weighted' violating path *) 
type weighted_path = (float * stmt_id) list 

(* Performance counting information *) 
(*type counters = {
  mutable ins  : int ; (* insertions *) 
  mutable del  : int ; (* deletions *) 
  mutable swap : int ; (* swaps *) 
  mutable xover : int ; (* crossover count *) 
  mutable xswap : int ; (* crossover swaps *) 
  mutable mut   : int ; (* mutation count *) 
} *)

(* Performance counting information *) 
type counters = {
    (* mutable ins  : int ; (* insertions *) 
  mutable del  : int ; (* deletions *) 
  mutable swap : int ; (* swaps *) *)
    (* F.A Aug 28,2012 *)
    (* Ne = Not Equal *)
    mutable chgNeToEq : int ; (*change Ne to Eq *)
    mutable chgNeToLt : int ; (*change Ne to Lt *)
    mutable chgNeToGt : int ; (*change Ne to Gt *)
    mutable chgNeToGe : int ; (*change Ne to Ge *)
    mutable chgNeToLe : int ; (*change Ne to Le *)
    
    (* Eq = Equal *)
    mutable chgEqToNe : int ; (*change Eq to Ne *)
    mutable chgEqToLe : int ; (*change Eq to Le *)
    mutable chgEqToGe : int ; (*change Eq to Ge *)
    mutable chgEqToGt : int ; (*change Eq to Gt *)
    mutable chgEqToLt : int ; (*change Eq to Lt *)
    
    (* Gt = Greater than*)
    mutable chgGtToEq : int ; (*change Gt to Eq *)
    mutable chgGtToNe : int ; (*change Gt to Ne *)
    mutable chgGtToLe : int ; (*change Gt to Le *)
    mutable chgGtToLt : int ; (*change Gt to Lt *)
    mutable chgGtToGe : int ; (*change Gt to Ge *)
    
    (* Lt = Less than *)
    mutable chgLtToEq : int ; (*change Lt to Eq *)
    mutable chgLtToNe : int ; (*change Lt to Ne *)
    mutable chgLtToGt : int ; (*change Lt to Gt *)
    mutable chgLtToGe : int ; (*change Lt to Ge *)
    mutable chgLtToLe : int ; (*change Lt to Le *)
    
    (* Ge = Less than or Equal *) 
    mutable chgGeToEq : int ; (*change Ge to Eq *)
    mutable chgGeToNe : int ; (*change Ge to Ne *)
    mutable chgGeToLe : int ; (*change Ge to Le *)
    mutable chgGeToLt : int ; (*change Ge to Lt *)
    mutable chgGeToGt : int ; (*change Ge to Gt *)
    
    (* Le = Less than or Equal *)
    mutable chgLeToEq : int ; (*change Le to Eq *)
    mutable chgLeToNe : int ; (*change Le to Ne *)
    mutable chgLeToGt : int ; (*change Le to Gt *)
    mutable chgLeToGe : int ; (*change Le to Ge *)
    mutable chgLeToLt : int ; (*change Le to Lt *)
    
    (*Logical Operators Jan 31 *)
    (*LAnd : && *)
    (*mutable chgLAndToLOr : int ; (*change LAnd To LOr *)
	mutable chgLAndToBAnd : int ; (*change LAnd To BAnd *)
	mutable chgLAndToBXor : int ; (*change LAnd To BXor *)
	mutable chgLAndToBOr : int ; (*change LAnd To BOr*)	
	
	(*LOr : || *)
	mutable chgLOrToLAnd : int ; (*change LOr To LAnd *)
	mutable chgLOrToBAnd : int ; (*change LOr To BAnd *)
	mutable chgLOrToBXor : int ; (*change LOr To BXor *)
	mutable chgLOrToBOr : int ; (*change LOr To BOr*)	*)
    
    (*Bit-wise Operators*)
    (*BAnd*: &*)
    mutable chgBAndToBXor : int ; (*change BAnd To LAnd *)
    mutable chgBAndToBOr : int ; (*change BAnd To LAnd *)
    
    (*BXor: ^  *)
    mutable chgBXorToBAnd : int ; (*change BAnd To LAnd *)
    mutable chgBXorToBOr : int ; (*change BAnd To LAnd *)
    
    (*BOr: | *)
    mutable chgBOrToBAnd : int ; (*change BAnd To LAnd *)
    mutable chgBOrToBXor : int ; (*change BAnd To LAnd *)
    
    (*BShift*)
    mutable chgBSLtToBSRt : int ; (*change BAnd To LAnd *)
    mutable chgBSRtToBSLt : int ; (*change BAnd To LAnd *)
    
    
    (*Arthimatci operator *)
    (*PlusA*)
    mutable chgPlusToMinus : int ; (*change Plus To Minus *)
    mutable chgPlusToMult : int ; (*change Plus To Mult *)
    mutable chgPlusToDiv : int ; (*change Plus To Div *)
    mutable chgPlusToMod : int ; (*change Plus To Mod *)
    
    (*MinusA*)
    mutable chgMinusToPlus : int ; (*change Minus To Plus *)
    mutable chgMinusToMult : int ; (*change Minus To Mult *)
    mutable chgMinusToDiv : int ; (*change Minus To Div *)
    mutable chgMinusToMod : int ; (*change Minus To Mod *)
    
    (*Mult *)
    mutable chgMultToPlus : int ; (*change Mult To Plus *)
    mutable chgMultToMinus : int ; (*change Mult To Minus *)
    mutable chgMultToDiv : int ; (*change Mult To Div *)
    mutable chgMultToMod : int ; (*change Mult To Mod *)
    
    (*Div *)
    mutable chgDivToPlus : int ; (*change Div To Plus *)
    mutable chgDivToMinus : int ; (*change Div To Minus *)
    mutable chgDivToMult : int ; (*change Div To Mult *)
    mutable chgDivToMod : int ; (*change Div To Mod *)
    
    (*Mod *)
    mutable chgModToPlus : int ; (*change Mod To Plus *)
    mutable chgModToMinus : int ; (*change Mod To Minus *)
    mutable chgModToMult : int ; (*change Mod To Mult *)
    mutable chgModToDiv : int ; (*change Mod To Div *)
    
    
    (*****************************)
    (*Equality and Assignement*)
    
    (*mutable chgEqToAssign : int ; (*change Equl To Assignement *)*)
    mutable chgAssignToEq : int ; (*change Equl To Assignement *)
    
    (******************************)
    (* others *)
    mutable xover : int ; (* crossover count *) 
    mutable xswap : int ; (* crossover swaps *) 
    mutable mut   : int ; (* mutation count *) 

}

type tracking = {
    mutable current : counters ; 
    mutable at_last_fitness : counters ; 
} 

(* Our key data type: a single 'individual' in our GP population. 
 * Each individual is a four-tuple with
 * 1. A Cil.file -- the abstract syntax tree
 * 2. A Hashtable -- mapping integers to statements in the AST 
 * 3. A number -- the number of statements in the *whole AST*
 *                (_not_ the length of the path)
 * 4. A list of numbers -- the violating path as a list of statement IDs 
 *) 
type id_fun = (stmt_id, string) Hashtbl.t
type fix_fun = (string, int list) Hashtbl.t
type individual = 
    Cil.file *
	stmt_map *
	    stmt_id *
		(weighted_path) *
		    tracking *
			id_fun *
			    fix_fun

(**************************************)
let hashtbl_keys h = 
  Hashtbl.fold (fun key _ l -> key :: l) h []

(******************************************)
(*function that compare two values in a list*)
let compare_fun (k1,_) (k2,_) = compare k1 k2 

(***********************************************************************
 * Utility Functions 
 ***********************************************************************)
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

(*let new_counters () = 
  { ins = 0; del = 0; swap = 0; xswap = 0; xover = 0; mut = 0; } *)
let new_counters () = 
  {(* Ne *) chgNeToEq = 0; chgNeToLt = 0 ; chgNeToGt = 0 ; chgNeToGe = 0 ; chgNeToLe = 0 ; 
	    (* Eq *) chgEqToNe = 0 ; chgEqToLe = 0 ; chgEqToGe = 0 ; chgEqToGt = 0 ; chgEqToLt = 0 ;
	    (* Gt *)	chgGtToEq = 0 ; chgGtToNe = 0 ; chgGtToLe = 0 ; chgGtToLt = 0 ;chgGtToGe = 0 ;
	    (* Lt *)	chgLtToEq = 0 ; chgLtToNe = 0 ; chgLtToGt = 0 ; chgLtToGe = 0 ;chgLtToLe = 0 ;
	    (* Ge *) chgGeToEq = 0 ; chgGeToNe = 0 ; chgGeToLe = 0 ; chgGeToLt = 0 ;chgGeToGt = 0 ;
	    (* Le *) chgLeToEq = 0 ; chgLeToNe = 0 ; chgLeToGt = 0 ; chgLeToGe = 0 ;chgLeToLt = 0 ;
	    (*(* LAnd *) chgLAndToLOr = 0 ; chgLAndToBAnd = 0 ; chgLAndToBXor = 0 ; chgLAndToBOr = 0 ; 
	 (* LOr *) chgLOrToLAnd = 0 ; chgLOrToBAnd = 0 ; chgLOrToBXor = 0 ; chgLOrToBOr = 0 ; *)
	    (*BAnd*) chgBAndToBXor = 0 ; chgBAndToBOr = 0 ; 
	    (*BXor*) chgBXorToBAnd = 0 ; chgBXorToBOr = 0 ; 
	    (*BOr*) chgBOrToBAnd = 0 ; chgBOrToBXor = 0 ;
	    (*BS*) chgBSLtToBSRt = 0 ; chgBSRtToBSLt = 0 ; 
	    (* Plus *) chgPlusToMinus = 0 ; chgPlusToMult = 0 ; chgPlusToDiv = 0 ; chgPlusToMod = 0 ;
	    (* Minus *) chgMinusToPlus = 0 ; chgMinusToMult = 0 ; chgMinusToDiv = 0 ; chgMinusToMod = 0 ;
	    (* Mult *) chgMultToPlus = 0 ; chgMultToMinus = 0 ; chgMultToDiv = 0 ; chgMultToMod = 0 ;
	    (* Div *) chgDivToPlus = 0 ; chgDivToMinus = 0 ; chgDivToMult = 0 ; chgDivToMod = 0 ;
	    (* Mod *) chgModToPlus = 0 ; chgModToMinus = 0 ; chgModToMult = 0 ; chgModToDiv = 0 ;
	    (*Eq & Assign*) (*chgEqToAssign = 0 ;*) chgAssignToEq = 0;
	    (* other *) xswap = 0; xover = 0; mut = 0; }
      
(*let average_counters a b = 
  { ins = (a.ins + b.ins) / 1 ;
    del = (a.del + b.del) / 1 ; 
    swap = (a.swap + b.swap) / 1 ;
    xswap = (a.xswap + b.xswap) / 1 ; 
    xover = (a.xover + b.xover) / 1 ;
    mut = (a.mut + b.mut) / 1 ; } *)
      
let average_counters a b = 
  { (*ins = (a.ins + b.ins) / 1 ;
    del = (a.del + b.del) / 1 ; 
    swap = (a.swap + b.swap) / 1 ;*)
      (*F.A. Aug 28,2012 *)
      (* Ne *)
      chgNeToEq = (a.chgNeToEq + b.chgNeToEq) / 1; 
      chgNeToLt = (a.chgNeToLt + b.chgNeToLt) / 1;
      chgNeToGt = (a.chgNeToGt + b.chgNeToGt) / 1;
      chgNeToGe = (a.chgNeToGe + b.chgNeToGe) / 1;
      chgNeToLe = (a.chgNeToLe + b.chgNeToLe) / 1;
      
      (* Eq *)
      chgEqToNe = (a.chgEqToNe + b.chgEqToNe) / 1;
      chgEqToLe = (a.chgEqToLe + b.chgEqToLe) / 1;
      chgEqToGe = (a.chgEqToGe + b.chgEqToGe) / 1;
      chgEqToGt = (a.chgEqToGt + b.chgEqToGt) / 1;
      chgEqToLt = (a.chgEqToLt + b.chgEqToLt) / 1;
      
      (* Gt *)
      chgGtToEq = (a.chgGtToEq + b.chgGtToEq) / 1;
      chgGtToNe = (a.chgGtToNe + b.chgGtToNe) / 1;
      chgGtToLe = (a.chgGtToLe + b.chgGtToLe) / 1;
      chgGtToLt = (a.chgGtToLt + b.chgGtToLt) / 1;
      chgGtToGe = (a.chgGtToGe + b.chgGtToGe) / 1;
      
      (* Lt *)
      chgLtToEq = (a.chgLtToEq + b.chgLtToEq) / 1;
      chgLtToNe = (a.chgLtToNe + b.chgLtToNe) / 1;
      chgLtToGt = (a.chgLtToGt + b.chgLtToGt) / 1;
      chgLtToGe = (a.chgLtToGe + b.chgLtToGe) / 1;
      chgLtToLe = (a.chgLtToLe + b.chgLtToLe) / 1;
      
      (* Ge *)
      chgGeToEq = (a.chgGeToEq + b.chgGeToEq) / 1;
      chgGeToNe = (a.chgGeToNe + b.chgGeToNe) / 1;
      chgGeToLe = (a.chgGeToLe + b.chgGeToLe) / 1;
      chgGeToLt = (a.chgGeToLt + b.chgGeToLt) / 1;
      chgGeToGt = (a.chgGeToGt + b.chgGeToGt) / 1;
      
      (* Le *)
      chgLeToEq = (a.chgLeToEq + b.chgLeToEq) / 1;
      chgLeToNe = (a.chgLeToNe + b.chgLeToNe) / 1;
      chgLeToGt = (a.chgLeToGt + b.chgLeToGt) / 1;
      chgLeToGe = (a.chgLeToGe + b.chgLeToGe) / 1;
      chgLeToLt = (a.chgLeToLt + b.chgLeToLt) / 1;
      
      (*
		(*LAnd *)
		chgLAndToLOr = (a.chgLAndToLOr + b.chgLAndToLOr) / 1;
		chgLAndToBAnd = (a.chgLAndToBAnd + b.chgLAndToBAnd) / 1;
		chgLAndToBXor = (a.chgLAndToBXor + b.chgLAndToBXor) / 1;
		chgLAndToBOr = (a.chgLAndToBOr + b.chgLAndToBOr) / 1;
		
		(*LOr *)
		chgLOrToLAnd = (a.chgLOrToLAnd + b.chgLOrToLAnd) / 1;
		chgLOrToBAnd = (a.chgLOrToBAnd + b.chgLOrToBAnd) / 1;
		chgLOrToBXor = (a.chgLOrToBXor + b.chgLOrToBXor) / 1;
		chgLOrToBOr = (a.chgLOrToBOr + b.chgLOrToBOr) / 1; *)
      
      (*BAnd*)
      chgBAndToBXor = (a.chgBAndToBXor + b.chgBAndToBXor) / 1;
      chgBAndToBOr = (a.chgBAndToBOr + b.chgBAndToBOr) / 1;
      
      (*BXor*)
      chgBXorToBAnd = (a.chgBXorToBAnd + b.chgBXorToBAnd) / 1;
      chgBXorToBOr = (a.chgBXorToBOr + b.chgBXorToBOr) / 1;
      
      (*BOr*)
      chgBOrToBAnd = (a.chgBOrToBAnd + b.chgBOrToBAnd) / 1;
      chgBOrToBXor = (a.chgBOrToBXor + b.chgBOrToBXor) / 1;
      
      (*BS*)
      chgBSLtToBSRt = (a.chgBSLtToBSRt + b.chgBSLtToBSRt) / 1;
      chgBSRtToBSLt = (a.chgBSRtToBSLt + b.chgBSRtToBSLt) / 1;
      
      (*PlusA *)
      chgPlusToMinus = (a.chgPlusToMinus + b.chgPlusToMinus) / 1;
      chgPlusToMult = (a.chgPlusToMult + b.chgPlusToMult) / 1;
      chgPlusToDiv = (a.chgPlusToDiv + b.chgPlusToDiv) / 1;
      chgPlusToMod = (a.chgPlusToMod + b.chgPlusToMod) / 1;
      
      (*MinusA *)
      chgMinusToPlus = (a.chgMinusToPlus + b.chgMinusToPlus) / 1;
      chgMinusToMult = (a.chgMinusToMult + b.chgMinusToMult) / 1;
      chgMinusToDiv = (a.chgMinusToDiv + b.chgMinusToDiv) / 1;
      chgMinusToMod = (a.chgMinusToMod + b.chgMinusToMod) / 1;
      
      (*Mult *)
      chgMultToPlus = (a.chgMultToPlus + b.chgMultToPlus) / 1;
      chgMultToMinus = (a.chgMultToMinus + b.chgMultToMinus) / 1;
      chgMultToDiv = (a.chgMultToDiv + b.chgMultToDiv) / 1;
      chgMultToMod = (a.chgMultToMod + b.chgMultToMod) / 1;
      
      (*Div *)
      chgDivToPlus = (a.chgDivToPlus + b.chgDivToPlus) / 1;
      chgDivToMinus = (a.chgDivToMinus + b.chgDivToMinus) / 1;
      chgDivToMult = (a.chgDivToMult + b.chgDivToMult) / 1;
      chgDivToMod = (a.chgDivToMod + b.chgDivToMod) / 1;
      
      (*Mod *)
      chgModToPlus = (a.chgModToPlus + b.chgModToPlus) / 1;
      chgModToMinus = (a.chgModToMinus + b.chgModToMinus) / 1;
      chgModToMult = (a.chgModToMult + b.chgModToMult) / 1;
      chgModToDiv = (a.chgModToDiv + b.chgModToDiv) / 1;
      
      (*Eq & Assign*)
      (*chgEqToAssign = (a.chgEqToAssign + b.chgEqToAssign) / 1;*)
      chgAssignToEq = (a.chgAssignToEq + b.chgAssignToEq) / 1;
      
      
      (* Other*)
      xswap = (a.xswap + b.xswap) / 1 ; 
      xover = (a.xover + b.xover) / 1 ;
      mut = (a.mut + b.mut) / 1 ; }   
      
let average_tracking a b = 
  { current = average_counters a.current b.current ;
    at_last_fitness = average_counters a.at_last_fitness b.at_last_fitness
    ; }

let new_tracking () = 
  { current = new_counters () ; at_last_fitness = new_counters (); } 

let print_best_output = ref (fun () -> ()) 


(* we copy all debugging output to a file and to stdout *)
let debug_out = ref stdout 
let debug fmt = 
  let k result = begin
	output_string !debug_out result ; 
	output_string stdout result ; 
	flush stdout ; 
    end in
  Printf.kprintf k fmt 

let uniq lst = (* return a copy of 'lst' where each element occurs once *) 
  let ht = Hashtbl.create 255 in 
  let lst = List.filter (fun elt ->
			 if Hashtbl.mem ht elt then false
			 else begin
				 Hashtbl.add ht elt () ;
				 true 
			     end 
			) lst in
  lst 

(* Returns the elements of 'lst' in a random order. *) 
let random_order lst = 
  let a = List.map (fun x -> (Random.float 1.0), x) lst in
  let b = List.sort (fun (a,_) (b,_) -> compare a b) a in 
  List.map (fun (_,a) -> a) b 

let rec first_nth lst size =  
  if size < 1 then [] 
  else match lst with
       | [] -> []
       | hd :: tl -> hd :: (first_nth tl (pred size))

let file_size name = (* return the size of the given file on the disk *) 
  try 
      let stats = Unix.stat name in
      stats.Unix.st_size 
  with _ -> 0 

(* This makes a deep copy of an arbitrary Ocaml data structure *) 
let copy (x : 'a) = 
  let str = Marshal.to_string x [] in
  (Marshal.from_string str 0 : 'a) 
(* Cil.copyFunction does not preserve stmt ids! Don't use it! *) 



(* Counts the number of lines in a simple text file -- used by
 * our fitness function. Returns the integer number as a float. *) 
let count_lines_in_file (file : string) 
    (* returns: *) : float =
  try 
      let fin = open_in file in 
      let count = ref 0 in
      (try while true do
	       let line = input_line fin in
	       ignore line ;
	       incr count 
	   done ; 0. with _ -> begin close_in fin ; float_of_int !count end) 
  with _ -> 0.


let probability p = 
  if p <= 0.0 then false
  else if p >= 1.0 then true
  else Random.float 1.0 <= p 

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



(*v_ Vu's stuffs*)
let v_avg_fit_l:float list ref = ref []  (*avg_fit list*)
let v_bc_fit_l:float list ref = ref []	 (*best chrome fit list*)

let v_debug:int ref = ref 0

let v_writeFile (f_src:string) (f_ast:Cil.file) = (
    let f_out = open_out f_src in
    Cil.dumpFile Cil.defaultCilPrinter f_out f_src f_ast;
    close_out f_out
)


let v_getDigestName (filecontent:Cil.file):string=(
    let filename = "temp_digest" in
    v_writeFile filename filecontent;
    let digest = Digest.file filename in
    (try (Unix.unlink filename) with _ -> ());
    let res = Digest.to_hex(digest) in
    res
)
						      
let v_get_stmt (b:stmt):string= (
    let doc_of_stmt = d_stmt () b in
    let string_of_stmt = Pretty.sprint ~width:80 doc_of_stmt in
    string_of_stmt
)
				    

(*v_ Vu's stuffs*)


(***********************************************************************
 * Genetic Programming Functions - Sampling
 ***********************************************************************)
let use_tournament = ref false 

(* 
 * Stochastic universal sampling. 
 *
 * Stephanie suggests that we replace this with tournament selection at
 * some point. 
 *
 * Input: a list of individual,fitness pairs
 *        a desired number of individuals
 *
 * Output: a list of individuals
 *) 
let sample (population : (individual * float) list) 
           (desired : int) 
    (* returns *) : individual list = 
  let total = List.fold_left (fun acc (_,fitness) ->  
			      acc +. fitness) 0. population in 


  (*v_ analysis*)
  v_avg_fit_l := (total /. float_of_int (List.length population) )::!v_avg_fit_l;
  
  let sort_pop = List.rev (List.sort (fun (_,a)(_,b) -> compare a b)population) in 
  let best_chrome_fit:float = snd(List.hd sort_pop) in
  v_bc_fit_l :=  best_chrome_fit::!v_bc_fit_l ;
  (*v_ analysis*)


  (if total <= 0. then failwith "selection: total <= 0") ; 
  let normalized = List.map (fun (a,fitness) ->
			     a, fitness /. total
			    ) population in 
  let sofar = ref 0.0 in 
  let accumulated = List.map (fun (a,normalized) ->
			      let res = normalized +. !sofar in
			      sofar := !sofar +. normalized ;
			      (a,res)
			     ) normalized in 
  let distance_between_pointers = 1.0 /. (float_of_int desired) in 
  let offset = Random.float distance_between_pointers in 
  let result = ref [] in 
  for i = 0 to pred desired do
      let marker = offset +. ((float_of_int i) *. distance_between_pointers) in 
      let rec walk lst = match lst with
	  | [] -> (* error! should never happen! *) 
	     debug "desired = %d\n" desired ; 
	     debug "distance_between_pointers = %g\n" distance_between_pointers ;
	     debug "offset = %g\n" offset ;
	     debug "i = %d\n" i ; 
	     debug "marker = %g\n" marker ;
	     failwith "selection problem" 
	  | (elt, acc) :: rest -> 
	     if acc > marker then result := elt :: !result 
	     else walk rest 
      in
      walk accumulated
  done ;
  !result 

(***********************************************************************
 * Genetic Programming Functions - Tournament Selection
 ***********************************************************************)
let tournament_k = ref 2 
let tournament_p = ref 1.00 

let tournament_selection (population : (individual * float) list) 
			 (desired : int) 
    (* returns *) : individual list = 
  let p = !tournament_p in 
  assert ( desired >= 0 ) ; 
  assert ( !tournament_k >= 1 ) ; 
  assert ( p >= 0.0 ) ; 
  assert ( p <= 1.0 ) ; 
  assert ( List.length population > 0 ) ; 
  let rec select_one () = 
    (* choose k individuals at random *) 
    let lst = random_order population in 
    (* sort them *) 
    let pool = first_nth lst !tournament_k in 
    let sorted = List.sort (fun (_,f) (_,f') -> compare f' f) pool in 
    let rec walk lst step = match lst with
	| [] -> select_one () 
	| (indiv,fit) :: rest -> 
           let taken = 
             if p >= 1.0 then true
             else begin 
		     let required_prob = p *. ((1.0 -. p)**(step)) in 
		     Random.float 1.0 <= required_prob 
		 end 
           in
           if taken then (indiv) else walk rest (step +. 1.0)
    in
    walk sorted 0.0
  in 
  let answer = ref [] in 
  for i = 1 to desired do
      answer := (select_one ()) :: !answer
  done ;
  !answer

(***********************************************************************
 * Genetic Programming Functions - AST-Changing Visitors
 ***********************************************************************)

(*
 * Three AST visitors used in crossover and mutation. 
 *)
class xswapVisitor (file : Cil.file) 
                   (counters : counters) 
                   (to_swap : stmt_map) 
  = object
    (* If (x,y) is in the to_swap mapping, we replace statement x 
     * with statement y. Presumably (y,x) is also in the mapping. *) 
    inherit nopCilVisitor
    method vstmt s = ChangeDoChildrenPost(s, fun s ->
					     if Hashtbl.mem to_swap s.sid then begin
										  let swap_with = Hashtbl.find to_swap s.sid in 
										  let copy = copy swap_with in
										  counters.xswap <- counters.xswap + 1 ; 
										  { s with skind = copy } 
									      end else s 
					 ) 
end 

	
(*borrowd from coverage.ml *)
class numToZeroVisitor = object
    inherit nopCilVisitor
    method vstmt s = s.sid <- 0 ; DoChildren
end 

let my_zero = new numToZeroVisitor

(**************************************************)

class getExpVisitor output first = object
    inherit nopCilVisitor
    method vstmt s = 
      if !first then begin
			first := false ; DoChildren
		    end else 
	  SkipChildren (* stay within this statement *) 
    method vexpr e = 
      ChangeDoChildrenPost(e, fun e ->
			      output := e :: !output ; e
			  ) 
end

let get_Exp = new getExpVisitor


(***************************************) 

let repair_stmt sk = 
  match sk with
  | Instr _ | Return _ | If _ | Loop _ -> true

  | Goto _ | Break _ | Continue _ | Switch _ 
  | Block _ | TryFinally _ | TryExcept _ -> false
						
(************************************)



class changeBAndToBXorVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map) 
			      (stmtId : int)
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BAndToBXor stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BAndToBXor currentloc  %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					                                                                                        let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					                                                                                        debug "LeToLt currentloc %s \n " lw ;
					                                                                                        debug "LeToLt current stmt id %d \n " s.sid;  *)
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BAnd ->  
										let bexp = BinOp(BXor,e1,e2,ulongType) in
										let the_if = If(bexp,b1,b2,l) in 
										let if_stmt = mkStmt the_if in 
										let chg_with = if_stmt.skind in
										let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgBAndToBXor <- counters.chgBAndToBXor + 1 ; 
										{ s with skind = copy }  

									      |_ -> s;)
									  | _ -> s;)


								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
									       |BAnd ->  
										 let bexp = BinOp(BXor,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
										 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
										 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
									    |BAnd ->  
									      let bexp = BinOp(BXor,e1,e2,ulongType) in
									      let the_instr = Instr([Set(lval,bexp,l)]) in 
									      let instr_stmt = mkStmt the_instr in 
									      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
									      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 

								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 

						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
(******************************************************************************)

class changeBAndToBOrVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)
			     (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
                
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BAndToBOr stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BAndToBOr currentloc  %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					debug "LeToLt currentloc %s \n " lw ;
					debug "LeToLt current stmt id %d \n " s.sid; *) 
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BAnd ->  
										let bexp = BinOp(BOr,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
										let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     		  						counters.chgBAndToBOr <- counters.chgBAndToBOr + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)


								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |BAnd ->  
										 let bexp = BinOp(BOr,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
										 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |BAnd ->  
									      let bexp = BinOp(BOr,e1,e2,ulongType) in
									      let the_instr = Instr([Set(lval,bexp,l)]) in 
									      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
									      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      s
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
(**************************************************************************)



class changeBXorToBAndVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map) 
			      (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BXorToBAnd stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BXorToBAnd currentloc  %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					debug "LeToLt currentloc %s \n " lw ;
					debug "LeToLt current stmt id %d \n " s.sid; *) 
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BXor ->  
										let bexp = BinOp(BAnd,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     		 						counters.chgBXorToBAnd <- counters.chgBXorToBAnd + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |BXor ->  
								      		 let bexp = BinOp(BAnd,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
										 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |BXor ->  
									      let bexp = BinOp(BAnd,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      s
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			

(******************************************************************************)

class changeBXorToBOrVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)
			     (stmtId : int)  
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BXorToBOr stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BXorToBOr currentloc %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					debug "LeToLt currentloc %s \n " lw ;*)
								      
			   					      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BXor ->  
										let bexp = BinOp(BOr,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
										let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgBXorToBOr <- counters.chgBXorToBOr + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s; )
									     
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |BXor ->  
										 let bexp = BinOp(BOr,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
										 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |BXor ->  
									      let bexp = BinOp(BOr,e1,e2,ulongType) in
									      let the_instr = Instr([Set(lval,bexp,l)]) in 
									      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
									      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin
									      s
									  end
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			


(***********************************************************)

class changeBOrToBAndVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map) 
			     (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid
							      then begin	 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BorToBAnd stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BOrToBAnd currentloc %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					                              let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					debug "LeToLt currentloc after assigned  %s \n " lw ;
					debug "LeToLt current stmt id %d \n " s.sid;   *)
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BOr ->  
										let bexp = BinOp(BAnd,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
										let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgBOrToBAnd <- counters.chgBOrToBAnd + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |BOr ->  
										 let bexp = BinOp(BAnd,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
										 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |BOr ->  
									      let bexp = BinOp(BAnd,e1,e2,ulongType) in
									      let the_instr = Instr([Set(lval,bexp,l)]) in 
									      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
									      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin
									      s
									  end
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			

(****************************************************************)

class changeBOrToBXorVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map) 
			     (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid 
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BOrToBXor stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BOrToBXor currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
					let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					debug "LeToLt currentloc %s \n " lw ;
					debug "LeToLt current stmt id %d \n " s.sid; *) 
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |BOr ->  
										let bexp = BinOp(BXor,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
										let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgBOrToBXor <- counters.chgBOrToBXor + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |BOr ->  
										 let bexp = BinOp(BXor,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
										 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
										 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |BOr -> 
									      let bexp = BinOp(BXor,e1,e2,ulongType) in 
								 	      let the_instr = Instr([Set(lval,bexp,l)]) in 
									      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
									      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin
									      s 
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
(***********************************************************************)

class changeBSLtToBSRtVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map) 
			      (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BSLtToBSRt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BSLtToBSRt currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
					 let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
					 debug "LeToLt currentloc %s \n " lw ;
					 debug "LeToLt current stmt id %d \n " s.sid;  *)
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Shiftlt ->  
										let bexp = BinOp(Shiftrt,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgBOrToBXor <- counters.chgBOrToBXor + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Shiftlt ->  
								       		 let bexp = BinOp(Shiftrt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Shiftlt ->  
									      let bexp = BinOp(Shiftrt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
(************************************************************************)
class changeBSRtToBSLtVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map) 
			      (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "BSRtToBSLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "BSRtToBSLt currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "LeToLt currentloc %s \n " lw ;
															       debug "LeToLt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Shiftrt ->  
										(*create the new if *)
										let bexp = BinOp(Shiftlt,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgBOrToBXor <- counters.chgBOrToBXor + 1 ; 
        									{ s with skind = copy } 										   													|_ -> s;)
									  | _ -> s;)
									     
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Shiftrt ->  
										 let bexp = BinOp(Shiftlt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Shiftrt ->  
									      let bexp = BinOp(Shiftlt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        								      { s with skind = copy } 										   													     |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			

(******************************************************************************)

(*F.A. aug 28,2012 *)             
class changeNeToEqVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "NeToEq stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "NeToEq currentloc  %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If:NeToEq currentloc %s \n " lw ;
															       debug "If:NeToEq current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,loc) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Ne ->
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,loc) in 
									      let if_stmt = mkStmt the_if in 
									      let chg_with = if_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        								      { s with skind = copy } 
									    | _ -> s ;) (*Op match*)
									 | _ -> s;)(*BinOp match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ne ->  
										 let bexp = BinOp(Eq,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ne ->  
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToEq <- counters.chgNeToEq + 1 ; 
        								      { s with skind = copy } 										   													     |_ -> s;  )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			

	
(************************************************************************************)				

class changeNeToLtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "NeToLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "NeToLt currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: NeToLt currentloc %s \n " lw ;
															       debug "If: NeToLt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ne ->
									      (*create the new if *)
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                  							      counters.chgNeToLt <- counters.chgNeToLt + 1 ; 
        								      { s with skind = copy } 
									    |_ -> s;) (*end op match *)
									 | _ -> s;)(*end e match *)
		   							    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ne ->  
										 let bexp = BinOp(Lt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgNeToLt <- counters.chgNeToLt + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ne ->  
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToLt <- counters.chgNeToLt + 1 ;  
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			

(******************************************************************************)

class changeNeToGtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
		  				      if repair_stmt ss = true
						      then begin 
		  					      if stmtId = s.sid
							      then begin
		  						      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "NeToGt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "NeToGt currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: NeToGt currentloc %s \n " lw ;
								      debug "If: NeToGt current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ne ->
									      (*create the new if *)
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToGt <- counters.chgNeToGt + 1 ; 
        								      { s with skind = copy }
									    |_ -> s;)(*op match *)
									 | _ -> s;)(*e match *)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ne ->  
										 let bexp = BinOp(Gt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgNeToGt <- counters.chgNeToGt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ne ->  
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToGt <- counters.chgNeToGt + 1 ; 
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
	

(********************************************************************************************)

class changeNeToGeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "NeToGe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "NeToGe currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: NeToGe currentloc %s \n " lw ;
															       debug "If: NeToGe current stmt id %d \n " s.sid;  *)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ne ->
									      (*create the new if *)
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgNeToGe <- counters.chgNeToGe + 1 ; 
        								      { s with skind = copy }																						              |_ -> s;)(*op match*)
									 | _ -> s;)(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ne ->  
										 
										 let bexp = BinOp(Ge,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgNeToGe <- counters.chgNeToGe + 1 ;  
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ne ->  
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToGe <- counters.chgNeToGe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
	

(********************************************************************************)

class changeNeToLeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug " NeToLe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug " NeToLt currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
								       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								       debug "If: NeToLe currentloc %s \n " lw ;
								       debug "If: NeToLe current stmt id %d \n " s.sid;*)  
								      match ss with
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ne ->
									      (*create the new if *)
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToLe <- counters.chgNeToLe + 1 ; 
        								      { s with skind = copy }	
									    |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ne ->  
										 let bexp = BinOp(Le,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     	 							 counters.chgNeToLe <- counters.chgNeToLe + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ne ->  
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgNeToLe <- counters.chgNeToLe + 1 ;  
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
	

(********************************************************************************)

class changeEqToNeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "EqToNe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "EqToNe currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: EqToNe currentloc %s \n " lw ;
								      debug "If: EqToNe current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Eq -> 
									      (*create the new if *)
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgEqToNe <- counters.chgEqToNe + 1 ; 
        								      { s with skind = copy }	
									    |_ -> s;)(*op match*)
									 |_ -> s;)(*e match*)

								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Eq ->  
										 let bexp = BinOp(Ne,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgEqToNe <- counters.chgEqToNe + 1 ;
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Eq ->  
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgEqToNe <- counters.chgEqToNe + 1 ;
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
	
	
(**********************************************************************)	

class changeEqToLeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
	  					      if repair_stmt ss = true 
						      then begin 
	  						      if stmtId = s.sid 
							      then begin
	  							      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "EqToLe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "EqToLe currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								       debug "If: EqToLe currentloc %s \n " lw ;
								       debug "If: EqToLe current stmt id %d \n " s.sid;*) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Eq ->
								 	      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                 							      counters.chgEqToLe <- counters.chgEqToLe + 1 ; 
        								      { s with skind = copy }	
									    |_ -> s;)(*op match*)
									 | _ -> s; )(*e macth*)

								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Eq ->  
										 let bexp = BinOp(Le,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgEqToLe <- counters.chgEqToLe + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Eq ->  
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgEqToLe <- counters.chgEqToLe + 1 ; 
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end 			
	
	

(************************************************************************)

class changeEqToGeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug " EqToGe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug " EqToGe currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: EqToGe currentloc %s \n " lw ;
															       debug "If: EqToGe current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Eq -> 
								  	      (*create the new if *)
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgEqToGe <- counters.chgEqToGe + 1 ; 
        								      { s with skind = copy }											   												     |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Eq ->  
										 let bexp = BinOp(Ge,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgEqToGe <- counters.chgEqToGe + 1 ;
        									 { s with skind = copy } 										   													|_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Eq ->  
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgEqToGe <- counters.chgEqToGe + 1 ;
        								      { s with skind = copy } 										   													     |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end

(****************************************************************)

class changeEqToGtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug " EqToGt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug " EqToGt currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: EqToGt currentloc %s \n " lw ;
															       debug "If: EqToGt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Eq ->
						  			      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgEqToGt <- counters.chgEqToGt + 1 ; 
        								      { s with skind = copy }										   													     |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Eq ->  
										 let bexp = BinOp(Gt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgEqToGt <- counters.chgEqToGt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Eq ->  
									      
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgEqToGt <- counters.chgEqToGt + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end

(*********************************************************************)

class changeEqToLtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "EqToLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "EqToLt currentloc %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: EqToLt currentloc %s \n " lw ;
															       debug "If: EqToLt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Eq ->  
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgEqToLt <- counters.chgEqToLt + 1 ; 
        								      { s with skind = copy }											   													
									    |_ -> s;)(*op match*)
									 |_ -> s;)(*e macth*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Eq ->  
										 
										 let bexp = BinOp(Lt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgEqToLt <- counters.chgEqToLt + 1 ;  
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Eq ->
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgEqToLt <- counters.chgEqToLt + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(*****************************************************************) 


class changeGtToEqVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GtToEq stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GtToEq currentloc %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GtToEq currentloc %s \n " lw ;
								      debug "If: GtToEq current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Gt ->
									      
									      (*create the new if *)
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGtToEq <- counters.chgGtToEq + 1 ; 
        								      { s with skind = copy }										   													
									    |_ -> s;)(*op match*)
									 | _ -> s;)(*e match*)
									    
				 				      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
									       |Gt ->  
										 
										 let bexp = BinOp(Eq,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
					 					 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
           									 counters.chgGtToEq <- counters.chgGtToEq + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
									    |Gt ->  
									      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGtToEq <- counters.chgGtToEq + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(*****************************************************************)

class changeGtToNeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GtToNe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GtToNe currentloc d %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: GtToNe currentloc %s \n " lw ;
															       debug "If: GtToNe current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Gt -> 
									      
								   	      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGtToNe <- counters.chgGtToNe + 1 ; 
        								      { s with skind = copy }										   													
									    |_ -> s;)(*op match*)
									 |_ -> s;)(*e match*) 
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Gt ->  
										 
										 let bexp = BinOp(Ne,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGtToNe <- counters.chgGtToNe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Gt ->  
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGtToNe <- counters.chgGtToNe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(***************************************************************************)

class changeGtToLeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GtToLe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GtToLe currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
															       let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
															       debug "If: GtToLe currentloc %s \n " lw ;
															       debug "If: GtToLe current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Gt -> 
									      
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
              								      counters.chgGtToLe <- counters.chgGtToLe + 1 ; 
        								      { s with skind = copy }										   													
							 		    |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Gt ->  
										 
										 let bexp = BinOp(Le,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGtToLe <- counters.chgGtToLe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Gt ->  
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGtToLe <- counters.chgGtToLe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end

(*************************************************************************)

class changeGtToLtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid 
							      then begin
								      (*debug "";*)
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GtToLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GtToLt currentloc before reassigned %s \n " lb ;
								      currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GtToLt currentloc %s \n " lw ;
								      debug "If: GtToLt current stmt id %d \n " s.sid;  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Gt ->  
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGtToLt <- counters.chgGtToLt + 1 ; 
        								      { s with skind = copy }	
									    |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
					  			      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Gt ->  
										 
										 let bexp = BinOp(Lt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGtToLt <- counters.chgGtToLt + 1 ;  
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Gt ->  
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGtToLt <- counters.chgGtToLt + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end

(***************************************************************************)

class changeGtToGeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin  
							      if stmtId = s.sid
							      then begin
								     (* debug "";*)
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GtToGe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GtToGe currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GtToGe currentloc %s \n " lw ;
								      debug "If: GtToGe current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Gt -> 
								 	      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGtToGe <- counters.chgGtToGe + 1 ; 
        								      { s with skind = copy }										   													
									    |_ -> s;)(*op match*)
									 | _ -> s; )(*e matcc*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Gt ->  
										 
										 let bexp = BinOp(Ge,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGtToGe <- counters.chgGtToGe + 1 ;
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Gt ->  
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGtToGe <- counters.chgGtToGe + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(**************************************************************************) 

class changeLtToEqVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
  						      if repair_stmt ss = true
						      then begin 
  							      if stmtId = s.sid 
							      then begin
  								      (* debug "";*)
  								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LtToEq stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LtToEq currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LtToEq currentloc %s \n " lw ;
								      debug "If: LtToEq current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Lt -> 
									      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToEq <- counters.chgLtToEq + 1 ; 
        								      { s with skind = copy }				
									    |_ -> s;)(*op match*)
									 |_ -> s;)(*e match*) 
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Lt ->  
										 
										 let bexp = BinOp(Eq,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLtToEq <- counters.chgLtToEq + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Lt ->  
									      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToEq <- counters.chgLtToEq + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(******************************************************************)

class changeLtToNeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor

		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin
								      debug "stmtid is equal to s.sid";
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LtToNe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LtToNe currentlocd %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LtToNe currentloc %s \n " lw ;
								      debug "If: LtToNe current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Lt -> 
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToNe <- counters.chgLtToNe + 1 ; 
        								      { s with skind = copy }				
									    |_ -> s;)(*op match*)
									 | _ -> s;)(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Lt ->  
										 
										 let bexp = BinOp(Ne,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgLtToNe <- counters.chgLtToNe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Lt ->  
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLtToNe <- counters.chgLtToNe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(*******************************************************************)

class changeLtToGtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin  
							      if stmtId = s.sid 
							      then begin
								      debug "stmtId is equal to s.sid";
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LtToGt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LtToGt currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LtToGt currentloc %s \n " lw ;
								      debug "If: LtToGt current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Lt ->  
									      
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToGt <- counters.chgLtToGt + 1 ; 
        								      { s with skind = copy }				
									    |_ -> s;)(*op match*)
									 | _ -> s; ) (*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Lt ->  
										 
										 let bexp = BinOp(Gt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLtToGt <- counters.chgLtToGt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Lt ->  
									      
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLtToGt <- counters.chgLtToGt + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(******************************************************************)

class changeLtToGeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId : int)  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid
							      then begin
								      debug "stmtId is equal to s.sid " ;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LtToGe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LtToGe currentloc %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LtToGe currentloc %s \n " lw ;
								      debug "If: LtToGe current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Lt -> 
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToGe <- counters.chgLtToGe + 1 ; 
        								      { s with skind = copy }									 													
									    |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Lt ->  
										 
										 let bexp = BinOp(Ge,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLtToGe <- counters.chgLtToGe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Lt ->  
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLtToGe <- counters.chgLtToGe + 1 ;  
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(********************************************************************)

class changeLtToLeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if s.sid = stmtId
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LtToLe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LtToLe currentloc before assigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LtToLe currentloc after assigned %s \n " lw ;*)
								      
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Lt -> 
								 	      
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLtToLe <- counters.chgLtToLe + 1 ; 
        								      { s with skind = copy }						
									    |_ -> s;	)(*op match*)
									 |_ -> s; )(*e match*)
									    
									    
				  				      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Lt ->  
										 
										 let bexp = BinOp(Le,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLtToLe <- counters.chgLtToLe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s; )(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Lt ->  
									      
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLtToLe <- counters.chgLtToLe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(*********************************************************************)

class changeGeToEqVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)
			  (stmtId: int)
			  
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      debug "stmtId is equal to s.sid ";  
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GeToEq stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GeToEq currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GeToEq currentloc %s \n " lw ;
								      debug "If: GeToEq current stmt id %d \n " s.sid; *) 
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ge -> 
									      
									      (*create the new if *)
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToEq <- counters.chgGeToEq + 1 ; 
        								      { s with skind = copy }													   													
									    |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
									    
				  				      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ge ->  
										 
										 let bexp = BinOp(Eq,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgGeToEq <- counters.chgGeToEq + 1 ;
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ge ->  
									      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGeToEq <- counters.chgGeToEq + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	
(**************************************************************************)

class changeGeToNeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int)
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if s.sid = stmtId 
							      then begin
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GeToNe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GeToNe currentloc %s \n " lb ;
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ge -> 
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
									      let the_if = If(bexp,b1,b2,l) in 
									      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToNe <- counters.chgGeToNe + 1 ; 
									      { s with skind = copy }	
										  
							 		    |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
				  				      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ge ->  
										 
										 let bexp = BinOp(Ne,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGeToNe <- counters.chgGeToNe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ge ->  
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToNe <- counters.chgGeToNe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									     (* debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end if s.sid = stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	
	
	
(********************************************************************)
class changeGeToLtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if s.sid = stmtId
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GeToLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GeToLt currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GeToLe currentloc %s \n " lw ;
								      debug "If: GeToLe current stmt id %d \n " s.sid;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ge -> 
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToLt <- counters.chgGeToLt + 1 ; 
        								      { s with skind = copy } 								   													
									    |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ge ->  
										 
										 let bexp = BinOp(Lt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGeToLt <- counters.chgGeToLt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ge ->  
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToLt <- counters.chgGeToLt + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end	 

(********************************************************************)

class changeGeToLeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map) 
			  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if s.sid = stmtId 
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GeToLe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GeToLe currentloc before reassigned %s \n " lb ;
								      (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GeToLe currentloc %s \n " lw ;
								      debug "If: GeToLe current stmt id %d \n " s.sid;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Ge ->  
					 				      
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGeToLe <- counters.chgGeToLe + 1 ; 
        								      { s with skind = copy } 								   													
						  			    |_ -> s;)(*op match*)
									 | _ -> s;)(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ge ->  
										 
										 let bexp = BinOp(Le,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGeToLe <- counters.chgGeToLe + 1 ;
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ge ->  
									      
									      let bexp = BinOp(Le,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGeToLe <- counters.chgGeToLe + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 	
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end

(************************************************************************)
class changeGeToGtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if s.sid = stmtId
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "GeToGt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "GeToGt currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: GeToGt currentloc %s \n " lw ;
								      debug "If: GeToGt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Ge -> 
									      
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgGeToGt <- counters.chgGeToGt + 1 ; 
        								      { s with skind = copy } 									
									    |_ -> s;)(*op match*)
									 |_ -> s;)(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Ge ->  
										 
										 let bexp = BinOp(Gt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgGeToGt <- counters.chgGeToGt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)	
									    
								      (*An assignment ex: x = x-r *)	
								      |Instr([Set(lval,e,_)])-> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Ge ->  			         
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgGeToLe <- counters.chgGeToLe + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; ) (*op match*)
									 |_ -> s; )(*e macth*) 
									    
								      (*An assignment ex: x= x-r *)	
								      (*|Instr([Call(lval,e,[],l)])->
							   let l = get_stmtLoc ss in 
					     let lo= Pretty.sprint ~width:80 (d_loc () l) in
					      debug "instr call :GeToGt stmt loc %s \n " lo  ;  
							(match e with 
						   |BinOp(op,e1,e2,t) -> 
							  (match op with  
							 		|PlusA ->  
										 
										  let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
										  debug "instr():GeToGt currentloc before reassigned %s \n " lb ;
										  currentLoc :=  get_stmtLoc ss ; 
										  let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
										  debug "instr ():GeToGt currentloc %s \n " lw ;
									    debug "instr ():GeToGt current stmt id %d \n " s.sid; 
								      let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 						let the_instr = Instr([Call(lval,bexp,[],l)]) in 
        	 						let instr_stmt = mkStmt the_instr in 
					 						let chg_with = instr_stmt.skind in
           						let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                    counters.chgGeToGt <- counters.chgGeToGt + 1 ; 
        							 { s with skind = copy } 										   													
								   |_ -> s; )(*op match *)
							  |_ -> s;)(*e match *) *)
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 	
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	
	
(**********************************************************************)

class changeLeToEqVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
			 				      if s.sid = stmtId
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LeToEq stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToEq currentloc before assigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ;
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LeToEq currentloc after reassigned %s \n " lw ;*)
								      match ss with 
								      |If(e,b1,b2,loc) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Le -> 
								 	      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,!currentLoc) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLeToEq <- counters.chgLeToEq + 1 ; 
        								      { s with skind = copy } 
									    |_ -> s;) (*op match*)
									 | _ -> s;)(*e match*) 
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Le ->  
										 
										 let bexp = BinOp(Eq,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLeToEq <- counters.chgLeToEq + 1 ;  
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Le ->  
									      
									      let bexp = BinOp(Eq,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLeToEq <- counters.chgLeToEq + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
									    
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 						
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(*************************************************************)

class changeLeToNeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if s.sid = stmtId 
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LeToNe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToNe currentloc before assigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LeToNe currentloc after assigned %s \n " lw ;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Le -> 
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLeToNe <- counters.chgLeToNe + 1 ; 
        					  			      { s with skind = copy } 
									    |_ -> s;)(*op match*)
									 | _ -> s; )(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Le ->  
										 
										 let bexp = BinOp(Ne,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLeToNe <- counters.chgLeToNe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Le ->  
									      
									      let bexp = BinOp(Ne,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLeToNe <- counters.chgLeToNe + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
				 				  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end


(*************************************************************)

class changeLeToGtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if s.sid = stmtId 
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LeToGt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToGt currentloc %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LeToGt currentloc after assigned %s \n " lw ;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
							 		    |Le ->  
								 	      
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
									      let the_if = If(bexp,b1,b2,l) in 
									      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
									      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
          								      counters.chgLeToGt <- counters.chgLeToGt + 1 ; 
        								      { s with skind = copy } 									   													
									    |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Le ->  
										 let bexp = BinOp(Gt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLeToGt <- counters.chgLeToGt + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Le ->  
									      let bexp = BinOp(Gt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                    							      counters.chgLeToGt <- counters.chgLeToGt + 1 ;  
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
				 				  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	
	
(**********************************************************************)

class changeLeToGeVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if s.sid = stmtId 
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LeToGe stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToGe currentloc %s \n " lb ;
					                              (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LeToGe currentloc after assigned %s \n " lw ;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Le ->  
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLeToGe <- counters.chgLeToGe + 1 ; 
        								      { s with skind = copy } 									   													
							 		    |_ -> s;) (*op match*)
									 | _ -> s;	)(*e match*)
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Le ->  
										 
										 let bexp = BinOp(Ge,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLeToGe <- counters.chgLeToGe + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Le ->  
									      
									      let bexp = BinOp(Ge,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgLeToGe <- counters.chgLeToGe + 1 ;  
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
				 				  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(*******************************************************************)

class changeLeToLtVisitor (file : Cil.file) 
			  (counters : counters) 
			  (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if s.sid = stmtId
							      then begin 
								      debug "stmtId:%d is equal to s.sid \n" stmtId;
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "LeToLt stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToLt currentloc before assigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: LeToLt currentloc after assigned %s \n " lw ;*)
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |Le ->  
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLeToLt <- counters.chgLeToLt + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s;)(*op match*)
									 |_ -> s; )(*e match*)
									    
									    
								      (*Return statement *)
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Le ->  
								       		 let bexp = BinOp(Lt,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgLeToLt <- counters.chgLeToLt + 1 ;
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*Op match*)
									    | _ -> s;)(*BinOp match*) 
									 |_ -> s;)(*eo  match*)				

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with  
							 		    |Le ->  
									      
									      let bexp = BinOp(Lt,e1,e2,ulongType) in
        	 							      let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							      let instr_stmt = mkStmt the_instr in 
					 				      let chg_with = instr_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									      counters.chgLeToLt <- counters.chgLeToLt + 1 ;
        								      { s with skind = copy } 										   													
									    |_ -> s; )(*op match *)
									 |_ -> s;)(*e match *) 
									    
								      (*if it is NOT instr , return of If *)  
								      |_ -> s;						
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 
							  end else s (*end can_repair if_stmt *) 
								       
						  end else s (*end if Hashtbl.mem to_chg s.sid *)
					  ) (*end of ChangeDoChildrenPost function *)
end
	

(********************************************************************************)

(*Arithmetic operators *)
class changePlusToMinusVisitor (file : Cil.file) 
			       (counters : counters) 
			       (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      (*  let rec filter s = begin *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if s.sid = stmtId
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug ":PlusToMinus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "PlusToMinus currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:PlusToMult currentloc %s \n " lw ;
								      debug "If:PlusToMult current stmt id %d \n " s.sid;  *)
								      match ss with 
								      (***************** we should iterate If blocks to change AOP inside the blocks (b1 & b2)***************)
								      (* |If (e,b1,b2,l) -> 
					                                                     List.iter(
						                                               fun bs -> filter (bs) 
					                                           )b1.bstmts	 *)
								
							      | If(e,b1,b2,l) -> 							
								 (match e with 
								  | BinOp(op,e1,e2,t) -> 
								     (match op with 
								      |PlusA ->  
									
									(*create the new if *)
									let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 							let the_if = If(bexp,b1,b2,l) in 
        	 							let if_stmt = mkStmt the_if in 
					 				let chg_with = if_stmt.skind in
           								let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									counters.chgPlusToMult <- counters.chgPlusToMult + 1 ; 
        								{ s with skind = copy } 										   													
								      | _ -> s;) (*Op match*)
								  | _ -> s;) (*e match*)		
								     
							      (*An assignment ex: x= x-r *)	
							      |Instr([Set(lval,e,_)]) -> 
								(match e with 
								 | BinOp(op,e1,e2,t) -> 
								    (match op with  
							 	     |PlusA ->  
								      
								       let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 						       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 						       let instr_stmt = mkStmt the_instr in 
					 			       let chg_with = instr_stmt.skind in
           							       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                   						       counters.chgPlusToMinus <- counters.chgPlusToMinus + 1 ; 
        							       { s with skind = copy } 										   													
								     | _ -> s;) (*op match *)
								 | _ -> s;) (*e match*) 


 							      (*Return Ex: return (x-y)*)	
							      |Return(eo,l) -> 
								(match eo with 
								 |Some(e) -> 
								   (match e with 
								    |BinOp(op,e1,e2,t) -> 
								      (match op with  
							 	       |PlusA ->  
									 
									 let bexp = BinOp(MinusA,e1,e2,ulongType) in
									 let the_return = Return(Some(bexp),l) in 
        	 							 let return_stmt = mkStmt the_return in 
					 				 let chg_with = return_stmt.skind in
           								 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							 (* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        								 counters.chgPlusToMinus <- counters.chgPlusToMinus + 1 ; 
        								 { s with skind = copy } 										   													
								       |_ -> s; )(*op match *)
								    | _ -> s; ) (*e match*) 
								 |_ -> s;) (*eo match *)	
								    
							      (*|Loop(b,l,so1,so2) ->*)
							      (*********************** This is wrong becuse it will iterate throught all stmts in block  *)
							      (*********************** stmt inside block can be instr and If stmt types .. *)
								    
								    
							      (*if it it is not If,return,assignment*)				
							      |_ -> s;
								  end else begin 
									      (*debug "stmtId:%d is not equal to s.sid \n" stmtId;*)
									      s (*end s.sid =  stmtId *)
									  end 						
							  end else s (*end can_repair if_stmt *) 								
						  end else s 
					  ) 
end


(***********************************************************************)
class changePlusToMultVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if s.sid = stmtId
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "PlusToMult stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "PlusToMult currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:PlusToMult currentloc %s \n " lw ;
								      debug "If:PlusToMult current stmt id %d \n " s.sid;*)  

								      
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |PlusA ->  
										
										(*create the new if *)
										let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgPlusToMult <- counters.chgPlusToMult + 1 ; 
        									{ s with skind = copy } 										   													
									      | _ -> s;) (*Op match*)
									  | _ -> s;) (*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |PlusA ->  
									       
									       let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									       counters.chgPlusToMult <- counters.chgPlusToMult + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |PlusA ->  
										 
										 let bexp = BinOp(Mult,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgPlusToMult <- counters.chgPlusToMult + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*op match*)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;) (*eo match*)
									    
								      (*if it is not If, return, or assignement stmt*)	
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s (*end can_repair if_stmt *) 								
							  end else s 
					  ) 
end

(***************************************************************************)

class changePlusToDivVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if s.sid = stmtId
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "PlusToDiv stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "PlusToDiv currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "LeToLt currentloc %s \n " lw ;
								      debug "LeToLt current stmt id %d \n " s.sid;*)  
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |PlusA ->  
										
									 	let bexp = BinOp(Div,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                  								counters.chgPlusToDiv <- counters.chgPlusToDiv + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;) (*Op match*)
									  | _ -> s;)(*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |PlusA ->  
									       
									       let bexp = BinOp(Div,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									       counters.chgPlusToDiv <- counters.chgPlusToDiv + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |PlusA ->  
										  
										 let bexp = BinOp(Div,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                   								 counters.chgPlusToDiv <- counters.chgPlusToDiv + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; )(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)(*eo match*)
								      (*if it is not If,return, or assignemnt stmt*)
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end

(*************************************************************************)

class changePlusToModVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin
							      if s.sid = stmtId
							      then begin  
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "PlusToMod stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "PlusToMod currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:PlusToMod currentloc %s \n " lw ;
								      debug "If:PlusToMod current stmt id %d \n " s.sid;  *)

								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
							 		      |PlusA ->  
									
										(*create the new if *)
										let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgPlusToMod <- counters.chgPlusToMod + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)(*op match*)
									  | _ -> s;) (*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |PlusA ->  
									      
									       let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgPlusToMod <- counters.chgPlusToMod + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |PlusA ->  
										
										 let bexp = BinOp(Mod,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgPlusToMod <- counters.chgPlusToMod + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; )(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;) (*eo match *)
								      (*if it is not If, return, assignment*)
								      |_ -> s;
								  end else begin 
									      s
									  end 
								  end else s							
							  end else s 
					  ) 
end

(***************************************************************************)
class changeMinusToPlusVisitor (file : Cil.file) 
			       (counters : counters) 
			       (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MinusToPlus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MinusToPlus currentloc before reassigned %s \n " lb ;
					                              (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If: MinusToPlus currentloc %s \n " lw ;
								      debug "If: MinusToPlus current stmt id %d \n " s.sid;*) 
								      
								      match ss with 
								      |If(e,b1,b2,l) -> 							
									(match e with 
									 |BinOp(op,e1,e2,t) -> 
									   (match op with 
									    |MinusA ->  
									      
									      let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 							      let the_if = If(bexp,b1,b2,l) in 
        	 							      let if_stmt = mkStmt the_if in 
					 				      let chg_with = if_stmt.skind in
           								      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							      counters.chgMinusToPlus <- counters.chgMinusToPlus + 1 ; 
        								      { s with skind = copy } 										   													
									    |_ -> s;) (*op match*)
									 |_ -> s;) (*e match*)
									    
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |MinusA ->  
									      
									       let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                    							       counters.chgMinusToPlus <- counters.chgMinusToPlus + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 |_ -> s;) (*e match*) 
									    
								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |MinusA ->  
										 
										 let bexp = BinOp(PlusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMinusToPlus <- counters.chgMinusToPlus + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; )(*op match*)
									    | _ -> s; )(*e match*) 
									 |_ -> s;)(*eo match*)				
								      (*If it is not If, return. assignement stmt*)
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end

(********************************************************************)

class changeMinusToMultVisitor (file : Cil.file) 
			       (counters : counters) 
			       (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin
							      if stmtId= s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MinusToMult stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MinusToMult currentloc before reassigned %s \n " lb ;
					                             (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MinusToMult currentloc %s \n " lw ;
								      debug "If:MinusToMult current stmt id %d \n " s.sid; *)
								      
				   				      match ss with 
								      (*and if stmt EX: if (x-y>0)*)
								      | If(e,b1,b2,l) -> 
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with  
							 		      |MinusA ->  
										
										let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgMinusToMult <- counters.chgMinusToMult + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s; )
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |MinusA ->  
									       
									       let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgMinusToMult <- counters.chgMinusToMult + 1 ; 
        								       { s with skind = copy } 										   													     |_ -> s; )(*op match*)
									 | _ -> s; ) (*e match*) 
									    
								      (*loop : it is always While loop in CIL transofrmation ex: while (1) {if(x+y>0)}else {break;} *)
								      (*  in this case the while() and ll its if and if block has teh same ID*)
								      (* How we get to loop like this while(j+j < 3) ??*)
								      (* |Loop(b,l,so1,so2)-> 
					 (match so1 with 
						| Some(s)->
						 (match s.skind with 
						  | If(e,b1,b2,l) ->
							(match e with 
						   | BinOp(op,e1,e2,t) -> 
							  (match op with  
							 		|MinusA ->  
								       let l = get_stmtLoc ss in 
					             let lo= Pretty.sprint ~width:80 (d_loc () l) in
					             debug "Loop:MinusToMult stmt loc %s \n " lo  ; 
										   let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
										   debug "Loop:MinusToMult currentloc before reassigned %s \n " lb ;
										   currentLoc :=  get_stmtLoc ss ; 
										   let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
										   debug "Loop:MinusToMult currentloc %s \n " lw ;
									     debug "Loop:MinusToMult current stmt id %d \n " s.sid;  
										   	let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 							let the_if = If(bexp,b1,b2,l) in 
        	 							let if_stmt = mkStmt the_if in 
					 							let chg_with = if_stmt.skind in
           						  let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     		(* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        								counters.chgMinusToMult <- counters.chgMinusToMult + 1 ; 
        							  { s with skind = copy } 										   													
								
							    |_ -> s;)
						   |_ -> s;) 
					    |_ -> s)
					  |_ -> s;)*)
									    
								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |MinusA ->  
										  
										 let bexp = BinOp(Mult,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMinusToMult <- counters.chgMinusToMult + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s;)(*op match *)
									    | _ -> s;) (*e match*) 
									 |_ -> s;)	(*eo match*)				
									    
								      (*if it is not If, return, assignment*)																									  						
								      |_ -> s; (*first match ss *)
				 				  end else begin
									      s
									  end
								  end else s (*end can_repair if_stmt *) 								
							  end else s 
					  ) 
end

(*********************************************************************)

class changeMinusToDivVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId = s.sid
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MinusToDiv stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MinusToDiv currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MinusToDiv currentloc %s \n " lw ;
								      debug "If:MinusToDiv current stmt id %d \n " s.sid; *)
								      
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |MinusA ->  
										
									 	let bexp = BinOp(Div,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgMinusToDiv <- counters.chgMinusToDiv + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)(*op match*)
									  | _ -> s;)(*e match*)

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |MinusA ->  
									     
									       let bexp = BinOp(Div,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
									       counters.chgMinusToDiv <- counters.chgMinusToDiv + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |MinusA ->  
										
										 let bexp = BinOp(Div,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										 counters.chgMinusToDiv <- counters.chgMinusToDiv + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s;)(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;) (*eo match*)					
								      (*if it is not if, return, assignment stmt *)					
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s								
							  end else s 
					  ) 
end

(*********************************************************************)

class changeMinusToModVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MinusToMod stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MinusToMod currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MinusToMod currentloc %s \n " lw ;
								      debug "If:MinusToMod current stmt id %d \n " s.sid;  *)

								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |MinusA ->  
										
										(*create the new if *)
										let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgMinusToMod <- counters.chgMinusToMod + 1 ; 
        									{ s with skind = copy } 										   													
									      | _ -> s;) (*op match*)
									  | _ -> s;)(*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |MinusA ->  
									      
									       let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                    							       counters.chgMinusToMod <- counters.chgMinusToMod + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |MinusA ->  
										
										 let bexp = BinOp(Mod,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMinusToMod <- counters.chgMinusToMod + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; )(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)(*eo match*)					
								      (*if it is not If, return, assignment stmt *)
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s								
							  end else s 
					  ) 
end


(*********************************************************************)

class changeMultToPlusVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId= s.sid 
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MultToPlus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MultToPlus currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MultToPlus currentloc %s \n " lw ;
								      debug "If:MultToPlus current stmt id %d \n " s.sid;*) 
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mult ->  
										
										(*create the new if *)
										let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgMultToPlus <- counters.chgMultToPlus + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;) (*op match *)
									  | _ -> s;)(*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mult ->  
									       
									       let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgMultToPlus <- counters.chgMultToPlus + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s; )(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mult ->  
										
										 let bexp = BinOp(PlusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMultToPlus <- counters.chgMultToPlus + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end

(***********************************************************************)
class changeMultToMinusVisitor (file : Cil.file) 
			       (counters : counters) 
			       (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MultToMinus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MultToMinus currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MultToMinus currentloc %s \n " lw ;
								      debug "If:MultToMinus current stmt id %d \n " s.sid;*)

								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mult ->  
										
										(*create the new if *)
										let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
										counters.chgMultToMinus <- counters.chgMultToMinus + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;) (*op match*)
									  | _ -> s;) (*e match*)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mult ->  
									      
									       let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                   							       counters.chgMultToMinus <- counters.chgMultToMinus + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s;)(*op match *)
									 | _ -> s;) (*e match*) 

 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mult ->  
										 
										 let bexp = BinOp(MinusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                  								 counters.chgMultToMinus <- counters.chgMultToMinus + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; )(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end
							  end else s									
						  end else s 
					  ) 
end

(************************************************************************)
class changeMultToDivVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MultToDiv stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MultToDiv currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MultToDiv currentloc %s \n " lw ;
								      debug "If:MultToDiv current stmt id %d \n " s.sid;  *)

								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mult ->  
										
									 	(*create the new if *)
										let bexp = BinOp(Div,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgMultToDiv <- counters.chgMultToDiv + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mult ->  
									       
									       let bexp = BinOp(Div,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgMultToDiv <- counters.chgMultToDiv + 1 ; 
        								       { s with skind = copy } 										   													
									     |_ -> s;)(*op match *)
									 | _ -> s;) (*e match*) 

 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mult ->  
										  
										 let bexp = BinOp(Div,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMultToDiv <- counters.chgMultToDiv + 1 ; 
        									 { s with skind = copy } 										   													
									       |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s									
							  end else s 
					  ) 
end

(*******************************************************************)

class changeMultToModVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map) (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "MultToMod stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "MultToMod currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:MultToMod currentloc %s \n " lw ;
								      debug "If:MultToMod current stmt id %d \n " s.sid; *) 
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mult ->  
										
										(*create the new if *)
										let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgMultToMod <- counters.chgMultToMod + 1 ; 
        									{ s with skind = copy } 										   													
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mult ->  
									       
									       let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgMultToMod <- counters.chgMultToMod + 1 ; 
        								       { s with skind = copy } 										   													
										   
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mult ->  
										 
										 let bexp = BinOp(Mod,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgMultToMod <- counters.chgMultToMod + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s									
							  end else s 
					  ) 
end

(*******************************************************************)
class changeDivToPlusVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin
							      if stmtId = s.sid 
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "DivToPlus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "DivToPlus currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:DivToPlus currentloc %s \n " lw ;
								      debug "If:DivToPlus current stmt id %d \n " s.sid; *)
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
										
									      |Div  ->  
										
										(*create the new if *)
										let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgDivToPlus <- counters.chgDivToPlus + 1 ; 
        									{ s with skind = copy } 										   													
										    
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Div ->  
									       
									       let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgDivToPlus <- counters.chgDivToPlus + 1 ; 
        								       { s with skind = copy } 										   													     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Div ->  
										  
										 let bexp = BinOp(PlusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgDivToPlus <- counters.chgDivToPlus + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s							
							  end else s 
					  ) 
end

(***********************************************************************)
class changeDivToMinusVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "DivToMinus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "DivToMinus currentloc before reassigned %s \n " lb ;
					                              (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:DivToMinus currentloc %s \n " lw ;
								      debug "If:DivToMinus current stmt id %d \n " s.sid;*)  
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Div  ->  
									
										(*create the new if *)
										let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgDivToMinus <- counters.chgDivToMinus + 1 ; 
        									{ s with skind = copy } 										   												        |_ -> s;)
									  | _ -> s; )
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Div ->  
									       
									       let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgDivToMinus <- counters.chgDivToMinus + 1 ; 
        								       { s with skind = copy } 										   													     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Div ->  
										 
										 let bexp = BinOp(MinusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgDivToMinus <- counters.chgDivToMinus + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s										
							  end else s 
					  ) 
end

(**************************************************************************)
class changeDivToMultVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int)  
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId =s.sid
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "DivToMult stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "DivToMult currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:DivToMult currentloc %s \n " lw ;
								      debug "If:DivToMult current stmt id %d \n " s.sid;*)   
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Div  ->  
										(*create the new if *)
										let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgDivToMult <- counters.chgDivToMult + 1 ; 
        									{ s with skind = copy } 										   													
										    
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Div ->  
									       let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgDivToMult <- counters.chgDivToMult + 1 ; 
        								       { s with skind = copy } 										   													
										   
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Div ->  
										 
										 let bexp = BinOp(Mult,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgDivToMult <- counters.chgDivToMult + 1 ; 
        									 { s with skind = copy } 										   													
										     
									       |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end

(***********************************************************************)

class changeDivToModVisitor (file : Cil.file) 
			    (counters : counters) 
			    (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "DivToMod stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "DivToMod currentloc before reassigned %s \n " lb ;
								      (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "if:DivToMod currentloc %s \n " lw ;
								      debug "if:DivToMod current stmt id %d \n " s.sid;*)  
						
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
										
									      |Div  ->  
										
										(* visitCilFileSameGlobals (del l ) file; *)
										(*create the new if *)
										let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgDivToMod <- counters.chgDivToMod + 1 ; 
        									{ s with skind = copy } 										   													|_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Div -> 

									       let bexp = BinOp(Mod,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgDivToMod <- counters.chgDivToMod + 1 ; 
        								       { s with skind = copy } 										   													     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Div ->  
										 let bexp = BinOp(Mod,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgDivToMod <- counters.chgDivToMod + 1 ; 
        									 { s with skind = copy } 										   													|_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end									    
								  end else s								
							  end else s 
					  ) 
end

(**************************************************************************)

class changeModToPlusVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "ModToPlus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "ModToPlus currentloc before reassigned %s \n " lb ;
					                              (*currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:ModToPlus currentloc %s \n " lw ;
								      debug "If:ModToPlus current stmt id %d \n " s.sid;*) 

								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mod  ->  
									
										(*create the new if *)
										let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgModToPlus <- counters.chgModToPlus + 1 ; 
        									{ s with skind = copy } 										   													
										    
									      |_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mod ->  
									      
									       let bexp = BinOp(PlusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgModToPlus <- counters.chgModToPlus + 1 ; 
        								       { s with skind = copy } 										   													
										   
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mod ->  
										
										 let bexp = BinOp(PlusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     						                 counters.chgModToPlus <- counters.chgModToPlus + 1 ; 
        									 { s with skind = copy } 										   												        |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
									    
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end

(*********************************************************************)
class changeModToMinusVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true
						      then begin
							      if stmtId= s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "ModToMinus stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "ModToMinus currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:ModToMinus currentloc %s \n " lw ;
								      debug "If:ModToMinus current stmt id %d \n " s.sid; *)
								      
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mod  ->  
										
										(*create the new if *)
										let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgModToMinus <- counters.chgModToMinus + 1 ; 
        									{ s with skind = copy } 										   												       |_ -> s;)
									  | _ -> s;)

								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mod ->  
									       
									       let bexp = BinOp(MinusA,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgModToMinus <- counters.chgModToMinus + 1 ; 
        								       { s with skind = copy }  
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mod -> 
										 let bexp = BinOp(MinusA,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgModToMinus <- counters.chgModToMinus + 1 ; 
        									 { s with skind = copy }
									       |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
								      |_ -> s;
								  end else begin
									      s
									  end 
								  end else s								
							  end else s 
					  ) 
end
(***********************************************************************)

class changeModToMultVisitor (file : Cil.file) 
			     (counters : counters) 
			     (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin 
							      if stmtId = s.sid 
							      then begin
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "ModToMult stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "ModToMult currentloc before reassigned %s \n " lb ;
								      currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:ModToMult currentloc %s \n " lw ;
								      debug "If:ModToMult current stmt id %d \n " s.sid;  
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mod  ->  
										
										
										(* visitCilFileSameGlobals (del l ) file; *)
										(*create the new if *)
										let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								(* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        									counters.chgModToMult <- counters.chgModToMult + 1 ; 
        									{ s with skind = copy } 										   													
										    
									      |_ -> s; )
									  | _ ->s;)
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mod ->  
									       
									       let bexp = BinOp(Mult,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       (* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        								       counters.chgModToMult <- counters.chgModToMult + 1 ; 
        								       { s with skind = copy } 										   													
										   
									     |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mod ->  
										 
										 let bexp = BinOp(Mult,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 (* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        									 counters.chgModToMult <- counters.chgModToMult + 1 ; 
        									 { s with skind = copy } 										   													
										     
									       |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;						
								  end else begin
									      s
									  end 
							  end else s								
						  end else s 
					  ) 
end

(**************************************************************************)

class changeModToDivVisitor (file : Cil.file) 
			    (counters : counters) 
			    (to_chg : stmt_map)  (stmtId : int) 
  = object
    inherit nopCilVisitor
    (* If (x>y) is in the to_del mapping, we replace > with < *)
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid 
					      then begin
						      let ss= Hashtbl.find to_chg s.sid in
						      if repair_stmt ss = true 
						      then begin
							      if stmtId = s.sid
							      then begin 
								      let l = get_stmtLoc ss in 
								      let lo= Pretty.sprint ~width:80 (d_loc () l) in
								      debug "ModToDiv stmt loc %s \n " lo  ; 
								      let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "ModToDiv currentloc before reassigned %s \n " lb ;
								     (* currentLoc :=  get_stmtLoc ss ; 
								      let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								      debug "If:ModToDiv currentloc %s \n " lw ;
								      debug "If:ModToDiv current stmt id %d \n " s.sid;*)
								      match ss with 
								      | If(e,b1,b2,l) -> 							
									 (match e with 
									  | BinOp(op,e1,e2,t) -> 
									     (match op with 
									      |Mod  ->  
										(*create the new if *)
										let bexp = BinOp(Div,e1,e2,ulongType) in
        	 								let the_if = If(bexp,b1,b2,l) in 
        	 								let if_stmt = mkStmt the_if in 
					 					let chg_with = if_stmt.skind in
           									let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								counters.chgModToDiv <- counters.chgModToDiv + 1 ; 
        									{ s with skind = copy } 										   												      |_ -> s;)
									  | _ -> s;)
									     
								      (*An assignment ex: x= x-r *)	
								      |Instr([Set(lval,e,_)]) -> 
									(match e with 
									 | BinOp(op,e1,e2,t) -> 
									    (match op with  
							 		     |Mod ->  
									       
									       let bexp = BinOp(Div,e1,e2,ulongType) in
        	 							       let the_instr = Instr([Set(lval,bexp,l)]) in 
        	 							       let instr_stmt = mkStmt the_instr in 
					 				       let chg_with = instr_stmt.skind in
           								       let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     							       counters.chgModToDiv <- counters.chgModToDiv + 1 ; 
        								       { s with skind = copy } 										   													      |_ -> s; (*op match*))(*op match *)
									 | _ -> s;) (*e match*) 


 								      (*Return Ex: return (x-y)*)	
								      |Return(eo,l) -> 
									(match eo with 
									 |Some(e) -> 
									   (match e with 
									    |BinOp(op,e1,e2,t) -> 
									      (match op with  
							 		       |Mod ->  
										 let bexp = BinOp(Div,e1,e2,ulongType) in
										 let the_return = Return(Some(bexp),l) in 
        	 								 let return_stmt = mkStmt the_return in 
					 					 let chg_with = return_stmt.skind in
           									 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     								 counters.chgModToDiv <- counters.chgModToDiv + 1 ; 
        									 { s with skind = copy } 										   												        |_ -> s; (*op match*))(*op match *)
									    | _ -> s; ) (*e match*) 
									 |_ -> s;)
									    
								      |_ -> s;
								  end else begin
									      s
									  end
								  end else s								
							  end else s 
					  ) 
end


(*************************************************************************)

class delVisitor (id: int) = object
    inherit nopCilVisitor
 		
    method vstmt s = ChangeDoChildrenPost(s, fun s -> 
					     if s.sid = id 
					     then begin 
						     debug "delete visisot current stmt id %d \n " s.sid; 
						     mkEmptyStmt()
						 end else s 
					 )       
					 
end	
				 
let del = new delVisitor 

(*******************************************************)

class delStmtVisitor (loc: Cil.location)= object
    inherit nopCilVisitor
    (* If (x,_) is in the to_del mapping, we replace x with { } -- an
     * empty statement. *) 
    method vstmt s = ChangeDoChildrenPost(s, fun s ->
					     
					     if !currentLoc = loc then begin 
									  let cl = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
									  debug "loca inside delete visitor %s \n " cl ;
									  let block = {
									      battrs = [] ;
									      bstmts = [] ; 
									  } in
									  { s with skind = Block(block) } 
								      end else begin 
										  s 
									      end 
					 ) 
end 

let delStmt = new delStmtVisitor

(**************************************************************)

class changeAssignToEqVisitor (file : Cil.file) 
			      (counters : counters) 
			      (to_chg : stmt_map) 
  = object
    inherit nopCilVisitor
		
    method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
					      (*tested if key = s.sid is in the hashtbl *)
					      if Hashtbl.mem to_chg s.sid then begin
										  let ss= Hashtbl.find to_chg s.sid in
										  if repair_stmt ss = true then begin 
														   let l = get_stmtLoc ss in 
														   let lo= Pretty.sprint ~width:80 (d_loc () l) in
														   debug "If:AssignToEq stmt loc %s \n " lo  ; 
														   let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
														   debug "If:AssignToEq currentloc before reassigned %s \n " lb ;
														   currentLoc :=  get_stmtLoc ss ; 
														   (*(match ss with 
			   |Instr([Set(lval,e,_)]) ->
			    (match e with 
			     | Const(c) -> 
			           let nc= Pretty.sprint ~width:80 (Pretty.dprintf "%s[%s]" v.vname d_const () e) in
			         debug "constant %s \n " nc  ; 
				 | _ -> ();)
			   | _ -> ();) ;*)
			     											   
														   match ss with 
														   | If(e,b1,b2,l) -> 							
														      (match e with 
														       | Lval(host, NoOffset) -> 
															  (match host with 
															   | Var(v)->
															      (*delete stmt but I do not think is doing what I want .
						      It is not deleting assignmenet  a =c/1 *)
															      (*let l = get_stmtLoc ss in 
								let lo= Pretty.sprint ~width:80 (d_loc () l) in
								debug "If:AssignToEq stmt loc %s \n " lo  ; 
								let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
								debug "If:AssignToEq currentloc before reassigned %s \n " lb ;
								currentLoc :=  get_stmtLoc ss ; 
								let block = {battrs = [] ; bstmts = [] ;} in*)
															      (*{ s with skind = Block(block) } ;*)
															      (*copy makes copy for varniable a but we want to copy c /1*)
															      (*let newCons = copyVarinfo v "g" in
								let lv = (Var(newCons),NoOffset) in
								let lvp = Pretty.sprint ~width:80 (d_lval() lv) in
								debug "Value of newCons %s \n " lvp  ;*)
															      (*let newE = Lval(Var(newCons),NoOffset) in *)
															      (*let lvp = Pretty.sprint ~width:80 (d_lval() lv) in*)
															      let bexp = BinOp(Eq,e,e,ulongType) in
        	 													      let the_if = If(bexp,b1,b2,l) in 
        	 													      let if_stmt = mkStmt the_if in 
					 										      let chg_with = if_stmt.skind in
           														      let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     													      counters.chgAssignToEq <- counters.chgAssignToEq + 1 ; 
        														      { s with skind = copy } 										
         														   | _ -> s;) (*host match*)
														       | _ -> s;) (*e match*)	
															  
														   | _ -> s; (*ss match*)
													       end else s (*end repair_stmt if stmt*)
									      end  else s (*end hashtl.mem if stmt*)
					  ) 
end 
	
(* method vstmt s =  ChangeDoChildrenPost(s, fun s ->            
           (*tested if key = s.sid is in the hashtbl *)
        if Hashtbl.mem to_chg s.sid then begin
           let ss= Hashtbl.find to_chg s.sid in
			if repair_stmt ss = true then begin 
			match ss with 
               | If(e,b1,b2,l) -> 							
				(match e with 
					| Lval(host, NoOffset) -> 
					  (match host with 
						  | Var(v)->
						       let l = get_stmtLoc ss in 
		     	               let lo= Pretty.sprint ~width:80 (d_loc () l) in
					           debug "If:AssignToEq stmt loc %s \n " lo  ; 
							   let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
							   debug "If:AssignToEq currentloc before reassigned %s \n " lb ;
							   currentLoc :=  get_stmtLoc ss ; 
							   let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
							   debug "If:AssignToEq currentloc %s \n " lw ;
							   debug "If:AssignToEq current stmt id %d \n " s.sid;  
						(*--------------> delet stmt declear a to constant to another variable*)
								visitCilFileSameGlobals (del s.sid) file;   
						(*--------------> find how to creat nother e that hs the other have of the if stmt*)
							 	let bexp = BinOp(Eq,e,e,ulongType) in
        	 							let the_if = If(bexp,b1,b2,l) in 
        	 							let if_stmt = mkStmt the_if in 
					 							let chg_with = if_stmt.skind in
           						  let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                     		(* let s' = { s with sid = 0 } in 
           							let stmt =  {s' with skind = copy } in *)
        								counters.chgAssignToEq <- counters.chgAssignToEq + 1 ; 
        							  { s with skind = copy } 										   													
						  | _ -> s;	)
						 | _ -> s;)	
						 
					
			
			(*(match e with 
			 | Const(cons) ->
						let l = get_stmtLoc ss in 
						let lo= Pretty.sprint ~width:80 (d_loc () l) in
						debug "If:AssignToEq stmt loc %s \n " lo  ; 
						let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
						debug "If:AssignToEq currentloc before reassigned %s \n " lb ;
						currentLoc :=  get_stmtLoc ss ; 
						let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
						debug "If:AssignToEq currentloc %s \n " lw ;
						(*let cexp = Const(CInt64(int64,IInt,None)) in (* for not it is limited to IInt: int*)*)
						 let fopen_va = makeVarinfo true "fopen" (TVoid []) in
						 let bexp = BinOp(Eq,e,e,ulongType) in
        	 			 let the_if = If(bexp,b1,b2,l) in 
        	 			 let if_stmt = mkStmt the_if in
					 	 let chg_with = if_stmt.skind in
           				 let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                		 counters.chgModToDiv <- counters.chgModToDiv + 1 ; 
        					 { s with skind = copy } 
																   													
					 | _ -> s;)*)
				
				(*| CInt64(i,kind,_) ->
							  let l = get_stmtLoc ss in 
					          let lo= Pretty.sprint ~width:80 (d_loc () l) in
					          debug "If:ModToDiv stmt loc %s \n " lo  ; 
							  let lb = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
							  debug "If:ModToDiv currentloc before reassigned %s \n " lb ;
							  currentLoc :=  get_stmtLoc ss ; 
							  let lw = Pretty.sprint ~width:80 (d_loc () !currentLoc) in
							  debug "If:ModToDiv currentloc %s \n " lw ;
							  debug "If:ModToDiv current stmt id %d \n " s.sid;  
							  (*let cexp = Const(CInt64(int64,IInt,None)) in (* for not it is limited to IInt: int*)*)
							  let nlval = (Var(!uniq_array_va)), (Index(Cons)) in
							  let nexp = Lval(nlval) in 
							  let bexp = BinOp(Eq,,e,ulongType) in
        	 				  let the_if = If(bexp,b1,b2,l) in 
        	 				  let if_stmt = mkStmt the_if in 
					 		  let chg_with = if_stmt.skind in
           					  let copy =  (visitCilStmt my_zero (mkStmt(copy chg_with))).skind in 
                		      counters.chgModToDiv <- counters.chgModToDiv + 1 ; 
        							  { s with skind = copy } 
									| _ -> s; )										   													
							 | _ -> s;)*)
							
					
					|_ -> s;						
				end else s								
      end else s 
    ) 
end *)


(***********************************************************************
 * Genetic Programming Functions - Mutation
 ***********************************************************************)

(* let mutation_chance = ref 0.2 
let crossover_chance = ref 1.0 
let ins_chance = ref 1.0 
let del_chance = ref 1.0 
let swap_chance = ref 1.0 
let template_chance = ref 0.0 *)

let mutation_chance = ref 0.2 
let crossover_chance = ref 1.0 
(*let ins_chance = ref 1.0 *)
(*let del_chance = ref 1.0 *)
(* Ne *)
let chgNeToEq_chance = ref 1.0
let chgNeToLt_chance = ref 1.0
let chgNeToGt_chance = ref 1.0
let chgNeToLe_chance = ref 1.0
let chgNeToGe_chance = ref 1.0
(* Eq *)
let chgEqToNe_chance = ref 1.0
let chgEqToLe_chance = ref 1.0
let chgEqToGe_chance = ref 1.0
let chgEqToGt_chance = ref 1.0
let chgEqToLt_chance = ref 1.0
(* Gt *)
let chgGtToEq_chance = ref 1.0
let chgGtToNe_chance = ref 1.0
let chgGtToLe_chance = ref 1.0
let chgGtToLt_chance = ref 1.0
let chgGtToGe_chance = ref 1.0
(* Lt *)
let chgLtToEq_chance = ref 1.0
let chgLtToNe_chance = ref 1.0
let chgLtToGt_chance = ref 1.0
let chgLtToGe_chance = ref 1.0
let chgLtToLe_chance = ref 1.0
(* Ge *) 
let chgGeToEq_chance = ref 1.0
let chgGeToNe_chance = ref 1.0
let chgGeToLe_chance = ref 1.0
let chgGeToLt_chance = ref 1.0
let chgGeToGt_chance = ref 1.0
(* Le *)
let chgLeToEq_chance = ref 1.0
let chgLeToNe_chance = ref 1.0
let chgLeToGt_chance = ref 1.0
let chgLeToGe_chance = ref 1.0
let chgLeToLt_chance = ref 1.0
(*
(*LAnd *)
let chgLAndToLOr_chance = ref 1.0
let chgLAndToBAnd_chance = ref 1.0
let chgLAndToBXor_chance = ref 1.0
let chgLAndToBOr_chance = ref 1.0
(*LOr *)
let chgLOrToLAnd_chance = ref 1.0
let chgLOrToBAnd_chance = ref 1.0
let chgLOrToBXor_chance = ref 1.0
let chgLOrToBOr_chance = ref 1.0
 *)
(*BAnd*)
let chgBAndToBXor_chance = ref 1.0
let chgBAndToBOr_chance = ref 1.0
(*BXor*)
let chgBXorToBAnd_chance = ref 1.0
let chgBXorToBOr_chance = ref 1.0
(*BOr*)
let chgBOrToBAnd_chance = ref 1.0
let chgBOrToBXor_chance = ref 1.0
(*BS*)
let chgBSLtToBSRt_chance = ref 1.0
let chgBSRtToBSLt_chance = ref 1.0
(*PlusA *)
let chgPlusToMinus_chance = ref 1.0
let chgPlusToMult_chance = ref 1.0
let chgPlusToDiv_chance = ref 1.0
let chgPlusToMod_chance = ref 1.0
(*MinusA *)
let chgMinusToPlus_chance = ref 1.0
let chgMinusToMult_chance = ref 1.0
let chgMinusToDiv_chance = ref 1.0
let chgMinusToMod_chance = ref 1.0
(*Mult *)
let chgMultToPlus_chance = ref 1.0
let chgMultToMinus_chance = ref 1.0
let chgMultToDiv_chance = ref 1.0
let chgMultToMod_chance = ref 1.0
(*Div *)
let chgDivToPlus_chance = ref 1.0
let chgDivToMinus_chance = ref 1.0
let chgDivToMult_chance = ref 1.0
let chgDivToMod_chance = ref 1.0
(*Mod *)
let chgModToPlus_chance = ref 1.0
let chgModToMinus_chance = ref 1.0
let chgModToMult_chance = ref 1.0
let chgModToDiv_chance = ref 1.0
(*AssignToEq*)
let chgAssignToEq_chance = ref 1.0


(*let swap_chance = ref 1.0 *)
let template_chance = ref 0.0

(* This function randomly mutates an individual 'i'. 
 * Each statement in i's critical path has a 'prob' % chance of being
 * randomly changed. Does not change 'i' -- instead, it returns a new copy
 * for the mutated result. *) 
let total_number_of_macromutations = ref 0 
let total_number_of_micromutations = ref 0 
let rec mutation   (i : individual) 
		   (op : string)
		   (o : int)
		   (id: int)
        (* returns *) : individual =
  let (file,ht,count,path,track,idfun,fun_id_hash_table) = i in
  let new_track = copy track in 
  new_track.current.mut <- new_track.current.mut + 1 ;
  Stats2.time "mutation" (fun () -> 
			  let force = true in
			  let any = ref false in (* any mutations made? *) 
			  let to_swap = Hashtbl.create 255 in 
			  let must_modify_step = ref None in 
			  if force then begin
					   match random_order path with
					   | [] -> ()
					   | (step_prob,path_step) :: tl -> must_modify_step := Some(path_step )
				       end ; 
			  incr total_number_of_macromutations ; 
			  let mutated_num = ref 0 in
			  List.iter (fun (step_prob,path_step) ->
				     let forced = Some(path_step) = !must_modify_step in 

				     if (!mutated_num < !mutation_max) && ((probability step_prob ) || forced) 
				     then begin
					     (* Change this path element by replacing/appending/deleting it
					      * with respect to a random element elsewhere anywhere in *the entire
					      * file* (not just on the path). 
					      *
					      * Note that in each mutation run, each statement will only be 
					      * considered once. If we're already swapping (55,33) and we later
					      * come to 66 and decide to swap it with 33 as well, we instead do
					      * nothing (since 33 is already being used). *)
					     let replace_with_id = 1 + (Random.int (pred count)) 
					     in 
					     if (Hashtbl.mem to_swap replace_with_id || 
						     Hashtbl.mem to_swap path_step) && not forced then
						 ()
					     else begin
						     try 
							 if not (Hashtbl.mem ht path_step) then begin
												   debug "cannot find path_step %d in ht\n" path_step 
											       end ; 
							 if not (Hashtbl.mem ht replace_with_id) then begin
													 debug "cannot find replace_with_id %d in ht\n" replace_with_id 
												     end  ;
							 (*let ss = Hashtbl.find ht path_step in *)
							 if !fixloc then(**增加了是否进行fix localization*)
							     begin
								 let fun_path_step = Hashtbl.find idfun path_step in
								 let idlist_fun = Hashtbl.find fun_id_hash_table fun_path_step in
								 let fix_replace_with_id = List.nth idlist_fun (Random.int (List.length idlist_fun)) in
          							 let rs = Hashtbl.find ht fix_replace_with_id in 
								 Hashtbl.add to_swap path_step rs ;(*debug "target***%d and %d\n" path_step fix_replace_with_id;*)
								 incr mutated_num;
          						     (*Hashtbl.add to_swap fix_replace_with_id ss*) 
							     end
							 else
							     begin 
								 let ss = Hashtbl.find ht path_step in 
								 let rs = Hashtbl.find ht replace_with_id in 
								 (*Hashtbl.add to_swap path_step rs ;
                                                                 Hashtbl.add to_swap replace_with_id ss ; *)
								 (*no swaping *)
								 Hashtbl.add to_swap path_step ss ;
								 Hashtbl.add to_swap replace_with_id rs ;
							         (*let rs = Hashtbl.find ht replace_with_id in 
                                                                 Hashtbl.add to_swap path_step rs ;
                                                                incr mutated_num;*)
          						     (*Hashtbl.add to_swap replace_with_id ss*) 
							     end;
							 incr total_number_of_micromutations ; 
							 (*
                                                            debug "\t\tAdding path_Step = %d, replace_With_id = %d\n" 
                                                             path_step replace_with_id ; 
							  *)
							 any := true ; 
						     with _ -> ()
						 end ;
					 end 
				    ) path ; 
			  (* Actually apply the mutation to some number of elements of the path. 
			   * The mutation is either a swap, an append or a delete. *) 
			  
			  
			  (*let keys_lst = hashtbl_keys to_swap in
                            debug "print to_swap hastble \n" ; 
                               List.iter (debug "%d \n ") keys_lst ; *)
			  
			  let file = copy file in (* don't destroy the original *) 
    			  let v =
  			    
			    (*Ne*) 
			    if op = "Ne" && o = 1 then
				new changeNeToEqVisitor  
			    else if  op = "Ne" && o = 2 then
				new changeNeToLeVisitor 
			    else if op = "Ne" && o = 3 then
				new changeNeToLtVisitor 
			    else if op = "Ne" && o = 4 then
				new changeNeToGtVisitor 
			    else if op = "Ne" && o = 5 then 
				new changeNeToGeVisitor 
				    
			    (*Eq*)
			    else if op = "Eq"  && o = 1 then
				new changeEqToNeVisitor
			    else if op = "Eq" && o = 2 then
				new changeEqToLeVisitor 
			    else if op = "Eq" && o = 3 then
				new changeEqToLtVisitor
			    else if op = "Eq" && o = 4 then
				new changeEqToGeVisitor 
			    else if op = "Eq" && o = 5  then
				new changeEqToGtVisitor 
			    (*Lt*)
			    else if op = "Lt" && o = 1  then 
				new changeLtToEqVisitor 
			    else if op = "Lt" && o = 2 then
				new changeLtToNeVisitor 
			    else if op = "Lt"  && o = 3 then
				new changeLtToLeVisitor 
			    else if op = "Lt" && o = 4 then
				new changeLtToGtVisitor 
			    else if op = "Lt" && o = 5 then
				new changeLtToGeVisitor
			    (*Le*)
			    else if op = "Le" && o = 1 then
				new changeLeToEqVisitor 
			    else if op = "Le" && o = 2 then
				new changeLeToNeVisitor 
			    else if op = "Le" && o = 3 then
				new changeLeToLtVisitor  
			    else if op = "Le"  && o = 4 then
				new changeLeToGtVisitor
			    else if op = "Le" && o = 5 then
				new changeLeToGeVisitor
				    
			    (*Gt*)
			    else if  op = "Gt"  && o = 1 then
				new changeGtToEqVisitor 
			    else if  op = "Gt"  && o = 2 then
				new changeGtToNeVisitor
			    else if op = "Gt" && o = 3 then
				new changeGtToLtVisitor
			    else if op = "Gt" && o = 4 then
				new changeGtToLeVisitor 
			    else if  op = "Gt" && o = 5 then
				new changeGtToGeVisitor
			    (*Ge*)
			    else if op = "Ge"  && o = 1 then
				new changeGeToEqVisitor 
			    else if op = "Ge" && o = 2 then
				new changeGeToNeVisitor
			    else if op = "Ge" && o = 3 then
				new changeGeToLtVisitor
			    else if op = "Ge" && o = 4 then
				new changeGeToLeVisitor 
			    else if op = "Ge" && o = 5 then
				new changeGeToGtVisitor 
				    
			    (*Plus*)
			    else if op = "PlusA" && o = 1 then
				new changePlusToMinusVisitor
			    else if op = "PlusA"  && o = 2 then
				new changePlusToMultVisitor
			    else if op = "PlusA" && o = 3 then
				new changePlusToDivVisitor
			    else if op = "PlusA" && o = 4 then
				new changePlusToModVisitor
				    
			    (*Minus*)
			    else if  op = "MinusA" && o = 1 then
				new changeMinusToPlusVisitor
			    else if op = "MinusA" && o = 2 then
				new changeMinusToMultVisitor
			    else if op = "MinusA" && o = 3 then
				new changeMinusToModVisitor
			    else if op = "MinusA" && o = 4 then
				new changeMinusToDivVisitor
				    
			    (*Mutl*)
			    else if op = "Mult" && o = 1 then
				new changeMultToPlusVisitor	
			    else if op = "Mult" && o = 2 then
				new changeMultToMinusVisitor	
			    else if op = "Mult" && o = 3 then
				new changeMultToModVisitor	
			    else if op = "Mult" && o = 4 then
				new changeMultToDivVisitor
				    
			    (*Mod*)
			    else if op = "Mod" && o = 1 then
				new changeModToPlusVisitor	
			    else if op = "Mod" && o = 2 then
				new changeModToMinusVisitor	
			    else if op = "Mod" && o = 3 then
				new changeModToMultVisitor	
			    else if op = "Mod" && o = 4 then
				new changeModToDivVisitor
				    
			    (*Div*)
			    else if op = "Div" && o = 1 then
				new changeDivToPlusVisitor	
			    else if op = "Div" && o = 2 then
				new changeDivToMinusVisitor	
			    else if op = "Div" && o = 3 then
				new changeDivToMultVisitor	
			    else if op = "Div"  && o = 4 then
	  			new changeDivToModVisitor	
			    (*BAnd*)
			    else if op = "BAnd" && o = 1 then
                                    new changeBAndToBXorVisitor 
			    else if op = "BAnd" && o = 2 then
                                     new changeBAndToBOrVisitor

					 
(*BXor *)
else if op =  "BXor" && o = 1 then 	
new changeBXorToBAndVisitor	
else if  op = "BXor" && o = 2 then 	
new changeBXorToBOrVisitor 
    
(*BOr*)
else if op = "BOr" && o = 1 then 	
new changeBOrToBAndVisitor
else if op = "BOr" && o = 2 then 	
new changeBOrToBXorVisitor
    
(*BShift*)
else if op = "Shiftlt" then 	
new changeBSLtToBSRtVisitor		
    
else  
new changeBSRtToBSLtVisitor																																					

		  in 
			  
			  let my_visitor = v file new_track.current ht id in 
			  visitCilFileSameGlobals my_visitor file ; 
			  (*debug "here executed a mutation";*)
			  file, ht, count, path, new_track,idfun,fun_id_hash_table
								     
			 ) () 


(***********************************************************************
 * Genetic Programming Functions - Fitness 
 ***********************************************************************)

let gcc_cmd = ref "gcc" 
let ldflags = ref "" 
let good_cmd = ref "./test-good.sh" 
let bad_cmd = ref  "./test-bad.sh" 
let check_cmd = ref "./test-check.sh"
let compile_counter = ref 0 (* how many _attempted_ compiles so far? *) 
let compile_fail = ref 0
let compile_tried = ref 0
let continue = ref false 
let input_params = ref ""
let max_fitness = ref 15 
let most_fit = ref None 
let baseline_file = ref "" 
let first_solution_at = ref 0. 
let first_solution_count = ref 0 
let fitness_count = ref 0 
let bad_factor = ref 10.0 
let exit_code = ref false
let compute_count = ref 0(**用于显示每代的计算的个体数*)

(* For web-based applications we need to pass a 'probably unused' port
 * number to the fitness-function shell scripts. This is a unix
 * implementation detail -- once you've started a server on port 8080, 
 * even if you kill your server another user program cannot bind to
 * that port for a few seconds. So if we want to run a thousand copies
 * of a webserver rapidly, we need to assign each one a new local port
 * number. *) 
let port = ref 808

(* Because fitness evaluation is so expensive, we cache (or memoize)
 * results. We cache not based on the internal AST data structure, but
 * on the serialized program text -- because two prorgrams with
 * different ASTs (say, different statement numbers) might actually print
 * the same way and thus yield the same results for the compiler. Instead,
 * we get the MD5 sum of the printed program text and use that as a cache
 * key. *) 
let fitness_ht : (Digest.t, float) Hashtbl.t = Hashtbl.create 255  

(* There is a fairly complicated interface between this function, which
 * calculates the fitness of a given individual, and ./test-good.sh and
 * ./test-bad.sh.
 *
 * You must write test-good.sh so that it takes 3 arguments
 *  1. the executable name (e.g., ./program-1.exe)
 *  2. a new text file to write each success to (e.g., ./good-1.txt) 
 *      -- for each successful testcase, write a line to this file.
 *         it doesn't matter what the line says, but by convention
 *         I write the name of the testcase there. 
 *  3. a port prefix (e.g., 808)
 *      -- if you are a webserver, you can safely uses 8080 to 8089 
 *         for yourself
 *
 * test-bad.sh works similarly. 
 *)
let total_avg = ref (new_counters())
let nonzerofitness_avg = ref (new_counters ())
let total_fitness_evals = ref 0
let total_nonzerofitness_evals = ref 0
let random_fitness = ref false 
let countp = ref 0 

let fitness (i : individual) 
    (* returns *) : float = 
  incr total_fitness_evals;
  let (file,ht,count,path,tracking,_,_) = i in 
  Stats2.time "fitness" (fun () -> 
			 try 
			     let a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,
				 (**)a27,a28,a29,a30,a31,a32,a33,a34,a35,a36,a37,a38,a39,a40,a41,a42,a43,a44,a45,a46,a47,a48,a49,a50,a51,a52,a53,a54
				 ,a55,a56,a57,a58,a59,a60,a61,a62 =
			       (*a54,a55,a56,a57,a58,a59,a60,a61,a62,a63,a64,a65,a66,a67,a68,a69,a70,a71,a72,a73 = *)
			       (* ( tracking.current.ins    -   tracking.at_last_fitness.ins   ),
    ( tracking.current.del    -   tracking.at_last_fitness.del   ),
    ( tracking.current.swap   -   tracking.at_last_fitness.swap  ),*)
			       (*Ne*)
			       ( tracking.current.chgNeToEq  -   tracking.at_last_fitness.chgNeToEq  ),
			       ( tracking.current.chgNeToLt  -   tracking.at_last_fitness.chgNeToLt  ),
			       ( tracking.current.chgNeToGt  -   tracking.at_last_fitness.chgNeToGt  ),
			       ( tracking.current.chgNeToGe  -   tracking.at_last_fitness.chgNeToGe  ),
			       ( tracking.current.chgNeToLe  -   tracking.at_last_fitness.chgNeToLe  ),
			       (*Eq*)
			       ( tracking.current.chgEqToNe  -   tracking.at_last_fitness.chgEqToNe  ),
			       ( tracking.current.chgEqToLe  -   tracking.at_last_fitness.chgEqToLe  ),
			       ( tracking.current.chgEqToGe  -   tracking.at_last_fitness.chgEqToGe  ),	
			       ( tracking.current.chgEqToGt  -   tracking.at_last_fitness.chgEqToGt  ),
			       ( tracking.current.chgEqToLt  -   tracking.at_last_fitness.chgEqToLt  ),
			       (*Gt*)
			       ( tracking.current.chgGtToEq  -   tracking.at_last_fitness.chgGtToEq  ),
			       ( tracking.current.chgGtToNe  -   tracking.at_last_fitness.chgGtToNe  ),
			       ( tracking.current.chgGtToLe  -   tracking.at_last_fitness.chgGtToLe  ),
			       ( tracking.current.chgGtToLt  -   tracking.at_last_fitness.chgGtToLt  ),
			       ( tracking.current.chgGtToGe  -   tracking.at_last_fitness.chgGtToGe  ),
			       (*Lt*)
			       ( tracking.current.chgLtToEq  -   tracking.at_last_fitness.chgLtToEq  ),
			       ( tracking.current.chgLtToNe  -   tracking.at_last_fitness.chgLtToNe  ),
			       ( tracking.current.chgLtToGt  -   tracking.at_last_fitness.chgLtToGt  ),
			       ( tracking.current.chgLtToGe  -   tracking.at_last_fitness.chgLtToGe  ),
			       ( tracking.current.chgLtToLe  -   tracking.at_last_fitness.chgLtToLe  ),
			       (*Ge*)
			       ( tracking.current.chgGeToEq  -   tracking.at_last_fitness.chgGeToEq  ),
			       ( tracking.current.chgGeToNe  -   tracking.at_last_fitness.chgGeToNe  ),
			       ( tracking.current.chgGeToLe  -   tracking.at_last_fitness.chgGeToLe  ),
			       ( tracking.current.chgGeToLt  -   tracking.at_last_fitness.chgGeToLt  ),
			       ( tracking.current.chgGeToGt  -   tracking.at_last_fitness.chgGeToGt  ),
			       (*Le*)
			       ( tracking.current.chgLeToEq  -   tracking.at_last_fitness.chgLeToEq  ),
			       ( tracking.current.chgLeToNe  -   tracking.at_last_fitness.chgLeToNe  ),
			       ( tracking.current.chgLeToGt  -   tracking.at_last_fitness.chgLeToGt  ),
			       ( tracking.current.chgLeToGe  -   tracking.at_last_fitness.chgLeToGe  ),
			       ( tracking.current.chgLeToLt  -   tracking.at_last_fitness.chgLeToLt  ),
			       (*
		(*LAnd*)
		( tracking.current.chgLAndToLOr  -   tracking.at_last_fitness.chgLAndToLOr),
		( tracking.current.chgLAndToBAnd  -   tracking.at_last_fitness.chgLAndToBAnd), 
		( tracking.current.chgLAndToBXor  -   tracking.at_last_fitness.chgLAndToBXor), 
		( tracking.current.chgLAndToBOr  -   tracking.at_last_fitness.chgLAndToBOr),  
		(*LOr*)
		( tracking.current.chgLOrToLAnd  -   tracking.at_last_fitness.chgLOrToLAnd),
		( tracking.current.chgLOrToBAnd  -   tracking.at_last_fitness.chgLOrToBAnd), 
		( tracking.current.chgLOrToBXor  -   tracking.at_last_fitness.chgLOrToBXor), 
		( tracking.current.chgLOrToBOr  -   tracking.at_last_fitness.chgLOrToBOr),*)
			       (*BAnd*)
			       ( tracking.current.chgBAndToBXor  -   tracking.at_last_fitness.chgBAndToBXor), 
			       ( tracking.current.chgBAndToBOr  -   tracking.at_last_fitness.chgBAndToBOr),
			       (*BXor*)
			       ( tracking.current.chgBXorToBAnd  -   tracking.at_last_fitness.chgBXorToBAnd), 
			       ( tracking.current.chgBXorToBOr  -   tracking.at_last_fitness.chgBXorToBOr),
			       (*BOr*)
			       ( tracking.current.chgBOrToBAnd  -   tracking.at_last_fitness.chgBOrToBAnd), 
			       ( tracking.current.chgBOrToBXor  -   tracking.at_last_fitness.chgBOrToBXor),
			       (*BS*)
			       ( tracking.current.chgBSLtToBSRt  -   tracking.at_last_fitness.chgBSLtToBSRt),
			       ( tracking.current.chgBSRtToBSLt  -   tracking.at_last_fitness.chgBSRtToBSLt),
			       (*arthimatci ops*)
			       (*PlusA*)
			       ( tracking.current.chgPlusToMinus  -   tracking.at_last_fitness.chgPlusToMinus),
			       ( tracking.current.chgPlusToMult  -   tracking.at_last_fitness.chgPlusToMult),
			       ( tracking.current.chgPlusToDiv  -   tracking.at_last_fitness.chgPlusToDiv),
			       ( tracking.current.chgPlusToMod  -   tracking.at_last_fitness.chgPlusToMod),
			       (*MinusA*)
			       ( tracking.current.chgMinusToPlus  -   tracking.at_last_fitness.chgMinusToPlus),
			       ( tracking.current.chgMinusToMult  -   tracking.at_last_fitness.chgMinusToMult),
			       ( tracking.current.chgMinusToDiv  -   tracking.at_last_fitness.chgMinusToDiv),
			       ( tracking.current.chgMinusToMod  -   tracking.at_last_fitness.chgMinusToMod),
			       (*Mult*)
			       ( tracking.current.chgMultToPlus  -   tracking.at_last_fitness.chgMultToPlus),
			       ( tracking.current.chgMultToMinus  -   tracking.at_last_fitness.chgMultToMinus),
			       ( tracking.current.chgMultToDiv  -   tracking.at_last_fitness.chgMultToDiv),
			       ( tracking.current.chgMultToMod  -   tracking.at_last_fitness.chgMultToMod),
			       (*Div*)
			       ( tracking.current.chgDivToPlus  -   tracking.at_last_fitness.chgDivToPlus),
			       ( tracking.current.chgDivToMinus  -   tracking.at_last_fitness.chgDivToMinus),
			       ( tracking.current.chgDivToMult  -   tracking.at_last_fitness.chgDivToMult),
			       ( tracking.current.chgDivToMod  -   tracking.at_last_fitness.chgDivToMod),
			       (*Mod*)
			       ( tracking.current.chgModToPlus  -   tracking.at_last_fitness.chgModToPlus),
			       ( tracking.current.chgModToMinus  -   tracking.at_last_fitness.chgModToMinus),
			       ( tracking.current.chgModToMult  -   tracking.at_last_fitness.chgModToMult),
			       ( tracking.current.chgModToDiv  -   tracking.at_last_fitness.chgModToDiv),
			       (*AssignToEq*)
			       ( tracking.current.chgAssignToEq  -   tracking.at_last_fitness.chgAssignToEq),
			       (*Others*)
			       ( tracking.current.xswap  -   tracking.at_last_fitness.xswap ),
			       ( tracking.current.xover  -   tracking.at_last_fitness.xover ),
			       ( tracking.current.mut    -   tracking.at_last_fitness.mut   ) 
			     in 
			     (* debug "\t\t\ti=%d d=%d s=%d o=%d c=%d m=%d  (delta i=%d d=%d s=%d o=%d c=%d m=%d )\n" *)
			     
			     debug "\t count# %d" !countp ;
			     incr countp;
			     
			     debug "\n\t\tNeToEq=%d NeToLt=%d NeToGt=%d NeToGe=%d NeToLe=%d EqToNe=%d EqToLe=%d EqToGe=%d EqToGt=%d EqToLt=%d
				    GtToEq=%d GtToNe=%d GtToLe=%d GtToLt=%d GtToGe=%d LtToEq=%d LtToNe=%d LtToGt=%d LtToGe=%d LtToLe=%d
				    GeToEq=%d GeToNe=%d GeToLe=%d GeToLt=%d GeToGt=%d LeToEq=%d LeToNe=%d LeToGt=%d LeToGe=%d LeToLt=%d 
				    BAndToBXor=%d BAndToBOr=%d BXorToBAnd=%d BXorToBOr=%d BOrToBAnd=%d BOrToBXor=%d BSLtToBSRt=%d BSRtToBSLt=%d
				    PlusToMinus=%d PlusToMult=%d PlusToDiv=%d PlusToMod=%d MinusToPlus=%d MinusToMult=%d MinusToDiv=%d MinusToMod=%d 
				    MultToPlus=%d MultToMinus=%d MultToDiv=%d MultToMod=%d DivToPlus=%d DivToMinus=%d DivToMult=%d DivToMod=%d
				    ModToPlus=%d ModToMinus=%d ModToMult=%d ModToDiv=%d AssignToEq=%d c=%d m=%d  
				    (delta NeToEq=%d NeToLt=%d NeToGt=%d NeToGe=%d NeToLe=%d EqToNe=%d EqToLe=%d EqToGe=%d EqToGt=%d EqToLt=%d
				    GtToEq=%d GtToNe=%d GtToLe=%d GtToLt=%d GtToGe=%d LtToEq=%d LtTo Ne=%d LtToGt=%d LtToGe=%d LtToLe=%d
				    GeToEq=%d GeToNe=%d GeToLe=%d GeToLt=%d GeToGt=%d LeToEq=%d LeToNe=%d LeToGt=%d LeToGe=%d LeToLt=%d 
				    BAndToBXor=%d BAndToBOr=%d BXorToBAnd=%d BXorToBOr=%d BOrToBAnd=%d BOrToBXor=%d BSLtToBSRt=%d BSRtToBSLt=%d 
				    PlusToMinus=%d PlusToMult=%d PlusToDiv=%d PlusToMod=%d MinusToPlus=%d MinusToMult=%d MinusToDiv=%d MinusToMod=%d 
				    MultToPlus=%d MultToMinus=%d MultToDiv=%d MultToMod=%d DivToPlus=%d DivToMinus=%d DivToMult=%d DivToMod=%d 
				    ModToPlus=%d ModToMinus=%d ModToMult=%d ModToDiv=%d AssignToEq=%d c=%d m=%d )\n"
				   (*tracking.current.ins 
      tracking.current.del 
      tracking.current.swap *)
				   (*Ne*)
				   tracking.current.chgNeToEq
				   tracking.current.chgNeToLt
				   tracking.current.chgNeToGt
				   tracking.current.chgNeToGe
				   tracking.current.chgNeToLe
				   (*Eq*)
				   tracking.current.chgEqToNe
				   tracking.current.chgEqToLe
				   tracking.current.chgEqToGe
				   tracking.current.chgEqToGt
				   tracking.current.chgEqToLt
				   (*Gt*)
				   tracking.current.chgGtToEq
				   tracking.current.chgGtToNe 
				   tracking.current.chgGtToLe 
				   tracking.current.chgGtToLt 
				   tracking.current.chgGtToGe 
				   (*Lt*)
				   tracking.current.chgLtToEq
				   tracking.current.chgLtToNe
				   tracking.current.chgLtToGt
				   tracking.current.chgLtToGe
				   tracking.current.chgLtToLe 
				   (*Ge*)
				   tracking.current.chgGeToEq
				   tracking.current.chgGeToNe 
				   tracking.current.chgGeToLe 
				   tracking.current.chgGeToLt 
				   tracking.current.chgGeToGt 
				   (*Le*)
				   tracking.current.chgLeToEq
				   tracking.current.chgLeToNe
				   tracking.current.chgLeToGt
				   tracking.current.chgLeToGe
				   tracking.current.chgLeToLt
				   (*
			(*LAnd*)
			tracking.current.chgLAndToLOr
			tracking.current.chgLAndToBAnd
			tracking.current.chgLAndToBXor
			tracking.current.chgLAndToBOr
			(*LOr*)
			tracking.current.chgLOrToLAnd
			tracking.current.chgLOrToBAnd
			tracking.current.chgLOrToBXor
			tracking.current.chgLOrToBOr*)
				   (*BAnd*)
				   tracking.current.chgBAndToBXor
				   tracking.current.chgBAndToBOr
				   (*BXor*)
				   tracking.current.chgBXorToBAnd
				   tracking.current.chgBXorToBOr
				   (*BOr*)
				   tracking.current.chgBOrToBAnd
				   tracking.current.chgBOrToBXor
				   (*BS*)
				   tracking.current.chgBSLtToBSRt
				   tracking.current.chgBSRtToBSLt
				   (*Arthimetic ops *)
				   (*Plus*)
				   tracking.current.chgPlusToMinus
				   tracking.current.chgPlusToMult
				   tracking.current.chgPlusToDiv
				   tracking.current.chgPlusToMod
				   (*Minus*)
				   tracking.current.chgMinusToPlus
				   tracking.current.chgMinusToMult
				   tracking.current.chgMinusToDiv
				   tracking.current.chgMinusToMod
				   (*Mult*)
				   tracking.current.chgMultToPlus
				   tracking.current.chgMultToMinus
				   tracking.current.chgMultToDiv
				   tracking.current.chgMultToMod
				   (*Div*)
				   tracking.current.chgDivToPlus
				   tracking.current.chgDivToMinus
				   tracking.current.chgDivToMult
				   tracking.current.chgDivToMod
				   (*Mod*)
				   tracking.current.chgModToPlus
				   tracking.current.chgModToMinus
				   tracking.current.chgModToMult
				   tracking.current.chgModToDiv
				   (**)
				   tracking.current.chgAssignToEq
				   (*Others*)
				   tracking.current.xover 
				   tracking.current.mut 
				   a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61; (* a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 ;*)
			     total_avg := 
				 {(*ins   = !total_avg.ins   + a1;
		      del   = !total_avg.del   + a2;
		      swap  = !total_avg.swap  + a3;*)
				     (*Ne*)
				     chgNeToEq = !total_avg.chgNeToEq + a1;
				     chgNeToLt = !total_avg.chgNeToLt + a2;
				     chgNeToGt = !total_avg.chgNeToGt + a3;
				     chgNeToGe = !total_avg.chgNeToGe + a4;
				     chgNeToLe = !total_avg.chgNeToLe + a5;
				     (*Eq*)
				     chgEqToNe = !total_avg.chgEqToNe + a6;
				     chgEqToLe = !total_avg.chgEqToLe + a7;
				     chgEqToGe = !total_avg.chgEqToGe + a8;
				     chgEqToGt = !total_avg.chgEqToGt + a9;
				     chgEqToLt = !total_avg.chgEqToLt + a10;
		    		     (*Gt*)
				     chgGtToEq = !total_avg.chgGtToEq + a11;
				     chgGtToNe = !total_avg.chgGtToNe + a12;
				     chgGtToLe = !total_avg.chgGtToLe + a13;
				     chgGtToLt = !total_avg.chgGtToLt + a14;
				     chgGtToGe = !total_avg.chgGtToGe + a15;
				     (*Lt*)
				     chgLtToEq = !total_avg.chgLtToEq + a16;
				     chgLtToNe = !total_avg.chgLtToNe + a17;
				     chgLtToGt = !total_avg.chgLtToGt + a18;
				     chgLtToGe = !total_avg.chgLtToGe + a19;
				     chgLtToLe = !total_avg.chgLtToLe + a20;
				     (*Ge*)
				     chgGeToEq = !total_avg.chgGeToEq + a21;
				     chgGeToNe = !total_avg.chgGeToNe + a22;
				     chgGeToLe = !total_avg.chgGeToLe + a23;
				     chgGeToLt = !total_avg.chgGeToLt + a24;
				     chgGeToGt = !total_avg.chgGeToGt + a25;
				     (*Le*)
				     chgLeToEq = !total_avg.chgLeToEq + a26;
				     chgLeToNe = !total_avg.chgLeToNe + a27;
				     chgLeToGt = !total_avg.chgLeToGt + a28;
				     chgLeToGe = !total_avg.chgLeToGe + a29;
				     chgLeToLt = !total_avg.chgLeToLt + a30;
				     (*
					(*LAnd*)
					chgLAndToLOr = !total_avg.chgLAndToLOr + a31;
					chgLAndToBAnd = !total_avg.chgLAndToBAnd + a32;
					chgLAndToBXor = !total_avg.chgLAndToBXor + a33;
					chgLAndToBOr = !total_avg.chgLAndToBOr + a34;
					(*LOr*)
					chgLOrToLAnd = !total_avg.chgLOrToLAnd + a35;
					chgLOrToBAnd = !total_avg.chgLOrToBAnd + a36;
					chgLOrToBXor = !total_avg.chgLOrToBXor + a37;
					chgLOrToBOr = !total_avg.chgLOrToBOr + a38; *)
				     (*BAnd*)
				     chgBAndToBXor = !total_avg.chgBAndToBXor + a31;
				     chgBAndToBOr = !total_avg.chgBAndToBOr + a32;
				     (*BXor*)
				     chgBXorToBAnd = !total_avg.chgBXorToBAnd + a33;
				     chgBXorToBOr = !total_avg.chgBXorToBOr + a34;
				     (*BOr*)
				     chgBOrToBAnd = !total_avg.chgBOrToBAnd + a35;
				     chgBOrToBXor = !total_avg.chgBOrToBXor + a36;
				     (*BS*)
				     chgBSLtToBSRt = !total_avg.chgBSLtToBSRt + a37;
				     chgBSRtToBSLt = !total_avg.chgBSLtToBSRt + a38;
				     (*arth ops *)
				     (*Plus*)
				     chgPlusToMinus = !total_avg.chgPlusToMinus + a39;
				     chgPlusToMult = !total_avg.chgPlusToMult + a40;
				     chgPlusToDiv = !total_avg.chgPlusToDiv + a41;
				     chgPlusToMod = !total_avg.chgPlusToMod + a42;
				     (*Minus*)
				     chgMinusToPlus= !total_avg.chgMinusToPlus + a43;
				     chgMinusToMult = !total_avg.chgMinusToMult + a44;
				     chgMinusToDiv = !total_avg.chgMinusToDiv + a45;
				     chgMinusToMod = !total_avg.chgMinusToMod + a46;
				     (*Mult*)
				     chgMultToPlus= !total_avg.chgMultToPlus + a47;
				     chgMultToMinus = !total_avg.chgMultToMinus + a48;
				     chgMultToDiv = !total_avg.chgMultToDiv + a49;
				     chgMultToMod = !total_avg.chgMultToMod + a50;
				     (*Div*)
				     chgDivToPlus= !total_avg.chgDivToPlus + a51;
				     chgDivToMinus = !total_avg.chgDivToMinus + a52;
				     chgDivToMult = !total_avg.chgDivToMult + a53;
				     chgDivToMod = !total_avg.chgDivToMod + a54;
				     (*Mod*)
				     chgModToPlus= !total_avg.chgModToPlus + a55;
				     chgModToMinus = !total_avg.chgModToMinus + a56;
				     chgModToMult = !total_avg.chgModToMult + a57;
				     chgModToDiv = !total_avg.chgModToDiv + a58;
				     (*AssignToEq*)
				     chgAssignToEq = !total_avg.chgAssignToEq + a59;
				     (*Others*)
				     xswap = !total_avg.xswap + a60;
				     xover = !total_avg.xover + a61;
				     mut   = !total_avg.mut   + a62;};

			     tracking.at_last_fitness <- copy tracking.current ; 
			     

			     
			     
			     (*try 
    let a1,a2,a3,a4,a5,a6 =
    ( tracking.current.ins    -   tracking.at_last_fitness.ins   ),
    ( tracking.current.del    -   tracking.at_last_fitness.del   ),
    ( tracking.current.swap   -   tracking.at_last_fitness.swap  ),
    ( tracking.current.xswap  -   tracking.at_last_fitness.xswap ),
    ( tracking.current.xover  -   tracking.at_last_fitness.xover ),
    ( tracking.current.mut    -   tracking.at_last_fitness.mut   ) 
    in 
    debug "\t\t\ti=%d d=%d s=%d c=%d m=%d (delta i=%d d=%d s=%d c=%d m=%d)\n" 
      tracking.current.ins 
      tracking.current.del 
      tracking.current.swap 
      tracking.current.xover 
      tracking.current.mut 
      a1 a2 a3 a4 a5 ; 
    total_avg := 
         {ins   = !total_avg.ins   + a1;
		      del   = !total_avg.del   + a2;
		      swap  = !total_avg.swap  + a3;
		      xswap = !total_avg.xswap + a4;
		      xover = !total_avg.xover + a5;
		      mut   = !total_avg.mut   + a6;};

    tracking.at_last_fitness <- copy tracking.current ; *)

			     (**********
			      * Fitness Step 1. Write out the C file from the in-memory AST. 
			      *)
			     let c = !compile_counter in
			     incr compile_counter ; 
			     let source_out = Printf.sprintf "%05d-file.c" c in 
			     let fout = open_out source_out in 
			     dumpFile noLineCilPrinter fout source_out file ;
			     close_out fout ; 

			     (**********
			      * Fitness Step 2. Do we have it cached? 
			      *)
			     let digest = Digest.file source_out in 
			     if Hashtbl.mem fitness_ht digest then begin
								      let fitness = Hashtbl.find fitness_ht digest in 
								      debug "\tfitness %g (cached)\n" fitness ; flush stdout ; 
								      fitness 
								  end else begin 

									      (**********
									       * Fitness Step 3. Try to compile it. 
									       *)
									      let exe_name = Printf.sprintf "./%05d-prog" c in 
									      let cmd = Printf.sprintf "%s -o %s %s %s >& /dev/null" !gcc_cmd exe_name source_out !ldflags in 
									      incr compile_tried ; 
									      (match Stats2.time "compile" Unix.system cmd with
									       | Unix.WEXITED(0) -> ()
									       | _ -> begin 
											(**********
											 * Fitness Step 3b. It failed to compile! fitness = 0 
											 *)
											(* printf "%s: does not compile\n" source_out ;  *)
											incr compile_fail;
											failwith "gcc failed"
										    end ) ; 

									      (**********
									       * Fitness Step 4. Run the good and bad testcases. 
									       *
									       * We use 'good testcase' to represent the legitimate requirements 
									       * testcases (e.g., "GET index.html should work") and 'bad testcase'
									       * to represent the anomaly that we're trying to avoid. You 'pass' the
									       * bad testcase if you aren't vulnerable to the exploit (or whatever). 
									       *)
									      let good_name = Printf.sprintf "%05d-good" c in 
									      let bad_name  = Printf.sprintf "%05d-bad" c in 

									      let port_arg = Printf.sprintf "%d" !port in
									      incr port ; 
									      (try Unix.unlink good_name with _ -> () ) ; 
									      (try Unix.unlink bad_name with _ -> () ) ; 

									      let cmd = Printf.sprintf "%s %s %s %d %s >& /dev/null" !good_cmd exe_name good_name (!compute_count+1) port_arg in  (* !compute_count作为随机种子seed传给testgood.sh*)
									      (match Stats2.time "good test" Unix.system cmd with
									       | Unix.WEXITED(0) -> ()
									       | _ -> begin 
											(**********
											 * Fitness Step 4b. The good testcase script failed to run.
											 * 
											 * This is different than 'you failed all the good testcases'. If you
											 * fail all of the good testcases the test script terminates
											 * successfully, but you get a 0-line good.txt file. This means that
											 * that something went really really wrong, and it basically never
											 * happens. 
											 *) 
											debug "FAILED: %s\n" cmd ; failwith "good failed"
										    end ) ; 

									      let cmd = Printf.sprintf "%s %s %s %s >& /dev/null" !bad_cmd exe_name bad_name port_arg in 
									      (match Stats2.time "bad test" Unix.system cmd with
									       | Unix.WEXITED(0) -> ()
									       | _ -> begin 
											(**********
											 * Fitness Step 4c. The bad testcase script failed to run.
											 *
											 * See above. This never happens. 
											 *) 
											debug "FAILED: %s\n" cmd ; failwith "bad failed"
										    end ) ; 

									      incr fitness_count ; (* total number of programs tested *) 

									      (**********
									       * Fitness Step 5. Read in the testcase script results. 
									       *)
									      let good = count_lines_in_file good_name in 
									      let bad  = count_lines_in_file bad_name  in 
									      let fitness = good +. (!bad_factor *. bad) in 
									      (* We write a copy of the fitness results to a file in the directory
									       * for easy debugging. *) 
									      let fname = Printf.sprintf "%05d-fitness" c in 
									      let fout = open_out fname in 
									      Printf.fprintf fout "%g\n" fitness ;
									      close_out fout ;
									      debug "\tfitness %g\n" fitness ; flush stdout ; 

									      if fitness > 0. then begin 
												      incr total_nonzerofitness_evals;
												      nonzerofitness_avg := 
													  {(*ins   = !nonzerofitness_avg.ins   + a1;
		      del   = !nonzerofitness_avg.del   + a2;
		      swap  = !nonzerofitness_avg.swap  + a3;*)
													      (*Ne*)
													      chgNeToEq = !nonzerofitness_avg.chgNeToEq + a1;
													      chgNeToLt = !nonzerofitness_avg.chgNeToLt + a2;
													      chgNeToGt = !nonzerofitness_avg.chgNeToGt + a3;
													      chgNeToGe = !nonzerofitness_avg.chgNeToGe + a4;
													      chgNeToLe = !nonzerofitness_avg.chgNeToLe + a5;
													      (*Eq*)
													      chgEqToNe = !nonzerofitness_avg.chgEqToNe + a6;
													      chgEqToLe = !nonzerofitness_avg.chgEqToLe + a7;
													      chgEqToGe = !nonzerofitness_avg.chgEqToGe + a8;
													      chgEqToGt = !nonzerofitness_avg.chgEqToGt + a9;
													      chgEqToLt = !nonzerofitness_avg.chgEqToLt + a10;
													      (*Gt*)
													      chgGtToEq = !nonzerofitness_avg.chgGtToEq + a11;
		     											      chgGtToNe = !nonzerofitness_avg.chgGtToNe + a12;
													      chgGtToLe = !nonzerofitness_avg.chgGtToLe + a13;
													      chgGtToLt = !nonzerofitness_avg.chgGtToLt + a14;
													      chgGtToGe = !nonzerofitness_avg.chgGtToNe + a15;
													      (*Lt*)
													      chgLtToEq = !nonzerofitness_avg.chgLtToEq + a16;
													      chgLtToNe = !nonzerofitness_avg.chgLtToNe + a17;
													      chgLtToGt = !nonzerofitness_avg.chgLtToGt + a18;
													      chgLtToGe = !nonzerofitness_avg.chgLtToGe + a19;
													      chgLtToLe = !nonzerofitness_avg.chgLtToLe + a20;
													      (*Ge*)
													      chgGeToEq = !nonzerofitness_avg.chgGeToEq + a21;
		     											      chgGeToNe = !nonzerofitness_avg.chgGeToNe + a22;
													      chgGeToLe = !nonzerofitness_avg.chgGeToLe + a23;
													      chgGeToLt = !nonzerofitness_avg.chgGeToLt + a24;
													      chgGeToGt = !nonzerofitness_avg.chgGeToGt + a25;
													      (*Le*)
													      chgLeToEq = !nonzerofitness_avg.chgLeToEq + a26;
													      chgLeToNe = !nonzerofitness_avg.chgLeToNe + a27;
													      chgLeToGt = !nonzerofitness_avg.chgLeToGt + a28;
													      chgLeToGe = !nonzerofitness_avg.chgLeToGe + a29;
													      chgLeToLt = !nonzerofitness_avg.chgLeToLt + a30;
													      (*
					(*LAnd*)
					chgLAndToLOr = !nonzerofitness_avg.chgLAndToLOr + a31;
					chgLAndToBAnd = !nonzerofitness_avg.chgLAndToBAnd + a32;
					chgLAndToBXor = !nonzerofitness_avg.chgLAndToBXor + a33;
					chgLAndToBOr = !nonzerofitness_avg.chgLAndToBOr + a34;
					(*LOr*)
					chgLOrToLAnd = !nonzerofitness_avg.chgLOrToLAnd + a35;
					chgLOrToBAnd = !nonzerofitness_avg.chgLOrToBAnd + a36;
					chgLOrToBXor = !nonzerofitness_avg.chgLOrToBXor + a37;
					chgLOrToBOr = !nonzerofitness_avg.chgLOrToBOr + a38; *)
													      (*BAnd*)
													      chgBAndToBXor = !nonzerofitness_avg.chgBAndToBXor + a31;
													      chgBAndToBOr = !nonzerofitness_avg.chgBAndToBOr + a32;
													      (*BXor*)
													      chgBXorToBAnd = !nonzerofitness_avg.chgBXorToBAnd + a33;
													      chgBXorToBOr = !nonzerofitness_avg.chgBXorToBOr + a34;
													      (*BOr*)
													      chgBOrToBAnd = !nonzerofitness_avg.chgBOrToBAnd + a35;
													      chgBOrToBXor = !nonzerofitness_avg.chgBOrToBXor + a36;
													      (*BS*)
													      chgBSLtToBSRt = !nonzerofitness_avg.chgBSLtToBSRt + a37;
													      chgBSRtToBSLt = !nonzerofitness_avg.chgBSRtToBSLt + a38;
													      (*arthimatic ops *)
													      (*Plus*)
													      chgPlusToMinus = !nonzerofitness_avg.chgPlusToMinus + a39;
													      chgPlusToMult = !nonzerofitness_avg.chgPlusToMult + a40;
													      chgPlusToDiv = !nonzerofitness_avg.chgPlusToDiv + a41;
													      chgPlusToMod = !nonzerofitness_avg.chgPlusToMod + a42;
													      (*Minus*)
													      chgMinusToPlus = !nonzerofitness_avg.chgMinusToPlus + a43;
													      chgMinusToMult = !nonzerofitness_avg.chgMinusToMult + a44;
													      chgMinusToDiv = !nonzerofitness_avg.chgMinusToDiv + a45;
													      chgMinusToMod = !nonzerofitness_avg.chgMinusToMod + a46;
													      (*Mult*)
													      chgMultToPlus = !nonzerofitness_avg.chgMultToPlus + a47;
													      chgMultToMinus = !nonzerofitness_avg.chgMultToMinus + a48;
													      chgMultToDiv = !nonzerofitness_avg.chgMultToDiv + a49;
													      chgMultToMod = !nonzerofitness_avg.chgMultToMod + a50;
													      (*Div*)
													      chgDivToPlus = !nonzerofitness_avg.chgDivToPlus + a51;
													      chgDivToMinus = !nonzerofitness_avg.chgDivToMinus + a52;
													      chgDivToMult = !nonzerofitness_avg.chgDivToMult + a53;
													      chgDivToMod = !nonzerofitness_avg.chgDivToMod + a54;
													      (*Mod*)
													      chgModToPlus = !nonzerofitness_avg.chgModToPlus + a55;
													      chgModToMinus = !nonzerofitness_avg.chgModToMinus + a56;
													      chgModToMult = !nonzerofitness_avg.chgModToMult + a57;
													      chgModToDiv = !nonzerofitness_avg.chgModToDiv + a58;
													      (*AssignToEq*)
													      chgAssignToEq = !nonzerofitness_avg.chgAssignToEq + a59;
													      (*Others*)
													      xswap = !nonzerofitness_avg.xswap + a60;
													      xover = !nonzerofitness_avg.xover + a61;
													      mut   = !nonzerofitness_avg.mut   + a62;};
												  end ;
									      
									      (* nonzerofitness_avg := 
         {ins   = !nonzerofitness_avg.ins   + a1;
		      del   = !nonzerofitness_avg.del   + a2;
		      swap  = !nonzerofitness_avg.swap  + a3;
		      xswap = !nonzerofitness_avg.xswap + a4;
		      xover = !nonzerofitness_avg.xover + a5;
		      mut   = !nonzerofitness_avg.mut   + a6;};
    end ; *)

									      (**********
									       * Fitness Step 6. Is this a good-enough variant? 
									       *)
									      if fitness >= (float_of_int !max_fitness) 
									      then begin

										      if !check_all 
										      then begin(*d对应check_all*)
											      (* 可在此添加是否是正确的验证方法**)
											      incr check_num ; (*增加全部验证次数*)

											      (*输出完整源文件 *********)
											      let source_out_all = Printf.sprintf "%05d-file-check.c" c in 
											      let fout = open_out source_out_all in 
											      dumpFile noLineCilPrinter fout source_out_all file ;
											      close_out fout ; 

											      (*测试所有测试用例 *********)
											      let all_cmd = Printf.sprintf "%s %s  >& /dev/null" !check_cmd source_out_all in  (* *)
											      debug "\tStart to check all the positive test cases(check_num %d):\n" !check_num; flush stdout ;
											      (match Stats2.time "check" Unix.system all_cmd with
											       | Unix.WEXITED(0) -> ( debug "\tCheck successfully all the positive test cases.\n" ; flush stdout ;() )
											       | _ -> begin (*如果返回错误则失败 *********)
													debug "FAILED: %s\n" all_cmd ; failwith "check failed"
												    end ) ; 
											  end;(*d对应check_all*)

										      let size_str = Printf.sprintf "%05d-size" c in 
										      (* we break ties in favor of the smallest 'diff' size *) 
										      let cmd = Printf.sprintf "diff -e %s %s | wc -c > %s" 
													       source_out !baseline_file size_str in 
										      let our_size = (match Stats2.time "size diff" Unix.system cmd with
												      | Unix.WEXITED(0) -> begin 
															     try 
																 let fin = open_in size_str in
																 let line = input_line fin in
																 close_in fin ;
																 my_int_of_string line 
															     with _ -> max_int 
															 end 
												      | _ -> max_int 
												     ) in
										      (* note when we got this variant for debugging purposes *) 
										      let now = Unix.gettimeofday () in 
										      let better = 
											match !most_fit with
											| None -> 
											   first_solution_at := now ; 
											   first_solution_count := !fitness_count ; 
											   true
											| Some(best_size,best_fitness,_,_,_,_) -> 
											   (our_size <= best_size) && 
											       (fitness >= best_fitness) 
										      in
										      if better then begin 
													debug "\t\tbest so far (size delta %d)\n" our_size ; 
													flush stdout ; 
													most_fit := Some(our_size, fitness, file, now, !fitness_count, 
															 copy tracking.current) ;
													if not !continue then begin
																 (* stop early now that we've found one *) 
																 !print_best_output () ;
																 Stats2.print stdout "Genetic Programming Prototype" ; 
																 Stats2.print !debug_out "Genetic Programming Prototype" ; 
																 exit 1 
															     end 
												    end 
										  end ; 
									      let fitness =
										if !random_fitness then
										    Random.float 15.0 
										else
										    fitness
									      in 
									      (* cache this result to save time later *) 
									      Hashtbl.replace fitness_ht digest fitness ; 
									      (* TODO: we can also cache non-compiling files as 0 *) 
									      fitness 
									  end 

			 with _ -> 
			   debug "\tfitness failure\n" ; flush stdout ; 0.
			) () 

(***********************************************************************
 * Genetic Programming Functions - Brute_force 
 ***********************************************************************)

(* *)

(*let gouping (group: string) = 
	
debug "execute one group of mutation"	*)

	      
let brute_force (indiv : individual) 
    (* returns *) :individual list =
  
  let (file,ht,count,path,tracking,idfun,fun_id_hash_table) = indiv in 
  
  let len = List.length path in  
  debug "search: brute: number of statement in bath %d \n" len;

  let lst = List.rev (path) in

  let res = ref [indiv] in 

  (*To debug
List.iter (fun (we,sid ) -> 
            debug "%f \t %d \n" we sid
             ) path ;*)



  (* List.iter ("%d\n") path; *)

  (************************************)														
  (*Ne mutation operators*)

  debug "***********************************************************************************************";
  debug "\t Ne mutation operators \n" ;	

  (*Ne mutation*)

  List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     (* If stmt ********************************)
					     | If(e,b1,b2,l)  -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Ne -> 
						       let op = "Ne" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Ne %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (**************************************)
						     |Eq -> 
						       let op = "Eq" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Ee %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (***********************************************)
						     |Gt -> 
						       let op = "Gt" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If :Gt %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (**********************************************)
						     |Ge -> 
						       let op = "Ge" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Ge %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)	   
						     (***********************************************)
						     |Lt -> 
						       let op = "Lt" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Lt %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (***********************************)
						     |Le -> 
						       let op = "Le" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Le %d \n" stmt ;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (****************************************)
						     |PlusA -> 
						       let op = "PlusA" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "Return:PlusA %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (***************************************)
						     |MinusA -> 
						       let op = "MinusA" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If: MinusA %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     (**************************************)
						     |Mult -> 
						       let op = "Mult" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:Mult %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (**********************************)
						     |Div -> 
						       let op = "Div" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:Div %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     (********************************)
						     |Mod -> 
						       let op = "Mod" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:Mod %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     (**********************************)
						     |BAnd -> 
						       let op = "BAnd" in 
						       let ne = ref 2 in 
						       while !ne > 0 do 
							   debug "Instr:BAnd %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*while loop*)   
						     (**************************)
						     |BAnd -> 
						       let op = "BAnd" in 
						       let ne = ref 2 in 
						       while !ne > 0 do 
							   debug "Instr:BAnd %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*while loop*)
						     (**********************************)
						     |BXor -> 
						       let op = "BXor" in 
						       let ne = ref 2 in 
						       while !ne > 0 do 
							   debug "If:BXor %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     (**********************************)
						     |BOr -> 
						       let op = "BOr" in 
						       let ne = ref 2 in 
						       while !ne > 0 do 
							   debug "If:BOr %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     (***************************)
						     |Shiftrt -> 
  						       let op = "Shiftrt" in
  						       let ne = ref 1 in
  						       debug "If:Shiftrt %d \n" stmt;
  						       let o = !ne in
  						       let new_pop= mutation indiv op o stmt in
  						       res := new_pop :: !res ;
  						       ()
						     (************************************)
						     |Shiftlt -> 
						       let op = "Shiftlt" in 
						       let ne = ref 1 in 
						       debug "Instr:Shiftlt %d \n" stmt;
						       let o = !ne in
						       let new_pop= mutation indiv op o stmt in 
						       res := new_pop :: !res ;
						       ()
						     (***********************************************)
	   
						     | _ -> () ;) (*op match*) 
						 | _ ->  (); ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Ne ->  
							let op = "Ne" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "return:Ne %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
					            (********************************************)
						      |Eq ->  
							let op = "Eq" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "return:Eq %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (******************************************)
						      |Gt -> 
							let op = "Gt" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "Return:Gt %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (*******************************************)
						      |Ge -> 
							let op = "Ge" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "If:Ge %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
								
							done (*While loop*)
						      (*****************************************)
						      |Lt -> 
							let op = "Lt" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "If:Lt %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (***********************************)
						      |Le -> 
							let op = "Le" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "If:Le %d \n" stmt ;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (***************************************)
						      |PlusA -> 
							let op = "PlusA" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "Return:PlusA %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (**********************************)
						      |MinusA -> 
							let op = "MinusA" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "If: MinusA %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
								
							done (*While loop*)
						      (*************************************)
						      |Mult -> 
							let op = "Mult" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "If:Mult %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      (**************************************)
						      |Div -> 
							let op = "Div" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "If:Div %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
								
							done (*While loop*)
						      (*******************************)
						      |Mod -> 
							let op = "Mod" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "If:Mod %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
								
							done (*While loop*)
						      (******************************)
						      |BAnd -> 
							let op = "BAnd" in 
							let ne = ref 2 in 
							while !ne > 0 do 
							    debug "Instr:BAnd %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*while loop*)   
						      (********************************)
						      |BXor -> 
							let op = "BXor" in 
							let ne = ref 2 in 
							while !ne > 0 do 
							    debug "If:BXor %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)  
						      (*************************************)
						      |BOr -> 
							let op = "BOr" in 
							let ne = ref 2 in 
							while !ne > 0 do 
							    debug "If:BOr %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
								
							done (*While loop*)
						      (*********************************)
						      |Shiftrt -> 
  							let op = "Shiftrt" in
  							let ne = ref 1 in
  							debug "If:Shiftrt %d \n" stmt;
  							let o = !ne in
  							let new_pop= mutation indiv op o stmt in
  							res := new_pop :: !res ;
  							() 
						      (*********************************)
						      |Shiftlt -> 
							let op = "Shiftlt" in 
							let ne = ref 1 in 
							debug "Instr:Shiftlt %d \n" stmt;
							let o = !ne in
							let new_pop= mutation indiv op o stmt in 
							res := new_pop :: !res ;
							()
						      (*****************************************)
						      | _ -> () ;) (*op match*) 
						   | _ -> () ; ) (*e macth*)
						| _ -> () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Ne -> 
						     let op = "Ne" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insert:Ne %d \n " stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
                                                   (***********************************************)
						   |Eq -> 
						     let op = "Eq" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:Ee %d\n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (******************************)
						   |Gt -> 
						     let op = "Gt" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:Gt %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
						     done (*While loop*)
						   (**************************************)
						   |Ge -> 
						     let op = "Ge" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "If:Ge %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
							     
						     done (*While loop*)
						   (**********************************)
						   |Lt -> 
						     let op = "Lt" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "If:Lt %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (***********************************)
						   |Le -> 
						     let op = "Le" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "If:Le %d \n" stmt ;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (***********************************)
						   |PlusA -> 
						     debug "PlusA on stmtid: %d" sid ;
						     let op = "PlusA" in 
						     let ne = ref 4 in 
						     while !ne > 0 do 
							 debug "Return:PlusA %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (***********************************)
						   |MinusA -> 
						     let op = "MinusA" in 
						     let ne = ref 4 in 
						     while !ne > 0 do 
							 debug "If: MinusA %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
							     
						     done (*While loop*)
						   (************************************)
						   |Mult -> 
						     let op = "Mult" in 
						     let ne = ref 4 in 
						     while !ne > 0 do 
							 debug "If:Mult %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (***********************************)
						   |Div -> 
						     let op = "Div" in 
						     let ne = ref 4 in 
						     while !ne > 0 do 
							 debug "If:Div %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
							     
						     done (*While loop*)
						   (*******************************)
						   |Mod -> 
						     let op = "Mod" in 
						     let ne = ref 4 in 
						     while !ne > 0 do 
							 debug "If:Mod %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
							     
						     done (*While loop*)
						   (***********************************)
						   |BAnd -> 
						     let op = "BAnd" in 
						     let ne = ref 2 in 
						     while !ne > 0 do 
							 debug "Instr:BAnd %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*while loop*)
						   (**********************************)
						   |BXor -> 
						     let op = "BXor" in 
						     let ne = ref 2 in 
						     while !ne > 0 do 
							 debug "If:BXor %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   (*****************************************)
						   |BOr -> 
						     let op = "BOr" in 
						     let ne = ref 2 in 
						     while !ne > 0 do 
							 debug "If:BOr %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
							     
						     done (*While loop*)
						   (****************************)
						   |Shiftrt -> 
  						     let op = "Shiftrt" in
  						     let ne = ref 1 in
  						     debug "If:Shiftrt %d \n" stmt;
  						     let o = !ne in
  						     let new_pop= mutation indiv op o stmt in
  						     res := new_pop :: !res ;
  						     ()
						   (***************************************)
						   |Shiftlt -> 
						     let op = "Shiftlt" in 
						     let ne = ref 1 in 
						     debug "Instr:Shiftlt %d \n" stmt;
						     let o = !ne in
						     let new_pop= mutation indiv op o stmt in 
						     res := new_pop :: !res ;
						     ()
						   (***********************************)
						   | _ -> () ;) (*op match*) 
						| _ -> () ; ) (*e macth*) 
					     (* Others **********************************) 		
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ;
  
  
  
  (*************************************************)
  (*Eq mutation Operators*)

  debug "***********************************************************************************************";																
  debug "\n \t Eq mutation operators" ;

  (*Ne mutation*)


 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     (* If sttmt *********************************************)
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Eq -> 
						       let op = "Eq" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Ee %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Eq ->  
							let op = "Eq" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "return:Eq %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*) 
						   | _ -> () ; ) (*e macth*)
						| _ -> () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Eq -> 
						     let op = "Eq" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:Ee %d\n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e macth*)
					     (* Others **********************************) 			
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ;*)

  
  
  (*********************************************************************) 	
  (*GT mutation operators*)

  debug "***********************************************************************************************";																																																													
 (* debug "\n \t Gt mutation operators" ;

  List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Gt -> 
						       let op = "Gt" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If :Gt %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Gt -> 
							let op = "Gt" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "Return:Gt %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*) 
						   | _ -> () ; ) (*e macth*)
						| _ -> () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Gt -> 
						     let op = "Gt" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:Gt %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
						     done (*While loop*)
						   | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e macth*)
					     (* Others **********************************) 			
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ;*)

  
  
  (***********************************************************************) 						   						
  (*Ge mutation operattors *)	

  debug "***********************************************************************************************";																																																													
 (* debug "\n \t Ge mutation operators" ;

  List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Ge -> 
						       let op = "Ge" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Ge %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     | _ -> debug "If:Ge:stmtId:%d: Not applicable" stmt ; () ;) (*op match*) 
						 | _ ->  debug "If:Ge:stmtId:%d: Not applicable" stmt ; () ; ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Ge -> 
							let op = "Ge" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "Retunr:Ge %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> debug "return:Ge:stmtId:%d: Not applicable" stmt; ();) (*op match*) 
						   | _ ->  debug "return:Ge:stmtId:%d: Not applicable" stmt ; () ; ) (*e macth*)
						| _ ->  debug "return:Ge:stmtId:%d: Not applicable" stmt ; () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Ge -> 
						     let op = "Ge" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Instr:Ge %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
						     done (*While loop*)
						   | _ ->  debug "Insrt:Ge:stmtId:%d: Not applicable" stmt ; ();) (*op match*)
						| _ ->  debug "Instr:Ge:stmtId:%d: Not applicable" stmt ;() ; ) (*e macth*)
					     (* Others **********************************) 			
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ;*)



  (****************************************) 													

  (*Lt mutation operators*)

  debug "***********************************************************************************************";																																																													
  debug "\n \t Lt mutation operators" ;

 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Lt -> 
						       let op = "Lt" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Lt %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*) 
						 | _ -> () ; ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Lt -> 
							let op = "Lt" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "Return:Lt %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*) 
						   | _ -> () ; ) (*e macth*)
						| _ -> () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Lt -> 
						     let op = "Lt" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:LT %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e macth*)
					     (* Others **********************************) 			
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ; *) 

  


  (*******************************************)
  (*Le mutation operators*)	


  debug "***********************************************************************************************";																																																													
  debug "\n \t Le mutation operators" ;

  (*List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    let l = get_stmtLoc ss in 
	    let lo= Pretty.sprint ~width:80 (d_loc () l) in
	    debug "Le:stmt loc %s \n " lo  ; 
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Le -> 
						       let op = "Le" in 
						       let ne = ref 5 in 
						       while !ne > 0 do 
							   debug "If:Le %d \n" stmt ;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*) 
						 | _ -> () ; ) (*e macth*)
					     (* Return stmt ****************************************)		
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Le -> 
							let op = "Le" in 
							let ne = ref 5 in 
							while !ne > 0 do 
							    debug "Return:Le %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*) 
						   | _ -> () ; ) (*e macth*)
						| _ -> () ;) (*eo match*)
					     (* An assignment ex ex: x= x-r *******************************) 
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						|BinOp(op,e1,e2,t) -> 
						  (match op with  
						   |Le -> 
						     let op = "Le" in 
						     let ne = ref 5 in 
						     while !ne > 0 do 
							 debug "Insrt:Le %d \n" stmt;
							 let o = !ne in
							 let new_pop= mutation indiv op o stmt in 
							 res := new_pop :: !res ;
							 ne := !ne - 1 ;
							 ()
						     done (*While loop*)
						   | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e macth*)
					     (* Others **********************************) 			
					     | _ -> () ; (*ss match*)
					 end;
	   )lst ;*)

  
  
  (****************************************************************************************)
  
  (*Plus Mutations: We used the standard order of operations. For Plus operators, we will replace it first to*)
  (* the operators in the same order. So + inot - , then into * , / , and % *)

  debug "***********************************************************************************************";																																																													
  debug "\n \t Plus mutation operators" ;

 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |PlusA -> 
						       let op = "PlusA" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:PlusA %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e match*)
						    
					     (*An assignment ex: x= x-r **************************)	
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						| BinOp(op,e1,e2,t) -> 
						   (match op with  
						    |PlusA -> 
						      let op = "PlusA" in 
						      let ne = ref 4 in 
						      while !ne > 0 do 
							  debug "Instr:PlusA %d \n" stmt;
							  let o = !ne in
							  let new_pop= mutation indiv op o stmt in 
							  res := new_pop :: !res ;
							  ne := !ne - 1 ;
							  ()
						      done (*While loop*)
						    | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e match*)
						   
					     (* Return Ex: return (x-y)****************************************)
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |PlusA -> 
							let op = "PlusA" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "Return:PlusA %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*)
						   | _ -> () ; ) (*e match*) 
						| _ -> () ; ) (*eo match*)		 		
					     (* Others **************************************)
					     | _ -> () ;
					 end;
	   )lst ; *)

  
  
  (***************************************************************)

  (*Minus Mutations:  We used the standard order of operations. For Minus operators, we will replace it first to*)
  (* the operators in the same order. So - inot + , then into * , / , and % *)
  debug "***********************************************************************************************";																																																													
  debug "\n \t Minus mutation operators" ;

 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |MinusA -> 
						       let op = "MinusA" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If: MinusA %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e match*)
						    
					     (*An assignment ex: x= x-r **************************)	
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						| BinOp(op,e1,e2,t) -> 
						   (match op with  
						    |MinusA -> 
						      let op = "MinusA" in 
						      let ne = ref 4 in 
						      while !ne > 0 do 
							  debug "Instr:MinusA %d \n" stmt;
							  let o = !ne in
							  let new_pop= mutation indiv op o stmt in 
							  res := new_pop :: !res ;
							  ne := !ne - 1 ;
							  ()
						      done (*While loop*)
						    | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e match*)
						   
					     (* Return Ex: return (x-y)****************************************)
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |MinusA -> 
							let op = "MinusA" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "Return:MinusA %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*)
						   | _ -> () ; ) (*e match*) 
						| _ -> () ; ) (*eo match*)		 		
					     (* Others **************************************)
					     | _ -> () ;
					 end;
	   )lst ;*)
  
  
  (**************************************************************)
  (*Mult Mutations:  We used the standard order of operations. For Minus operators, we will replace it first to*)
  (* the operators in the same order. So * inot / , % , then into + and - *)

  debug "***********************************************************************************************";																																																													
  debug "\n \t Mult mutation operators" ;

 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Mult -> 
						       let op = "Mult" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:Mult %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e match*)
						    
					     (*An assignment ex: x= x-r **************************)	
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						| BinOp(op,e1,e2,t) -> 
						   (match op with  
						    |Mult -> 
						      let op = "Mult" in 
						      let ne = ref 4 in 
						      while !ne > 0 do 
							  debug "Instr:Mult %d \n" stmt;
							  let o = !ne in
							  let new_pop= mutation indiv op o stmt in 
							  res := new_pop :: !res ;
							  ne := !ne - 1 ;
							  ()
						      done (*While loop*)
						    | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e match*)
						   
					     (* Return Ex: return (x-y)****************************************)
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Mult -> 
							let op = "Mult" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "Return:Mult %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*)
						   | _ -> () ; ) (*e match*) 
						| _ -> () ; ) (*eo match*)		 		
					     (* Others **************************************)
					     | _ -> () ;
						    
						    
					 end;
	   )lst ;*)
  

  
  (*****************************************************)

  (*Div mutation operators*)
  debug "***********************************************************************************************";																																																													
  debug "\n \t Div mutation operators" ;

 (* List.iter(fun (_, sid) ->
	    let stmt = sid in
	    debug "\n stmt Id from brute_force %d \n" stmt ;
	    let ss= Hashtbl.find ht sid in
	    if repair_stmt ss = true then begin 
					     match ss with 
					     | If(e,b1,b2,l) -> 							
						(match e with 
						 | BinOp(op,e1,e2,t) -> 
						    (match op with 
						     |Div -> 
						       let op = "Div" in 
						       let ne = ref 4 in 
						       while !ne > 0 do 
							   debug "If:Div %d \n" stmt;
							   let o = !ne in
							   let new_pop= mutation indiv op o stmt in 
							   res := new_pop :: !res ;
							   ne := !ne - 1 ;
							   ()
							       
						       done (*While loop*)
						     | _ -> () ;) (*op match*)
						 | _ -> () ; ) (*e match*)
						    
					     (*An assignment ex: x= x-r **************************)	
					     |Instr([Set(lval,e,_)]) -> 
					       (match e with 
						| BinOp(op,e1,e2,t) -> 
						   (match op with  
						    |Div -> 
						      let op = "Div" in 
						      let ne = ref 4 in 
						      while !ne > 0 do 
							  debug "Instr:Div %d \n" stmt;
							  let o = !ne in
							  let new_pop= mutation indiv op o stmt in 
							  res := new_pop :: !res ;
							  ne := !ne - 1 ;
							  ()
						      done (*While loop*)
						    | _ -> () ;) (*op match*)
						| _ -> () ; ) (*e match*)
						   
					     (* Return Ex: return (x-y)****************************************)
					     |Return(eo,l) -> 
					       (match eo with 
						|Some(e) -> 
						  (match e with 
						   |BinOp(op,e1,e2,t) -> 
						     (match op with  
						      |Div -> 
							let op = "Div" in 
							let ne = ref 4 in 
							while !ne > 0 do 
							    debug "Return:Div %d \n" stmt;
							    let o = !ne in
							    let new_pop= mutation indiv op o stmt in 
							    res := new_pop :: !res ;
							    ne := !ne - 1 ;
							    ()
							done (*While loop*)
						      | _ -> () ;) (*op match*)
						   | _ -> () ; ) (*e match*) 
						| _ -> () ; ) (*eo match*)		 		
					     (* Others **************************************)
					     | _ -> () ;
						    
					 end;
	   )lst ;*)

  
  
  
  (***********************************************************)

  (*Mod mutation operators *)

  debug "***********************************************************************************************";																																																													
  debug "\n \t Mod mutation operators" ;

  (* List.iter(fun (_, sid) -> *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |Mod ->  *)
  (* 						       let op = "Mod" in  *)
  (* 						       let ne = ref 4 in  *)
  (* 						       while !ne > 0 do  *)
  (* 							   debug "If:Mod %d \n" stmt; *)
  (* 							   let o = !ne in *)
  (* 							   let new_pop= mutation indiv op o stmt in  *)
  (* 							   res := new_pop :: !res ; *)
  (* 							   ne := !ne - 1 ; *)
  (* 							   () *)
							       
  (* 						       done (\*While loop*\) *)
  (* 						     | _ -> () ;) (\*op match*\) *)
  (* 						 | _ -> () ; ) (\*e match*\) *)
						    
  (* 					     (\*An assignment ex: x= x-r **************************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						| BinOp(op,e1,e2,t) ->  *)
  (* 						   (match op with   *)
  (* 						    |Mod ->  *)
  (* 						      let op = "Mod" in  *)
  (* 						      let ne = ref 4 in  *)
  (* 						      while !ne > 0 do  *)
  (* 							  debug "Instr:Mod %d \n" stmt; *)
  (* 							  let o = !ne in *)
  (* 							  let new_pop= mutation indiv op o stmt in  *)
  (* 							  res := new_pop :: !res ; *)
  (* 							  ne := !ne - 1 ; *)
  (* 							  () *)
  (* 						      done (\*While loop*\) *)
  (* 						    | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; ) (\*e match*\) *)
						   
  (* 					     (\* Return Ex: return (x-y)****************************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |Mod ->  *)
  (* 							let op = "Mod" in  *)
  (* 							let ne = ref 4 in  *)
  (* 							while !ne > 0 do  *)
  (* 							    debug "Return:Mod %d \n" stmt; *)
  (* 							    let o = !ne in *)
  (* 							    let new_pop= mutation indiv op o stmt in  *)
  (* 							    res := new_pop :: !res ; *)
  (* 							    ne := !ne - 1 ; *)
  (* 							    () *)
  (* 							done (\*While loop*\) *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; ) (\*e match*\)  *)
  (* 						| _ -> () ; ) (\*eo match*\)		 		 *)
  (* 					     (\* Others **************************************\) *)
  (* 					     | _ -> () ; *)
						    
  (* 					 end; *)
  (* 	   )lst ; *)

  (*************************************************************************)
  
  
  (*BAnd mutation operators*)

  debug "***********************************************************************************************";																																																													
  (* debug "\n \t BAnd mutation operators" ; *)

  (* List.iter(fun (_, sid) -> *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |BAnd ->  *)
  (* 						       let op = "BAnd" in  *)
  (* 						       let ne = ref 2 in  *)
  (* 						       while !ne > 0 do  *)
  (* 							   debug "If:BAnd %d \n" stmt; *)
  (* 							   let o = !ne in *)
  (* 							   let new_pop= mutation indiv op o stmt in  *)
  (* 							   res := new_pop :: !res ; *)
  (* 							   ne := !ne - 1 ; *)
  (* 							   () *)
  (* 						       done (\*While loop*\) *)
  (* 						     | _ -> () ;) (\*op match*\)  *)
  (* 						 | _ -> () ; ) (\*e match*\) *)
						    
  (* 					     (\*Return statement ***************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |BAnd ->  *)
  (* 							let op = "BAnd" in  *)
  (* 							let ne = ref 2 in  *)
  (* 							while !ne > 0 do  *)
  (* 							    debug " Return:BAnd %d \n" stmt; *)
  (* 							    let o = !ne in *)
  (* 							    let new_pop= mutation indiv op o stmt in  *)
  (* 							    res := new_pop :: !res ; *)
  (* 							    ne := !ne - 1 ; *)
  (* 							    () *)
  (* 							done (\*while loop*\) *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; )(\*e match*\) *)
  (* 						| _ -> () ;)(\*eo match*\) *)
						   
  (* 					     (\*An assignment ex: x= x-r *******************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						|BinOp(op,e1,e2,t) ->  *)
  (* 						  (match op with   *)
  (* 						   |BAnd ->  *)
  (* 						     let op = "BAnd" in  *)
  (* 						     let ne = ref 2 in  *)
  (* 						     while !ne > 0 do  *)
  (* 							 debug "Instr:BAnd %d \n" stmt; *)
  (* 							 let o = !ne in *)
  (* 							 let new_pop= mutation indiv op o stmt in  *)
  (* 							 res := new_pop :: !res ; *)
  (* 							 ne := !ne - 1 ; *)
  (* 							 () *)
  (* 						     done (\*while loop*\) *)
  (* 						   | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; )(\*e match*\) *)
						   
  (* 					     (\* Other *******************************\) *)
  (* 					     | _ -> () ; (\*ss match*\) *)
  (* 					 end; *)
  (* 	   )lst ; *)
  

  (*******************************************************)

  (*BXornd mutation operators*)

  debug "***********************************************************************************************";																																																													
  (* debug "\n \t BXor mutation operators" ; *)

  (* List.iter(fun (_, sid) -> *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |BXor ->  *)
  (* 						       let op = "BXor" in  *)
  (* 						       let ne = ref 2 in  *)
  (* 						       while !ne > 0 do  *)
  (* 							   debug "If:BXor %d \n" stmt; *)
  (* 							   let o = !ne in *)
  (* 							   let new_pop= mutation indiv op o stmt in  *)
  (* 							   res := new_pop :: !res ; *)
  (* 							   ne := !ne - 1 ; *)
  (* 							   () *)
  (* 						       done (\*While loop*\) *)
  (* 						     | _ -> () ;) (\*op match*\)  *)
  (* 						 | _ -> () ; ) (\*e match*\) *)
						    
  (* 					     (\*Return statement ***************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |BXor ->  *)
  (* 							let op = "BXor" in  *)
  (* 							let ne = ref 2 in  *)
  (* 							while !ne > 0 do  *)
  (* 							    debug "Return:BXor %d \n" stmt; *)
  (* 							    let o = !ne in *)
  (* 							    let new_pop= mutation indiv op o stmt in  *)
  (* 							    res := new_pop :: !res ; *)
  (* 							    ne := !ne - 1 ; *)
  (* 							    () *)
  (* 							done (\*while loop*\) *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; )(\*e match*\) *)
  (* 						| _ -> () ;)(\*eo match*\) *)
						   
  (* 					     (\*An assignment ex: x= x-r *******************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						|BinOp(op,e1,e2,t) ->  *)
  (* 						  (match op with   *)
  (* 						   |BXor ->  *)
  (* 						     let op = "BXor" in  *)
  (* 						     let ne = ref 2 in  *)
  (* 						     while !ne > 0 do  *)
  (* 							 debug "Insrt:BXor %d \n" stmt; *)
  (* 							 let o = !ne in *)
  (* 							 let new_pop= mutation indiv op o stmt in  *)
  (* 							 res := new_pop :: !res ; *)
  (* 							 ne := !ne - 1 ; *)
  (* 							 () *)
  (* 						     done (\*while loop*\) *)
  (* 						   | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; )(\*e match*\) *)
  (* 					     (\* Other *******************************\) *)
  (* 					     | _ -> () ; (\*ss match*\) *)
  (* 					 end; *)
  (* 	   )lst ; *)
  
  (*****************************************************)

  (*BOr mutation operators*)

  debug "***********************************************************************************************";																																																													
  (* debug "\n \t BOr mutation operators" ; *)

  (* List.iter(fun (_, sid) -> *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |BOr ->  *)
  (* 						       let op = "BOr" in  *)
  (* 						       let ne = ref 2 in  *)
  (* 						       while !ne > 0 do  *)
  (* 							   debug "If:BOr %d \n" stmt; *)
  (* 							   let o = !ne in *)
  (* 							   let new_pop= mutation indiv op o stmt in  *)
  (* 							   res := new_pop :: !res ; *)
  (* 							   ne := !ne - 1 ; *)
  (* 							   () *)
							       
  (* 						       done (\*While loop*\) *)
  (* 						     | _ -> () ;) (\*op match*\)  *)
  (* 						 | _ -> () ; ) (\*e match*\) *)
						    
  (* 					     (\*Return statement ***************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |BOr ->  *)
  (* 							let op = "BOr" in  *)
  (* 							let ne = ref 2 in  *)
  (* 							while !ne > 0 do  *)
  (* 							    debug "Return:BOr %d \n" stmt; *)
  (* 							    let o = !ne in *)
  (* 							    let new_pop= mutation indiv op o stmt in  *)
  (* 							    res := new_pop :: !res ; *)
  (* 							    ne := !ne - 1 ; *)
  (* 							    () *)
  (* 							done (\*while loop*\) *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; )(\*e match*\) *)
  (* 						| _ -> () ;)(\*eo match*\) *)
						   
  (* 					     (\*An assignment ex: x= x-r *******************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						|BinOp(op,e1,e2,t) ->  *)
  (* 						  (match op with   *)
  (* 						   |BOr ->  *)
  (* 						     let op = "BOr" in  *)
  (* 						     let ne = ref 2 in  *)
  (* 						     while !ne > 0 do  *)
  (* 							 debug "Instr:BOr %d\n" stmt; *)
  (* 							 let o = !ne in *)
  (* 							 let new_pop= mutation indiv op o stmt in  *)
  (* 							 res := new_pop :: !res ; *)
  (* 							 ne := !ne - 1 ; *)
  (* 							 () *)
  (* 						     done (\*while loop*\) *)
  (* 						   | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; )(\*e match*\) *)
						   
  (* 					     (\* Other *******************************\) *)
  (* 					     | _ -> () ; (\*ss match*\) *)
  (* 					 end; *)
  (* 	   )lst ; *)
  

  (*************************************************)
  (*Shiftrt operators*)																										

  debug "***********************************************************************************************";																																																													
  (* debug "\n \t shiftrt mutation operators" ; *)

  (* List.iter(fun (_, sid) ->  *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |Shiftrt ->  *)
  (* 						       let op = "Shiftrt" in  *)
  (* 						       let ne = ref 1 in  *)
  (* 						       debug "If:Shiftrt %d \n" stmt; *)
  (* 						       let o = !ne in *)
  (* 						       let new_pop= mutation indiv op o stmt in  *)
  (* 						       res := new_pop :: !res ; *)
  (* 						       () *)
  (* 						     | _ -> () ;) (\*op match*\) *)
  (* 						 | _ -> () ; )(\*e match*\) *)
  (* 					     (\*Return statement *************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |Shiftrt ->  *)
  (* 							let op = "Shiftrt" in  *)
  (* 							let ne = ref 1 in  *)
  (* 							debug "Return:Shiftrt %d \n" stmt; *)
  (* 							let o = !ne in *)
  (* 							let new_pop= mutation indiv op o stmt in  *)
  (* 							res := new_pop :: !res ; *)
  (* 							() *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; )(\*e match*\) 			 *)
  (* 						| _ -> () ; )(\*eo match*\) 	 *)
						   
  (* 					     (\*An assignment ex: x= x-r **********************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						|BinOp(op,e1,e2,t) ->  *)
  (* 						  (match op with   *)
  (* 						   |Shiftrt ->  *)
  (* 						     let op = "Shiftrt" in  *)
  (* 						     let ne = ref 1 in  *)
  (* 						     debug "Instr:Shiftrt %d \n" stmt; *)
  (* 						     let o = !ne in *)
  (* 						     let new_pop= mutation indiv op o stmt in  *)
  (* 						     res := new_pop :: !res ; *)
  (* 						     () *)
  (* 						   | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; )(\*e match*\) 			 *)
  (* 					     (\*Other ***********************************\) *)
  (* 					     | _ -> () ;(\*ss match*\) *)
  (* 					 end; *)
  (* 	   )lst ; *)
  
  (**********************************************)

  (*Shiftlt operators*)																										

  (* debug "***********************************************************************************************";																																																													 *)
  (* debug "\n \t Shiftlt mutation operators" ; *)

  (* List.iter(fun (_, sid) -> *)
  (* 	    let stmt = sid in *)
  (* 	    debug "\n stmt Id from brute_force %d \n" stmt ; *)
  (* 	    let ss= Hashtbl.find ht sid in *)
  (* 	    if repair_stmt ss = true then begin  *)
  (* 					     match ss with  *)
  (* 					     | If(e,b1,b2,l) -> 							 *)
  (* 						(match e with  *)
  (* 						 | BinOp(op,e1,e2,t) ->  *)
  (* 						    (match op with  *)
  (* 						     |Shiftlt ->  *)
  (* 						       let op = "Shiftlt" in  *)
  (* 						       let ne = ref 1 in  *)
  (* 						       debug "If:Shiftlt %d \n" stmt; *)
  (* 						       let o = !ne in *)
  (* 						       let new_pop= mutation indiv op o stmt in  *)
  (* 						       res := new_pop :: !res ; *)
  (* 						       () *)
  (* 						     | _ -> () ;)  *)
  (* 						 | _ -> () ; ) *)
  (* 					     (\*Return statement *************************\) *)
  (* 					     |Return(eo,l) ->  *)
  (* 					       (match eo with  *)
  (* 						|Some(e) ->  *)
  (* 						  (match e with  *)
  (* 						   |BinOp(op,e1,e2,t) ->  *)
  (* 						     (match op with   *)
  (* 						      |Shiftlt ->  *)
  (* 							let op = "Shiftlt" in  *)
  (* 							let ne = ref 1 in  *)
  (* 							debug "Return:Shiftlt %d \n" stmt; *)
  (* 							let o = !ne in *)
  (* 							let new_pop= mutation indiv op o stmt in  *)
  (* 							res := new_pop :: !res ; *)
  (* 							() *)
  (* 						      | _ -> () ;) (\*op match*\) *)
  (* 						   | _ -> () ; )(\*e match*\) 			 *)
  (* 						| _ -> () ; )(\*eo match*\) 	 *)
						   
  (* 					     (\*An assignment ex: x= x-r **********************\)	 *)
  (* 					     |Instr([Set(lval,e,_)]) ->  *)
  (* 					       (match e with  *)
  (* 						|BinOp(op,e1,e2,t) ->  *)
  (* 						  (match op with   *)
  (* 						   |Shiftlt ->  *)
  (* 						     let op = "Shiftlt" in  *)
  (* 						     let ne = ref 1 in  *)
  (* 						     debug "Instr:Shiftlt %d \n" stmt; *)
  (* 						     let o = !ne in *)
  (* 						     let new_pop= mutation indiv op o stmt in  *)
  (* 						     res := new_pop :: !res ; *)
  (* 						     () *)
  (* 						   | _ -> () ;) (\*op match*\) *)
  (* 						| _ -> () ; )(\*e match*\) 			 *)
  (* 					     (\*Other ***********************************\) *)
  (* 					     | _ -> () ;(\*ss match*\) *)
  (* 					 end; *)
  (* 	   )lst ; *)
  
  (**************************************************)


  (* 1. Determine Fitness. *)
  
  let pop_with_fitness = List.map (fun member ->
				   let f = fitness member in
				    (member,f)
				  )!res in

  !res 

   
   

(***********************************************************************
 * Sanity Checking
 ***********************************************************************)
class sanityVisitor (file : Cil.file) 
                    (visited) 
  = object
    (* If (x,y) is in the to_swap mapping, we replace statement x 
     * with statement y. Presumably (y,x) is also in the mapping. *) 
    inherit nopCilVisitor
    method vstmt s = ChangeDoChildrenPost(s, fun s ->
					     Hashtbl.add visited s.sid true ; s
					 ) 
end 





(***********************************************************************
 * Genetic Programming Functions - Parse Command Line Arguments, etc. 
 ***********************************************************************)
let main () = begin
      let good_path_factor = ref 0.0 in 
      let generations = ref 10 in 
      let pop = ref 40 in 
      let proportional_mutation = ref 0.0 in
      let filename = ref "" in 
      let repeat_bad = ref true in 
      Random.self_init () ; 
      (* By default we use and note a new random seed each time, but the user
       * can override that if desired for reproducibility. *) 
      let seed = ref (Random.bits ()) in  
      port := 800 + (Random.int 800) ; 

      let usageMsg = "Prototype No-Specification Bug-Fixer\n" in 

      let argDescr = [
	  "--fixloc", Arg.Set fixloc, " fix localization";
	  "--mutation_max", Arg.Set_int mutation_max, "max number of mutation are allowed";
	  "--check", Arg.Set check_all, " check all the positive at last (def: false)";
	  "--faultLoc", Arg.Set faultLoc, " give the interface for fault localization";
	  "--faultpath", Arg.Set_string faultpath, " give the path name for fault localization";

	  "--seed", Arg.Set_int seed, "X use X as random seed";
	  "--gcc", Arg.Set_string gcc_cmd, "X use X to compile C files (def: 'gcc')";
	  "--ldflags", Arg.Set_string ldflags, "X use X as LDFLAGS when compiling (def: '')";
	  "--continue", Arg.Set continue, " continue after a repair is found (def: false)"; 
	  "--good", Arg.Set_string good_cmd, "X use X as good-test command (def: './test-good.sh')"; 
	  "--bad", Arg.Set_string bad_cmd, "X use X as bad-test command (def: './test-bad.sh')"; 
	  "--gen", Arg.Set_int generations, "X use X genetic algorithm generations (def: 10)";
	  "--bad_factor", Arg.Set_float bad_factor, "X multiply 'bad' testcases by X for utility (def: 10)";
	  "--good_path_factor", Arg.Set_float good_path_factor, "X multiply probabilities for statements in good path";
	  "--no_repeat_bad", Arg.Clear repeat_bad, " do not count duplicate steps on the bad path" ;
	  "--mut", Arg.Set_float mutation_chance,"X use X mutation chance (def: 0.2)"; 
	  "--xover", Arg.Set_float crossover_chance,"X use X crossover chance (def: 1.0)"; 
	  "--promut", Arg.Set_float proportional_mutation, " use proportional mutation with X expected changes (def: 0)";
	  "--pop", Arg.Set_int pop,"X use population size of X (def: 40)"; 
	  "--max", Arg.Set_int max_fitness,"X best fitness possible is X (def: 15)"; 

	  (*"--ins", Arg.Set_float ins_chance,"X relative chance of mutation insertion (def: 1.0)"; 
    "--del", Arg.Set_float del_chance,"X relative chance of mutation deletion (def: 1.0)"; 
    "--swap", Arg.Set_float swap_chance,"X relative chance of mutation swap (def: 1.0)"; *)
	  
	  "--chgNeToEq", Arg.Set_float chgNeToEq_chance,"X relative chance of mutation change Ne To Eq operator (def: 1.0)"; 
	  "--chgNeToLt", Arg.Set_float chgNeToLt_chance,"X relative chance of mutation change Ne To Lt operator (def: 1.0)"; 
	  "--chgNeToGt", Arg.Set_float chgNeToGt_chance,"X relative chance of mutation change Ne To Gt operator (def: 1.0)";
	  "--chgNeToGe", Arg.Set_float chgNeToGe_chance,"X relative chance of mutation change Ne To Ge operator (def: 1.0)"; 
	  "--chgNeToLe", Arg.Set_float chgNeToLe_chance,"X relative chance of mutation change Ne To Le operator (def: 1.0)"; 
	  (*Eq*)
	  "--chgEqToNe", Arg.Set_float chgEqToNe_chance,"X relative chance of mutation change Eq To Ne operator (def: 1.0)";  
	  "--chgEqToLe", Arg.Set_float chgEqToLe_chance,"X relative chance of mutation change Eq To Le operator (def: 1.0)";   
	  "--chgEqToGe", Arg.Set_float chgEqToGe_chance,"X relative chance of mutation change Eq To Ge operator (def: 1.0)";    
	  "--chgEqToGt", Arg.Set_float chgEqToGt_chance,"X relative chance of mutation change Eq To Gt operator (def: 1.0)";    
	  "--chgEqToLt", Arg.Set_float chgEqToLt_chance,"X relative chance of mutation change Eq To Lt operator (def: 1.0)";  
	  (*Gt*)
	  "--chgGtToEq", Arg.Set_float chgGtToEq_chance,"X relative chance of mutation change Gt To Eq operator (def: 1.0)";  
	  "--chgGtToNe", Arg.Set_float chgGtToNe_chance,"X relative chance of mutation change Gt To Ne operator (def: 1.0)";     
	  "--chgGtToLe", Arg.Set_float chgGtToLe_chance,"X relative chance of mutation change Gt To Le operator (def: 1.0)";     
	  "--chgGtToLt", Arg.Set_float chgGtToLt_chance,"X relative chance of mutation change Gt To Lt operator (def: 1.0)";     
	  "--chgGtToGe", Arg.Set_float chgGtToGe_chance,"X relative chance of mutation change Gt To Ge operator (def: 1.0)"; 
	  (*Lt*)
	  "--chgLtToEq", Arg.Set_float chgLtToEq_chance,"X relative chance of mutation change Lt To Eq operator (def: 1.0)";
	  "--chgLtToNe", Arg.Set_float chgLtToNe_chance,"X relative chance of mutation change Lt To Ne operator (def: 1.0)";
	  "--chgLtToGt", Arg.Set_float chgLtToGt_chance,"X relative chance of mutation change Lt To Gt operator (def: 1.0)"; 
	  "--chgLtToGe", Arg.Set_float chgLtToGe_chance,"X relative chance of mutation change Lt To Ge operator (def: 1.0)";
	  "--chgLtToLe", Arg.Set_float chgLtToLe_chance,"X relative chance of mutation change Lt To Le operator (def: 1.0)";
	  (*Ge*)
	  "--chgGeToEq", Arg.Set_float chgGeToEq_chance,"X relative chance of mutation change Ge To Eq operator (def: 1.0)";  
	  "--chgGeToNe", Arg.Set_float chgGeToNe_chance,"X relative chance of mutation change Ge To Ne operator (def: 1.0)";     
	  "--chgGeToLe", Arg.Set_float chgGeToLe_chance,"X relative chance of mutation change Ge To Le operator (def: 1.0)";     
	  "--chgGeToLt", Arg.Set_float chgGeToLt_chance,"X relative chance of mutation change Ge To Lt operator (def: 1.0)";     
	  "--chgGeToGt", Arg.Set_float chgGeToGt_chance,"X relative chance of mutation change Ge To Gt operator (def: 1.0)"; 
	  (*Le*)
	  "--chgLeToEq", Arg.Set_float chgLeToEq_chance,"X relative chance of mutation change Le To Eq operator (def: 1.0)";
	  "--chgLeToNe", Arg.Set_float chgLeToNe_chance,"X relative chance of mutation change Le To Ne operator (def: 1.0)";
	  "--chgLeToGt", Arg.Set_float chgLeToGt_chance,"X relative chance of mutation change Le To Gt operator (def: 1.0)"; 
	  "--chgLeToGe", Arg.Set_float chgLeToGe_chance,"X relative chance of mutation change Le To Ge operator (def: 1.0)";
	  "--chgLeToLe", Arg.Set_float chgLeToLt_chance,"X relative chance of mutation change Le To Lt operator (def: 1.0)";         
	  (*
		(*LAnd*)
		"--chgLAndToLOr", Arg.Set_float chgLAndToLOr_chance,"X relative chance of mutation change LAnd To LOr operator (def: 1.0)";  
	  "--chgLAndToBAnd", Arg.Set_float chgLAndToBAnd_chance,"X relative chance of mutation change LAnd To BAnd operator (def: 1.0)";  
	  "--chgLAndToBXor", Arg.Set_float chgLAndToBXor_chance,"X relative chance of mutation change LAnd To BXor operator (def: 1.0)";  
	  "--chgLAndToBOr", Arg.Set_float chgLAndToBOr_chance,"X relative chance of mutation change LAnd To BOr operator (def: 1.0)";  	
		(*LOr*)
		"--chgLOrToLAnd", Arg.Set_float chgLOrToLAnd_chance,"X relative chance of mutation change LOr To LAnd operator (def: 1.0)"; 
		"--chgLOrToBAnd", Arg.Set_float chgLOrToBAnd_chance,"X relative chance of mutation change LOr To BAnd operator (def: 1.0)";  
	  "--chgLOrToBXor", Arg.Set_float chgLOrToBXor_chance,"X relative chance of mutation change LOr To BXor operator (def: 1.0)";  
	  "--chgLOrToBOr", Arg.Set_float chgLOrToBOr_chance,"X relative chance of mutation change LOr To BOr operator (def: 1.0)";  *)	 
	  (*BAnd*)
	  "--chgBAndToBXor", Arg.Set_float chgBAndToBXor_chance,"X relative chance of mutation change BAnd To BXor operator (def: 1.0)";  
	  "--chgBAndToBOr", Arg.Set_float chgBAndToBOr_chance,"X relative chance of mutation change BAnd To BOr operator (def: 1.0)";  	 
	  (*BXor*)
	  "--chgBXorToBAnd", Arg.Set_float chgBXorToBAnd_chance,"X relative chance of mutation change BXor To BAnd operator (def: 1.0)";  
	  "--chgBXorToBOr", Arg.Set_float chgBXorToBOr_chance,"X relative chance of mutation change BXor To BOr operator (def: 1.0)";  	 
	  (*BOr *)
	  "--chgBOrToBAnd", Arg.Set_float chgBOrToBAnd_chance,"X relative chance of mutation change BOr To BAnd operator (def: 1.0)";  
	  "--chgBOrToBXor", Arg.Set_float chgBOrToBXor_chance,"X relative chance of mutation change BOr To BXor operator (def: 1.0)";  	 
	  (*BS*)
	  "--chgBSLtToBSRt", Arg.Set_float chgBSLtToBSRt_chance,"X relative chance of mutation change BSLt To BSRt operator (def: 1.0)";  
	  "--chgBSRtToBSLt", Arg.Set_float chgBSRtToBSLt_chance,"X relative chance of mutation change BSRt To BSLt operator (def: 1.0)";  
	  (*Plus *)
	  "--chgPlusToMinus", Arg.Set_float chgPlusToMinus_chance,"X relative chance of mutation change Plus To Minus operator (def: 1.0)";
	  "--chgPlusToMult", Arg.Set_float chgPlusToMult_chance,"X relative chance of mutation change Plus To Mult operator (def: 1.0)";
	  "--chgPlusToDiv", Arg.Set_float chgPlusToDiv_chance,"X relative chance of mutation change Plus To Div operator (def: 1.0)";
	  "--chgPlusToMod", Arg.Set_float chgPlusToMod_chance,"X relative chance of mutation change Plus To Mod operator (def: 1.0)";
	  (*Minus*)
	  "--chgMinusToPlus", Arg.Set_float chgMinusToPlus_chance,"X relative chance of mutation change Minus To Plus operator (def: 1.0)";
	  "--chgMinusToMult", Arg.Set_float chgMinusToMult_chance,"X relative chance of mutation change Minus To Mult operator (def: 1.0)";
	  "--chgMinusToDiv", Arg.Set_float chgMinusToDiv_chance,"X relative chance of mutation change Minus To Div operator (def: 1.0)";
	  "--chgMinusToMod", Arg.Set_float chgMinusToMod_chance,"X relative chance of mutation change MinusTo Mod operator (def: 1.0)";	
	  (*Mult*)
	  "--chgMultToPlus", Arg.Set_float chgMultToPlus_chance,"X relative chance of mutation change Mult To Plus operator (def: 1.0)";
	  "--chgMultToMinus", Arg.Set_float chgMultToMinus_chance,"X relative chance of mutation change Mult To Minus operator (def: 1.0)";
	  "--chgMultToDiv", Arg.Set_float chgMultToDiv_chance,"X relative chance of mutation change Mult To Div operator (def: 1.0)";
	  "--chgMultToMod", Arg.Set_float chgMultToMod_chance,"X relative chance of mutation change Mult To Mod operator (def: 1.0)";	
	  (*Div*)
	  "--chgDivToPlus", Arg.Set_float chgDivToPlus_chance,"X relative chance of mutation change Div To Plus operator (def: 1.0)";
	  "--chgDivToMinus", Arg.Set_float chgDivToMinus_chance,"X relative chance of mutation change Div To Minus operator (def: 1.0)";
	  "--chgDivToMult", Arg.Set_float chgDivToMult_chance,"X relative chance of mutation change Div To Mult operator (def: 1.0)";
	  "--chgDivToMod", Arg.Set_float chgMultToMod_chance,"X relative chance of mutation change Div To Mod operator (def: 1.0)";	
	  (*Mod*)
	  "--chgModToPlus", Arg.Set_float chgModToPlus_chance,"X relative chance of mutation change Mod To Plus operator (def: 1.0)";
	  "--chgModToMinus", Arg.Set_float chgModToMinus_chance,"X relative chance of mutation change Mod To Minus operator (def: 1.0)";
	  "--chgModToMult", Arg.Set_float chgModToMult_chance,"X relative chance of mutation change Mod To Mult operator (def: 1.0)";
	  "--chgModToDiv", Arg.Set_float chgModToDiv_chance,"X relative chance of mutation change Mod To Div operator (def: 1.0)";	    	    	  	 		
	  (*AssignToEq*)
	  "--chgAssignToEq", Arg.Set_float chgModToDiv_chance,"X relative chance of mutation change Assignment To Eq operator (def: 1.0)";
	  (*Other*)
	  "--uniqifier", Arg.Set_string input_params, "String to uniqify output best file";
	  "--tour", Arg.Set use_tournament, " use tournament selection for sampling (def: false)"; 
	  "--vn", Arg.Set_int v_debug, " X Vu's debug mode (def:" ^ (string_of_int !v_debug)^ ")"; (*v_*)
	  "--templates", Arg.Set_float template_chance, "Use templates with X probability. Default is 0." ;
	  "--random-fitness", Arg.Set random_fitness, " report random fitness values";
	  "--exit", Arg.Set exit_code, "Change the exit code based on whether we succeed (0 on success, 1 on failure). Def: false";
      ] in 
      (try
	      let fin = open_in "ldflags" in
	      ldflags := input_line fin ;
	      close_in fin ;
	  with _ -> () 
      ) ; 
      let handleArg str = filename := str in 
      Arg.parse (Arg.align argDescr) handleArg usageMsg ; 
      Cil.initCIL () ; 
      Random.init !seed ;
      let start = Unix.gettimeofday () in 
      if !filename <> "" then begin
				 (**********
				  * Main Step 1. Read in all of the data files. 
				  *) 
				 debug "modify %s\n" !filename ; 
				 let path_str = !filename ^ ".path" in 
				 let goodpath_str = !filename ^ ".goodpath" in 
				 let ht_str = !filename ^ ".ht" in 
				 let ast_str = !filename ^ ".ast" in 

				 let idfun_str = !filename ^ ".idfun" in
				 let fixfun_str = !filename ^ ".fixfun" in

				 let debug_str = !filename ^ "-" ^ !input_params ^ ".debug" in 
				 debug_out := open_out debug_str ; 
				 at_exit (fun () -> close_out !debug_out) ; 

				 let file_fin = open_in_bin ast_str in 
				 let (file : Cil.file) = Marshal.from_channel file_fin in
				 close_in file_fin ; 
				 debug "%s loaded\n" ast_str ; 
				 let ht_fin = open_in_bin ht_str in 
				 let count, ht = Marshal.from_channel ht_fin in
				 close_in ht_fin ; 
				 debug "%s loaded (%d)\n" ht_str count ; 

				 let idfun_in = open_in_bin idfun_str in (*读取idVSfun哈希表*)
				 let idfun  = Marshal.from_channel idfun_in in
				 close_in idfun_in ; 
				 debug "%s loaded\n" idfun_str ;

				 (*if !fixloc then begin *)(*这个地方是个遗憾，目前只能强制读取了,每次都需要copyyige代.fixfun文件**************************************)
    				 let fix_in = open_in_bin fixfun_str in (*读取fixloc哈希表*)
    				 let fun_id_hash_table  = Marshal.from_channel fix_in in
    				 close_in fix_in;
				 
				 if !fixloc then  
    				     debug "%s loaded\n" fixfun_str ; 


				 let path = ref [] in 
				 let path_count = ref 0.0 in
				 let gpath_any = ref false in 
				 if (not !faultLoc) then begin(*corresponding hhhhhhhhh*)
							    let gpath_ht = Hashtbl.create 255 in 

							    (try
								    let gpath_fin = open_in goodpath_str in 
								    while true do
									let line = input_line gpath_fin in
									let i = my_int_of_string line in 
									gpath_any := true ;
									Hashtbl.add gpath_ht i () 
								    done ;
								with _ -> ()
							    ) ; 

							    let path_fin = open_in path_str in 
							    let bpath_ht = Hashtbl.create 255 in 
							    (try
								    while true do
									let line = input_line path_fin in
									let i = my_int_of_string line in 
									let prob = 
									  if Hashtbl.mem gpath_ht i then
									      !good_path_factor
									  else if (not !repeat_bad) && Hashtbl.mem bpath_ht i then
									      0.0
									  else 
									      1.0
									in 
									path_count := !path_count +. prob ; 
									Hashtbl.replace bpath_ht i true ; 
									if !repeat_bad || (prob > 0.) then 
									    path := (prob, (my_int_of_string line)) :: !path 
								    done 
								with _ -> close_in path_fin) ; 
							end(*corresponding hhhhhhhhh*)
				 else begin
					 let fin = open_in !faultpath in (*打开故障定位结果文件*)
					 let space_regexp = Str.regexp "[ \t]+" in
					 (*==========================读取定位文件并构造path=======================================*) 
					 try while true do
						 let string_of_file = input_line fin in
						 if string_of_file <> "" && string_of_file.[0] <> '#' then (*允许注释和空行，但必须在此将此类行忽略*)
						     begin
							 let words = Str.split space_regexp string_of_file in (*Str.bounded_split*) (*debug "ni:%s\n" (List.nth words 0);*)
							 if ( List.length words <> 2 ) then failwith "!!!length failed"; 
							 path := ( (float_of_string (List.nth words 1)), (my_int_of_string (List.nth words 0)) ):: !path;
							 path_count := !path_count +. (float_of_string (List.nth words 1)) ;		
						     end
					     done;
					 with  x_temp -> begin
					       match x_temp with
					       | (Failure "!!!length failed") -> 
						  raise x_temp;
					       | _ -> ();
						      close_in fin;
					   end;
				     (*=================================================================*) 
				     end;
				 

				 let path = uniq(!path) in 
				 debug "sanity checking (path len %d)\n" (List.length path); 


				 let sanity_ht = Hashtbl.create 255 in
				 let sanity = new sanityVisitor file sanity_ht in 
				 visitCilFileSameGlobals sanity file ; 
				 let any = ref false in 
				 let path_temp = path in let path_sanity = ref path in
							 List.iter (fun (_,sid) ->
								    if not (Hashtbl.mem sanity_ht sid) then begin
													       debug "\tStatment %d in path but not in AST\n" sid ;
													       path_sanity := ( List.filter (fun (_,b) -> b <> sid) !path_sanity ); debug "\t\tStatment %d has been removed\n" sid ;
													   end ;
								   (*debug "****%d\n" sid;*)
								   ) path_temp ;

							 let path = !path_sanity in
							 List.iter (fun (_,sid) ->
								    if not (Hashtbl.mem sanity_ht sid) then begin
													       any := true ;
													       debug "\tStatment %d in path but not in AST\n" sid 
													   end ;
								   (*debug "****%d\n" sid;*)
								   ) path ;
							 
							 (*to debug *)
							 (*List.iter (fun (we,sid ) -> debug "%f \t %d \n" we sid
             ) path; *)
							 
							 let ordered_path = List.rev (List.sort compare_fun path) in 
							 
							 
							 (*to debug*)
							 (*debug "***************************\n " ; 
   
   List.iter (fun (we,sid ) -> debug "%f \t %d \n" we sid
             ) ordered_path ;*)
							 
							 
							 
							 if !any then begin
									 exit 1 ;
								     end ; 
							 
							 
							 let source_out = (!filename ^ "-baseline.c") in 
							 baseline_file := source_out ; 
							 let fout = open_out source_out in 
							 dumpFile noLineCilPrinter fout source_out file ;
							 close_out fout ; 
							 debug "%s written\n" source_out ; 

							 if !proportional_mutation > 0.0 then begin
												 mutation_chance := !proportional_mutation /. !path_count
											     end ; 

							 (**********
							  * Main Step 2. Write out the output. 
							  *) 
							 debug "version %s\n" version ; 
							 debug "seed %d\n" !seed ; 
							 debug "gcc %s\n" !gcc_cmd ; 
							 debug "ldflags %s\n" !ldflags ; 
							 debug "good %s\n" !good_cmd ; 
							 debug "bad %s\n" !bad_cmd ; 
							 debug "gen %d\n" !generations ; 
							 debug "mut %g\n" !mutation_chance ; 
							 debug "promut %g\n" !proportional_mutation ; 
							 debug "pop %d\n" !pop ; 
							 debug "max %d\n" !max_fitness ; 
							 (*debug "ins %g\n" !ins_chance ; 
    debug "del %g\n" !del_chance ; 
    debug "swap %g\n" !swap_chance ; *)
							 (*Ne*)
							 debug "change Ne To Eq Operator %g\n" !chgNeToEq_chance;
							 debug "change Ne To Lt Operator %g\n" !chgNeToLt_chance;
							 debug "change Ne To Gt Operator %g\n" !chgNeToGt_chance;
							 debug "change Ne To Ge Operator %g\n" !chgNeToGe_chance;
							 debug "change Ne To Le Operator %g\n" !chgNeToLe_chance;
							 (*Eq*)
							 debug "change Eq To Ne Operator %g\n" !chgEqToNe_chance;
							 debug "change Eq To Le Operator %g\n" !chgEqToLe_chance;
							 debug "change Eq To Ge Operator %g\n" !chgEqToGe_chance;
							 debug "change Eq To Gt Operator %g\n" !chgEqToGt_chance;
							 debug "change Eq To Lt Operator %g\n" !chgEqToLt_chance;
							 (*Gt*)
							 debug "change Gt To Eq Operator %g\n" !chgGtToEq_chance;
							 debug "change Gt To Ne Operator %g\n" !chgGtToNe_chance;
							 debug "change Gt To Le Operator %g\n" !chgGtToLe_chance;
							 debug "change Gt To Lt Operator %g\n" !chgGtToLt_chance;
							 debug "change Gt To Ge Operator %g\n" !chgGtToGe_chance;
							 (*Lt*)
							 debug "change Lt To Eq Operator %g\n" !chgLtToEq_chance;
							 debug "change Lt To Ne Operator %g\n" !chgLtToNe_chance;
							 debug "change Lt To Gt Operator %g\n" !chgLtToGt_chance;
							 debug "change Lt To Ge Operator %g\n" !chgLtToGe_chance;
							 debug "change Lt To Le Operator %g\n" !chgLtToLe_chance;
							 (*Ge*)
							 debug "change Ge To Eq Operator %g\n" !chgGeToEq_chance;
							 debug "change Ge To Ne Operator %g\n" !chgGeToNe_chance;
							 debug "change Ge To Le Operator %g\n" !chgGeToLe_chance;
							 debug "change Ge To Lt Operator %g\n" !chgGeToLt_chance;
							 debug "change Ge To Gt Operator %g\n" !chgGeToGt_chance;
							 (*Le*)
							 debug "change Le To Eq Operator %g\n" !chgLeToEq_chance;
							 debug "change Le To Ne Operator %g\n" !chgLeToNe_chance;
							 debug "change Le To Gt Operator %g\n" !chgLeToGt_chance;
							 debug "change Le To Ge Operator %g\n" !chgLeToGe_chance;
							 debug "change Le To Lt Operator %g\n" !chgLeToLt_chance;
							 (*
		(*LAnd *)
		debug "change LAnd To LOr Operator %g\n" !chgLAndToLOr_chance;
		debug "change LAnd To BAnd Operator %g\n" !chgLAndToBAnd_chance;
		debug "change LAnd To BXor Operator %g\n" !chgLAndToBXor_chance;
		debug "change LAnd To BOr Operator %g\n" !chgLAndToBOr_chance;
		(*LOr*)
		debug "change LOr To LAnd Operator %g\n" !chgLOrToLAnd_chance;
		debug "change LOr To BAnd Operator %g\n" !chgLOrToBAnd_chance;
		debug "change LOr To BXor Operator %g\n" !chgLOrToBXor_chance;
		debug "change LOr To BOr Operator %g\n" !chgLOrToBOr_chance; *)
							 (*BAnd*)
							 debug "change BAnd To BXor Operator %g\n" !chgBAndToBXor_chance;
							 debug "change BAnd To BOr Operator %g\n" !chgBAndToBOr_chance;
							 (*BXor *)
							 debug "change BXor To BAnd Operator %g\n" !chgBXorToBAnd_chance;
							 debug "change BXor To BOr Operator %g\n" !chgBXorToBOr_chance;
							 (*BOr *)
							 debug "change BOr To BAnd Operator %g\n" !chgBOrToBAnd_chance;
							 debug "change BOr To BXor Operator %g\n" !chgBOrToBXor_chance;
							 (*BS*)
							 debug "change BSLt To BSRt Operator %g\n" !chgBSLtToBSRt_chance;
							 debug "change BSRt To BSLt Operator %g\n" !chgBSRtToBSLt_chance;
							 (*arthimatic ops *)
							 (*Plus*)
							 debug "change Plus To Minus Operator %g\n" !chgPlusToMinus_chance;
							 debug "change Plus To Mult Operator %g\n" !chgPlusToMult_chance;
							 debug "change Plus To Div Operator %g\n" !chgPlusToDiv_chance;
							 debug "change Plus To Mod Operator %g\n" !chgPlusToMod_chance;
							 (*Minus*)
							 debug "change Minus To Plus Operator %g\n" !chgMinusToPlus_chance;
							 debug "change Minus To Mult Operator %g\n" !chgMinusToMult_chance;
							 debug "change Minus To Div Operator %g\n" !chgMinusToDiv_chance;
							 debug "change Minus To Mod Operator %g\n" !chgMinusToMod_chance;
							 (*Mult*)
							 debug "change Mult To Plus Operator %g\n" !chgMultToPlus_chance;
							 debug "change Mult To Minus Operator %g\n" !chgMultToMinus_chance;
							 debug "change Mult To Div Operator %g\n" !chgMultToDiv_chance;
							 debug "change Mult To Mod Operator %g\n" !chgMultToMod_chance;
							 (*Div*)
							 debug "change Div To Plus Operator %g\n" !chgDivToPlus_chance;
							 debug "change Div To Minus Operator %g\n" !chgDivToMinus_chance;
							 debug "change Div To Mult Operator %g\n" !chgDivToMult_chance;
							 debug "change Div To Mod Operator %g\n" !chgDivToMod_chance;
							 (*Mod*)
							 debug "change Mod To Plus Operator %g\n" !chgModToPlus_chance;
							 debug "change Mod To Minus Operator %g\n" !chgModToMinus_chance;
							 debug "change Mod To Mult Operator %g\n" !chgModToMult_chance;
							 debug "change Mod To Div Operator %g\n" !chgModToDiv_chance;
							 (*Assign*)
							 debug "change Assign To Eq Operator %g\n" !chgAssignToEq_chance;
							 (*Others *)
							 debug "compile_counter %d\n" !compile_counter ; 
							 debug "fitness_count %d\n" !fitness_count ; 
							 debug "bad_factor %g\n" !bad_factor ; 
							 debug "good_path_factor %g\n" !good_path_factor ; 
							 debug "gpath_any %b\n" !gpath_any ; 
							 debug "path_count %g\n" !path_count ; 
							 debug "use_tournament %b\n" !use_tournament ; 
							 debug "tournament_k %d\n" !tournament_k ; 
							 debug "tournament_p %g\n" !tournament_p ; 

							 (**********
							  * Main Step 3. Do the genetic programming. 
							  *) 
							 let to_print_best_output () =

							   let printstats name total denom =
							     let denom = float denom in 
							     (*let i = float total.ins in 
        let d = float total.del in 
        let s = float total.swap in *)
							     let oNeToEq = float total.chgNeToEq in 
							     let oNeToLt = float total.chgNeToLt in 
							     let oNeToGt = float total.chgNeToGt in 
							     let oNeToGe = float total.chgNeToGe in 
							     let oNeToLe = float total.chgNeToLe in 
							     (* Eq *)
							     let oEqToNe = float total.chgEqToNe in 
							     let oEqToLe = float total.chgEqToLe in
							     let oEqToGe = float total.chgEqToGe in
							     let oEqToGt = float total.chgEqToGt in
							     let oEqToLt = float total.chgEqToLt in
							     (* Gt *)
							     let oGtToEq = float total.chgGtToEq in
							     let oGtToNe = float total.chgGtToNe in
							     let oGtToLe = float total.chgGtToLe in
							     let oGtToLt = float total.chgGtToLt in
							     let oGtToGe = float total.chgGtToGe in
							     (* Lt *)
							     let oLtToEq = float total.chgLtToEq in
							     let oLtToNe = float total.chgLtToNe in
							     let oLtToGt = float total.chgLtToGt in
							     let oLtToGe = float total.chgLtToGe in
							     let oLtToLe = float total.chgLtToLe in
							     (* Ge *)
							     let oGeToEq = float total.chgGeToEq in
							     let oGeToNe = float total.chgGeToNe in
							     let oGeToLe = float total.chgGeToLe in
							     let oGeToLt = float total.chgGeToLt in
							     let oGeToGt = float total.chgGeToGt in
							     (* Le *)
							     let oLeToEq = float total.chgLeToEq in
							     let oLeToNe = float total.chgLeToNe in
							     let oLeToGt = float total.chgLeToGt in
							     let oLeToGe = float total.chgLeToGe in
							     let oLeToLt = float total.chgLeToLt in
							     (*
				(*LAnd *)
				let oLAndToLOr = float total.chgLAndToLOr in
				let oLAndToBAnd = float total.chgLAndToBAnd in
				let oLAndToBXor = float total.chgLAndToBXor in
				let oLAndToBOr = float total.chgLAndToBOr in
				(*LOr *)
				let oLOrToLAnd = float total.chgLOrToLAnd in
				let oLOrToBAnd = float total.chgLOrToBAnd in
				let oLOrToBXor = float total.chgLOrToBXor in
				let oLOrToBOr = float total.chgLOrToBOr in *)
							     (*BAnd*)
							     let oBAndToBXor = float total.chgBAndToBXor in
							     let oBAndToBOr = float total.chgBAndToBOr in
							     (*BXor*)
							     let oBXorToBAnd = float total.chgBXorToBAnd in
							     let oBXorToBOr = float total.chgBXorToBOr in
							     (*BOr*)
							     let oBOrToBAnd = float total.chgBOrToBAnd in
							     let oBOrToBXor = float total.chgBOrToBXor in
							     (*BS*)
							     let oBSLtToBSRt = float total.chgBSLtToBSRt in
							     let oBSRtToBSLt = float total.chgBSRtToBSLt in
							     (*PlusA*)
							     let oPlusToMinus = float total.chgPlusToMinus in
							     let oPlusToMult = float total.chgPlusToMult in
							     let oPlusToDiv = float total.chgPlusToDiv in
							     let oPlusToMod = float total.chgPlusToMod in
							     (*MinusA*)
							     let oMinusToPlus = float total.chgMinusToPlus in
							     let oMinusToMult = float total.chgMinusToMult in
							     let oMinusToDiv = float total.chgMinusToDiv in
							     let oMinusToMod = float total.chgMinusToMod in
							     (*Mult*)
							     let oMultToPlus = float total.chgMultToPlus in
							     let oMultToMinus = float total.chgMultToMinus in
							     let oMultToDiv = float total.chgMultToDiv in
							     let oMultToMod = float total.chgMultToMod in
							     (*Div*)
							     let oDivToPlus = float total.chgDivToPlus in
							     let oDivToMinus = float total.chgDivToMinus in
							     let oDivToMult = float total.chgDivToMult in
							     let oDivToMod = float total.chgDivToMod in
							     (*Mod*)
							     let oModToPlus = float total.chgModToPlus in
							     let oModToMinus = float total.chgModToMinus in
							     let oModToMult = float total.chgModToMult in
							     let oModToDiv = float total.chgModToDiv in
							     (*Assign*)
							     let oAssignToEq = float total.chgAssignToEq in
							     (* Others *)
							     
							     let x = float total.xover in 
							     let xs = float total.xswap in 
							     let m = float total.mut in 
							     (*debug "%s inserts:     %g/%g = %g\n" name i denom (i /. denom) ; 
        debug "%s deletes:     %g/%g = %g\n" name d denom (d /. denom) ; 
        debug "%s mut swaps:   %g/%g = %g\n" name s denom (s /. denom) ; *)
							     (* Ne *)
							     debug "%s chg Ne To Eq :   %g/%g = %g\n" name oNeToEq denom (oNeToEq /. denom) ; 
							     debug "%s chg Ne To Lt :   %g/%g = %g\n" name oNeToLt denom (oNeToLt /. denom) ; 
							     debug "%s chg Ne To Gt :   %g/%g = %g\n" name oNeToGt denom (oNeToGt /. denom) ; 
							     debug "%s chg Ne To Ge :   %g/%g = %g\n" name oNeToGe denom (oNeToGe /. denom) ; 
							     debug "%s chg Ne To Le :   %g/%g = %g\n" name oNeToLe denom (oNeToLe /. denom) ; 
							     (* Eq *)
							     debug "%s chg Eq To Ne :   %g/%g = %g\n" name oEqToNe denom (oEqToNe /. denom) ; 
							     debug "%s chg Eq To Le :   %g/%g = %g\n" name oEqToLe denom (oEqToLe /. denom) ; 
							     debug "%s chg Eq To Ge :   %g/%g = %g\n" name oEqToGe denom (oEqToGe /. denom) ; 
							     debug "%s chg Eq To Gt :   %g/%g = %g\n" name oEqToGt denom (oEqToGt /. denom) ; 
							     debug "%s chg Eq To Lt :   %g/%g = %g\n" name oEqToLt denom (oEqToLt /. denom) ; 
							     (* Gt *)
							     debug "%s chg Gt To Eq :   %g/%g = %g\n" name oGtToEq denom (oGtToEq /. denom) ; 
							     debug "%s chg Gt To Ne :   %g/%g = %g\n" name oGtToNe denom (oGtToNe /. denom) ; 
							     debug "%s chg Gt To Le :   %g/%g = %g\n" name oGtToLe denom (oGtToLe /. denom) ; 
							     debug "%s chg Gt To Lt :   %g/%g = %g\n" name oGtToLt denom (oGtToLt /. denom) ; 
							     debug "%s chg Gt To Ge :   %g/%g = %g\n" name oGtToGe denom (oGtToGe /. denom) ; 
							     (* Lt *)
							     debug "%s chg Lt To Eq :   %g/%g = %g\n" name oLtToEq denom (oLtToEq /. denom) ; 
							     debug "%s chg Lt To Ne :   %g/%g = %g\n" name oLtToNe denom (oLtToNe /. denom) ; 
							     debug "%s chg Lt To Gt :   %g/%g = %g\n" name oLtToGt denom (oLtToGt /. denom) ; 
							     debug "%s chg Lt To Ge :   %g/%g = %g\n" name oLtToGe denom (oLtToGe /. denom) ; 
							     debug "%s chg Lt To Le :   %g/%g = %g\n" name oLtToLe denom (oLtToLe /. denom) ; 
							     (* Ge *)
							     debug "%s chg Ge To Eq :   %g/%g = %g\n" name oGeToEq denom (oGeToEq /. denom) ; 
							     debug "%s chg Ge To Ne :   %g/%g = %g\n" name oGeToNe denom (oGeToNe /. denom) ; 
							     debug "%s chg Ge To Le :   %g/%g = %g\n" name oGeToLe denom (oGeToLe /. denom) ; 
							     debug "%s chg Ge To Lt :   %g/%g = %g\n" name oGeToLt denom (oGeToLt /. denom) ; 
							     debug "%s chg Ge To Gt :   %g/%g = %g\n" name oGeToGt denom (oGeToGt /. denom) ; 
							     (* Le *)
							     debug "%s chg Le To Eq :   %g/%g = %g\n" name oLeToEq denom (oLeToEq /. denom) ; 
							     debug "%s chg Le To Ne :   %g/%g = %g\n" name oLeToNe denom (oLeToNe /. denom) ; 
							     debug "%s chg Le To Gt :   %g/%g = %g\n" name oLeToGt denom (oLeToGt /. denom) ; 
							     debug "%s chg Le To Ge :   %g/%g = %g\n" name oLeToGe denom (oLeToGe /. denom) ; 
							     debug "%s chg Le To Le :   %g/%g = %g\n" name oLeToLt denom (oLeToLt /. denom) ; 
							     (*
				(*LAnd*)
				debug "%s chg LAnd To LOr :   %g/%g = %g\n" name oLAndToLOr denom (oLAndToLOr /. denom) ; 
				debug "%s chg LAnd To BAnd :   %g/%g = %g\n" name oLAndToBAnd denom (oLAndToBAnd /. denom) ; 
				debug "%s chg LAnd To BXor :   %g/%g = %g\n" name oLAndToBXor denom (oLAndToBXor /. denom) ; 
			  debug "%s chg LAnd To BOr :   %g/%g = %g\n" name oLAndToBOr denom (oLAndToBOr /. denom) ; 
				(*LOr *)
				debug "%s chg LOr To LAnd :   %g/%g = %g\n" name oLOrToLAnd denom (oLOrToLAnd /. denom) ; 
				debug "%s chg LOr To BAnd :   %g/%g = %g\n" name oLOrToBAnd denom (oLOrToBAnd /. denom) ; 
				debug "%s chg LOr To BXor :   %g/%g = %g\n" name oLOrToBXor denom (oLOrToBXor /. denom) ; 
			  debug "%s chg LOr To BOr :   %g/%g = %g\n" name oLOrToBOr denom (oLOrToBOr /. denom) ; *)
							     (*BAnd*)
							     debug "%s chg BAnd To BXor :   %g/%g = %g\n" name oBAndToBXor denom (oBAndToBXor /. denom) ; 
							     debug "%s chg BAnd To BOr :   %g/%g = %g\n" name oBAndToBOr denom (oBAndToBOr /. denom) ; 
							     (*BXor*)
							     debug "%s chg BXor To BAnd :   %g/%g = %g\n" name oBXorToBAnd denom (oBXorToBAnd /. denom) ; 
							     debug "%s chg BXor To BOr :   %g/%g = %g\n" name oBXorToBOr denom (oBXorToBOr /. denom) ; 
							     (*BOr*)
       							     debug "%s chg BOr To BAnd :   %g/%g = %g\n" name oBOrToBAnd denom (oBOrToBAnd /. denom) ; 
							     debug "%s chg BOr To BXor :   %g/%g = %g\n" name oBOrToBXor denom (oBOrToBXor /. denom) ; 
							     (*BS*)
							     debug "%s chg BSLt To BSRt :   %g/%g = %g\n" name oBSLtToBSRt denom (oBSLtToBSRt /. denom) ; 
							     debug "%s chg BSRt To BSLt :   %g/%g = %g\n" name oBSRtToBSLt denom (oBSRtToBSLt /. denom) ; 
							     (*PlusA *)
							     debug "%s chg Plus To Minus :   %g/%g = %g\n" name oPlusToMinus denom (oPlusToMinus /. denom) ; 
							     debug "%s chg Plus To Mult :   %g/%g = %g\n" name oPlusToMult denom (oPlusToMult /. denom) ; 
							     debug "%s chg Plus To Div :   %g/%g = %g\n" name oPlusToDiv denom (oPlusToDiv /. denom) ; 
							     debug "%s chg Plus To Mod :   %g/%g = %g\n" name oPlusToMod denom (oPlusToMod /. denom) ; 
							     (*MinusA *)
							     debug "%s chg Minus To Plus :   %g/%g = %g\n" name oMinusToPlus denom (oMinusToPlus /. denom) ; 
							     debug "%s chg Minus To Mult :   %g/%g = %g\n" name oMinusToMult denom (oMinusToMult /. denom) ; 
							     debug "%s chg Minus To Div :   %g/%g = %g\n" name oMinusToDiv denom (oMinusToDiv /. denom) ; 
							     debug "%s chg Minus To Mod :   %g/%g = %g\n" name oMinusToMod denom (oMinusToMod /. denom) ; 
							     (*Mult *)
							     debug "%s chg Mult To Plus :   %g/%g = %g\n" name oMultToPlus denom (oMultToPlus /. denom) ; 
							     debug "%s chg Mult To Minus :   %g/%g = %g\n" name oMultToMinus denom (oMultToMinus /. denom) ; 
							     debug "%s chg Mult To Div :   %g/%g = %g\n" name oMultToDiv denom (oMultToDiv /. denom) ; 
							     debug "%s chg Mult To Mod :   %g/%g = %g\n" name oMultToMod denom (oMultToMod /. denom) ; 
							     (*Div *)
							     debug "%s chg Div To Plus :   %g/%g = %g\n" name oDivToPlus denom (oDivToPlus /. denom) ; 
							     debug "%s chg Div To Minus :   %g/%g = %g\n" name oDivToMinus denom (oDivToMinus /. denom) ; 
							     debug "%s chg Div To Mult :   %g/%g = %g\n" name oDivToMult denom (oDivToMult /. denom) ; 
							     debug "%s chg Div To Mod :   %g/%g = %g\n" name oDivToMod denom (oDivToMod /. denom) ; 
							     (*Mod *)
							     debug "%s chg Mod To Plus :   %g/%g = %g\n" name oModToPlus denom (oModToPlus /. denom) ; 
							     debug "%s chg Mod To Minus :   %g/%g = %g\n" name oModToMinus denom (oModToMinus /. denom) ; 
							     debug "%s chg Mod To Mult :   %g/%g = %g\n" name oModToMult denom (oModToMult /. denom) ; 
							     debug "%s chg Mod To Div :   %g/%g = %g\n" name oModToDiv denom (oModToDiv /. denom) ; 
							     (*Assign*)
							     debug "%s chg Assign To Eq :   %g/%g = %g\n" name oAssignToEq denom (oAssignToEq /. denom) ; 
							     (*Other *)
							     debug "%s xovers:      %g/%g = %g\n" name x denom (x /. denom) ; 
							     debug "%s xover swaps: %g/%g = %g\n" name xs denom (xs /. denom) ; 
							     debug "%s macromuts:   %g/%g = %g\n" name m denom (m /. denom) ; 
							   in 

							   (match !most_fit with
							    | None -> debug "\n\nNo adequate program found.\n" 
							    | Some(best_size, best_fitness, best_file, tau, best_count, tracking) -> begin
																       (*v_*)
																       debug "v_gen %d\n" (List.length !v_avg_fit_l);
																       debug "avgfit : "; List.iter(fun e -> debug "%g " e)(List.rev !v_avg_fit_l);debug "\n";
																       debug "bcfit : "; List.iter(fun e -> debug "%g " e)(List.rev !v_bc_fit_l);debug "\n";
																       flush !debug_out ;
																       (*v_*)

																       let source_out = (!filename ^ "-" ^ !input_params ^ "-best.c") in 
																       let fout = open_out source_out in 
																       dumpFile noLineCilPrinter fout source_out best_file ;
																       close_out fout ; 
																       debug "\n\nBest result written to %s\n" source_out ; 
																       debug "\tFirst Solution in %g (%d fitness evals)\n" 
																	     (!first_solution_at -. start) 
																	     !first_solution_count ; 
																       debug "\tBest  Solution in %g (%d fitness evals)\n\n" (tau -. start) 
																	     best_count; 

																       printstats "initial repair" tracking 1 ; 

																   end) ;


							   printstats "per-fitness average" !total_avg !total_fitness_evals ; 
							   printstats "per-nonzero-noncached-fitness average" !nonzerofitness_avg 
								      !total_nonzerofitness_evals ; 
							   (*debug "Generations to solution: %d\n" !gen_num;*)
							   debug "total number of MACROmutation operators: %d\n" !total_number_of_macromutations ; 
							   debug "total number of micromutation operators: %d\n" !total_number_of_micromutations ; 
							   debug "average micromutation per macromutation: %g\n"
								 ((float !total_number_of_micromutations) /. 
								      (float !total_number_of_macromutations)) ; 

							   let comp_fail = ((Int32.to_float (Int32.of_int !compile_fail)) /. (Int32.to_float (Int32.of_int !compile_tried))) in
							   let comp_fail2 = ((Int32.to_float (Int32.of_int !compile_fail)) /. (Int32.to_float (Int32.of_int !total_fitness_evals))) in
							   debug "Percent of unique variants that failed to compile: %d/%d = %g\n" 
								 !compile_fail !compile_tried comp_fail; 
							   debug "Percent possibly-cached fitness evals that failed to compile: %d/%d = %g\n" 
								 !compile_fail !total_fitness_evals comp_fail2; 
							   flush !debug_out ;
							   if !exit_code then begin
										 (match !most_fit with
										  | None -> exit 1
										  | Some(_) -> exit 0);
									     end
							 in 
							 print_best_output := to_print_best_output ;

							 brute_force (file,ht,count,ordered_path,new_tracking (),idfun,fun_id_hash_table); 
							 
							 (* WRW: ga *does not return* *) 
							 !print_best_output () ; 

			     end ;
      Stats2.print stdout "Genetic Programming Prototype" ; 
      Stats2.print !debug_out "Genetic Programming Prototype" ; 
  end ;;

    main () ;; 
