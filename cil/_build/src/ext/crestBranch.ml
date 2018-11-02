(* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
*
* This file is part of CREST, which is distributed under the revised
* BSD license.  A copy of this license can be found in the file LICENSE.
*
* This program is distributed in the hope that it will be useful, but
* WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
* for details.
*)

open Cil

(*
 * Utilities that should be in the O'Caml standard libraries.
 *)


let worldSizeLimit = 16

let isSome o =
	match o with
	| Some _ -> true
	| None   -> false



(* hComment: remove the none *)
let rec mapOptional f ls =
	match ls with
	| [] -> []
	| (x::xs) -> (match (f x) with
			| None -> mapOptional f xs
			| Some x' -> x' :: mapOptional f xs)



let concatMap f ls =
	let rec doIt res ls =
		match ls with
			| [] -> List.rev res
			| (x::xs) -> doIt (List.rev_append (f x) res) xs
		in
	doIt [] ls



let open_append fname =
	open_out_gen [Open_append; Open_creat; Open_text] 0o700 fname


(*
 * We maintain several bits of state while instrumenting a program:
 *  - the last id assigned to an instrumentation call
 *    (equal to the number of such inserted calls)
 *  - the last id assigned to a statement in the program
 *    (equal to the number of CFG-transformed statements)
 *  - the last id assigned to a function
 *  - the set of all branches seen so far (stored as pairs of branch
	 *    id's -- with paired true and false branches stored together),
 *    annotating branches with the funcion they are in
 *  - a per-function control-flow graph (CFG), along with all calls
 *    between functions
 *  - a map from function names to the first statement ID in the function
 *    (to build the complete CFG once all files have been processed)
 *
 * Because the CIL executable will be run once per source file in the
 * instrumented program, we must save/restore this state in files
 * between CIL executions.  (These last two bits of state are
	 * write-only -- at the end of each run we just append updates.)
 *)

let idCount = ref 0
let stmtCount = Cfg.start_id
let funCount = ref 0
let branches = ref []
let curBranches = ref []
(* Control-flow graph is stored inside the CIL AST. *)

let getNewId () = ((idCount := !idCount + 1); !idCount)
(* hComment: bp is a 2-tuple, i.e., a pair *)
let addBranchPair bp = (curBranches := bp :: !curBranches)
let addFunction () = (branches := (!funCount, !curBranches) :: !branches;
curBranches := [];
funCount := !funCount + 1)

let readCounter fname =
	try
		let f = open_in fname in
		Scanf.fscanf f "%d" (fun x -> x)
	with x -> 0

let writeCounter fname (cnt : int) =
	try
		let f = open_out fname in
		Printf.fprintf f "%d\n" cnt ;
		close_out f
	with x ->
		failwith ("Failed to write counter to: " ^ fname ^ "\n")

let readIdCount () = (idCount := readCounter "idcount")
let readStmtCount () = (stmtCount := readCounter "stmtcount")
let readFunCount () = (funCount := readCounter "funcount")

let writeIdCount () = writeCounter "idcount" !idCount
let writeStmtCount () = writeCounter "stmtcount" !stmtCount
let writeFunCount () = writeCounter "funcount" !funCount

let writeBranches () =
let writeFunBranches out (fid, bs) =
	if (fid > 0) then
	(let sorted = List.sort compare bs in
	Printf.fprintf out "%d %d\n" fid (List.length bs) ;
	List.iter (fun (s,d) -> Printf.fprintf out "%d %d\n" s d) sorted)
in
try
	let f = open_append "branches" in
	let allBranches = (!funCount, !curBranches) :: !branches in
	List.iter (writeFunBranches f) (List.tl (List.rev allBranches));
	close_out f
with x ->
	prerr_string "Failed to write branches.\n"




(* Visitor which walks the CIL AST, printing the (already computed) CFG. *)
class writeCfgVisitor out firstStmtIdMap =
	object (self)
	inherit nopCilVisitor
	val out = out
	val firstStmtIdMap = firstStmtIdMap

	(* write down the first statement's id if the function is in the list; *)
	(* otherwise, write down the function name *)
	method writeCfgCall f =
		(* hComment: List.mem_assq compares the two iterm based on physical *)
		(* equality, i.e., the address equality *)
		if List.mem_assq f firstStmtIdMap then
			(* hComment: sid, the unique number of the statement *)
			Printf.fprintf out " %d" (List.assq f firstStmtIdMap).sid
		else
			Printf.fprintf out " %s" f.vname


	(* find out all the instructions involving function calls and then call *)
	(* writeCfgCall for them *)
	method writeCfgInst i =
		match i with
			(* hComment: this instruction is of type Call. We need to get the *)
			(* function information, i.e., f *)
			Call(_, Lval(Var f, _), _, _) -> self#writeCfgCall f
			(* hComment: ignore it if it is not a function call *)
			| _ -> ()

	(* hComment: *)
	method vstmt(s) =
		Printf.fprintf out "%d" s.sid ;
		List.iter (fun dst -> Printf.fprintf out " %d" dst.sid) s.succs ;
		(match s.skind with
			 Instr is -> List.iter self#writeCfgInst is
			 | _       -> ()) ;
		output_string out "\n" ;
		DoChildren

end





let writeCfg cilFile firstStmtIdMap =
	try
		let out = open_append "cfg" in
		let wcfgv = new writeCfgVisitor out firstStmtIdMap in
		visitCilFileSameGlobals (wcfgv :> cilVisitor) cilFile ;
		close_out out
	with x ->
		prerr_string "Failed to write CFG.\n"





(* hComment: find the first statement for all functions in the file *)
let buildFirstStmtIdMap cilFile =
	let getFirstFuncStmtId glob =
	match glob with
		(* hComment: f.svar, the function's information; List.hd, lists *)
		(* the first element of a list; f.sbody, bstmts, the list of *)
		(* instructions in the function body *)
		| GFun(f, _) -> Some (f.svar, List.hd f.sbody.bstmts)
		(* this is not a function *)
		| _ -> None
	in
	(* hComment: iterate all the functions' globals so as to find the *)
	(* first statement for each function *)
	mapOptional getFirstFuncStmtId cilFile.globals




let writeFirstStmtIdMap firstStmtIdMap =
	let writeEntry out (f,s) =
		(* To help avoid "collisions", skip static functions. *)
		if not (f.vstorage = Static) then
			Printf.fprintf out "%s %d\n" f.vname s.sid
	in
	try
		let out = open_append "cfg_func_map" in
		List.iter (writeEntry out) firstStmtIdMap ;
		close_out out
	with x ->
		prerr_string "Failed to write (function, first statement ID) map.\n"





let handleCallEdgesAndWriteCfg cilFile =
	let stmtMap = buildFirstStmtIdMap cilFile in
	(* hComment: write down the CFG *)
	writeCfg cilFile stmtMap ;
	(* *)
	writeFirstStmtIdMap stmtMap





(* Utilities *)

let noAddr = zero

let shouldSkipFunction f = hasAttribute "crest_skip" f.vattr

(* hComment: insert the instruction list before the code block *)
let prependToBlock (is : instr list) (b : block) =
b.bstmts <- mkStmt (Instr is) :: b.bstmts

let isSymbolicType ty = isIntegralType (unrollType ty)


(* These definitions must match those in "libcrest/crest.h". *)
let limitType = intType
let idType   = intType
let bidType  = intType
let fidType  = uintType
let valType  = TInt (ILongLong, [])
let addrType = TInt (IULong, [])
let boolType = TInt (IUChar, [])
let opType   = intType  (* enum *)


(*
 * normalizeConditionalsVisitor ensures that every if block has an
 * accompanying else block (by adding empty "else { }" blocks where
	 * necessary).  It also attempts to convert conditional expressions
 * into predicates (i.e. binary expressions with one of the comparison
	 * operators ==, !=, >, <, >=, <=.)
 *)
class normalizeConditionalsVisitor =

	let isCompareOp op =
		match op with
			| Eq -> true  | Ne -> true  | Lt -> true
			| Gt -> true  | Le -> true  | Ge -> true
			| _ -> false
	in

	let negateCompareOp op =
		match op with
			| Eq -> Ne  | Ne -> Eq
			| Lt -> Ge  | Ge -> Lt
			| Le -> Gt  | Gt -> Le
			| _ ->
            invalid_arg "negateCompareOp"
	in

	(* hComment: transform conditional expressions into predicates *) 
	(**)
	(* TODO(jburnim): We ignore casts here because downcasting can
	 * convert a non-zero value into a zero -- e.g. from a larger to a
	 * smaller integral type.  However, we could safely handle casting
	 * from smaller to larger integral types. *)
	let rec mkPredicate e negated =
        match e with
            (* hComment: if(!x) --> if (x=0), i.e., recursion used to use *)
            (* the first match and then the third match *)
            | UnOp (LNot, e, _) -> mkPredicate e (not negated)
            (* hComment: the predicate would be the same to the expression *)
            (* if it is binary operation *)
            | BinOp (op, e1, e2, ty) when isCompareOp op ->
                if negated then
                       BinOp (negateCompareOp op, e1, e2, ty)
                else
                    e
            (* this match works together with the first match *)
            | _ ->
                let op = if negated then Eq else Ne in
                      BinOp (op, e, zero, intType)
	in

	(* hComment: this class is a subtype of nopCilVisitor *)
	object (self)
	inherit nopCilVisitor


	(* hComment: parameter s denotes a CONTROL-FLOW statement in the program *)
	method vstmt(s) =
		(* hComment: s.skind denotes the type of this statement *)
		match s.skind with
			(* hComment: this is a IF statement *)
			| If (e, b1, b2, loc) ->
				(* Ensure neither branch is empty. *)
				if (b1.bstmts == []) then b1.bstmts <- [mkEmptyStmt ()] ;
				if (b2.bstmts == []) then b2.bstmts <- [mkEmptyStmt ()] ;
				(* Ensure the conditional is actually a predicate. *)
				s.skind <- If (mkPredicate e false, b1, b2, loc) ;
				DoChildren
			(* hComment: anything else, e.g., goto *)
			| _ -> DoChildren
end


(* hComment: get the address of a left value *)
let addressOf : lval -> exp = mkAddrOrStartOf


(* hComment: what is this? *)
let hasAddress (_, off) =
	let rec containsBitField off =
		match off with
			| NoOffset         -> false
			| Field (fi, off) -> (isSome fi.fbitfield) || (containsBitField off)
			| Index (_, off)  -> containsBitField off
		in
	not (containsBitField off)





class crestInstrumentVisitor f =
	(*
	 * Get handles to the instrumentation functions.
	 *
	 * NOTE: If the file we are instrumenting includes "crest.h", this
	 * code will grab the varinfo's from the included declarations.
	 * Otherwise, it will create declarations for these functions.
	 *)
	let limitArg  = ("limit",  limitType,  []) in
	let bidArg  = ("bid",  bidType,  []) in
	let addrArg = ("addr", addrType, []) in
	let valArg  = ("val",  valType,  []) in
	
	let toAddr e = CastE (addrType, e) in
	
	let toValue e =
		if isPointerType (typeOf e) then
		CastE (valType, CastE (addrType, e))
		else
		CastE (valType, e)
	in
	
	(* hEdit: Create function definition *)
	let mkInstFunc_ name args =
		let ty = TFun (voidType, Some (args), false, []) in
		let func = findOrCreateFunc f ("__Crest" ^ name) ty in
		func.vstorage <- Extern ;
		func.vattr <- [Attr ("crest_skip", [])] ;
		func
	in

	(* hEdit: add a new branch function *)
	let branchFuncOnly   = mkInstFunc_ "BranchOnly" [bidArg] in
	(* hEdit: add a new function that marks MPI_rank in MPI_COMM_WORLD *)
	let rankFunc   = mkInstFunc_ "Rank" [addrArg] in
	(* hEdit: add a new function that marks MPI_rank in non-default comm *)
	let rankFuncNonDefaultComm1   = mkInstFunc_ "RankNonDefaultComm1" [addrArg] in
	let rankFuncNonDefaultComm2   = mkInstFunc_ "RankNonDefaultComm2" [valArg; addrArg] in
	(* hEdit: add a new function that marks MPI_COMM_WORLD's size in MPI_COMM_WORLD *)
	let worldSizeFunc   = mkInstFunc_ "WorldSizeWithLimit" [addrArg; limitArg] in
	(* hEdit: add a *)
	let getMPIInfo	     = mkInstFunc_ "GetMPIInfo" [] in
	(*
	 * Functions to create calls to the above instrumentation functions.
	 *)
	let mkInstCall_ func args =
		Call (None, Lval (var func), args, locUnknown)
	in

	let mkBranchOnly bid     = mkInstCall_ branchFuncOnly [integer bid] in
	let mkRank addr     = mkInstCall_ rankFunc [toAddr addr] in
	let mkRankNonDefaultComm1 addr     = mkInstCall_ rankFuncNonDefaultComm1 [toAddr addr] in
        let mkRankNonDefaultComm2 value addr     = mkInstCall_ rankFuncNonDefaultComm2 [toValue value; toAddr addr] in

	let mkWorldSize addr limit     = mkInstCall_ worldSizeFunc [toAddr addr; integer limit] in
	let mkGetMPIInfo ()      = mkInstCall_ getMPIInfo [] in

	(* hEdit: print the list of arguments. This is used for debugging purpose*) 
	let rec printArgList argList = 
		match argList with
		| [] -> ()
		| first::remains -> 
			match first with 
			| Lval(Var a, NoOffset) ->
				print_string "\nLval\n";
				print_string a.vname;
				printArgList remains;
			| AddrOf((Var a, NoOffset)) ->
				print_string "\nAddrOf\n";
				print_string a.vname;
				printArgList remains;
			| CastE(_, Lval(Var a, NoOffset)) ->
				print_string "\nCastE\n";
				print_string a.vname;
				printArgList remains;
				();
			| _ ->
				print_string "\nno matching!\n";
				printArgList remains;
				();
	in
	
    let rankMarker g i =
        match g with
            | [] -> [];
            | h::j when (isConstant h) ->
                (
                match j with
                    | [] -> [];
                    | k::_ -> 
                        (
                        match k with 
                            | Lval(_, _) ->
                                    [mkRank k; i]; 
                            | CastE(_, _) ->
                                    [mkRank k; i]; 
                            | AddrOf(a) ->
                                    (* miss the bracket cause the bug for addressOf*)
                                    [mkRank (addressOf a); i]; 
                            | _ -> [];
                        )
                )
            
            | h::j ->
                (
                match j with
                    | [] -> [];
                    | k::_ -> 
                        (
                        match k with 
                            | Lval(_, _) ->
                                [mkRankNonDefaultComm1 k; i; mkRankNonDefaultComm2 h k]; 
                            | CastE(_, _) ->
                                [mkRankNonDefaultComm1 k; i; mkRankNonDefaultComm2 h k]; 
                            | AddrOf(a) ->
                                (* miss the bracket cause the bug for addressOf*)
                                [mkRankNonDefaultComm1 k; i; mkRankNonDefaultComm2 h (addressOf a)]; 
                            | _ -> [];
                        )
                )
            
            | _ -> [];
    in

	let worldSizeMarker g = 
		match g with 
			| [] -> [];
			| h::j when (isConstant h) ->
				(
				match j with
					| [] -> [];
					| k::_ -> 
						(
						match k with 
							| Lval(_, _) ->
								[mkWorldSize k worldSizeLimit]; 
							| CastE(_, _) ->
								[mkWorldSize k worldSizeLimit]; 
							| AddrOf(a) ->
								(* miss the bracket cause the bug for addressOf*)
								[mkWorldSize (addressOf a) worldSizeLimit]; 
							| _ -> [];
						)
				)
			| _ -> [];
	in

	object (self)
	inherit nopCilVisitor

	(*
	 * Instrument a statement (branch or function return).
	 *)
	method vstmt(s) =
		match s.skind with
			| If (e, b1, b2, _) ->
			(* hComment: get the first statement's id of a code block *)
			let getFirstStmtId blk = (List.hd blk.bstmts).sid in
			(* hComment: get the first statement's id of THEN-block *)
			let b1_sid = getFirstStmtId b1 in
			(* hComment: get the first statement's id of ELSE-block*)
			let b2_sid = getFirstStmtId b2 in
			(* hComment: instrument the expression, i.e. insert some code *)
			(* before the current if branch*)

			(* self#queueInstr (instrumentExpr e) ; *)
			(* hComment: insert some code at the beginning of each branch body*)
			(prependToBlock [mkBranchOnly b1_sid] b1 ;
			 prependToBlock [mkBranchOnly b2_sid] b2 ; 
			 (* hComment: add a 2-tuple to the branch pair *)
			 addBranchPair (b1_sid, b2_sid));
			DoChildren
		| _ -> DoChildren



	(*
	 * hEdit: add a function call respectively after MPI_Init and before MPI_Finalize
	 *)
	method vinst(i) =

		match i with
			(* Don't instrument calls to functions marked as uninstrumented. *)
			| Call (_, Lval (Var f, NoOffset), _, _)
				when shouldSkipFunction f -> SkipChildren 
			| Call (_, Lval (Var f, NoOffset), g, _)  ->
				(
				match f.vname with 
					| "MPI_Init" ->
						ChangeTo [i;
						mkGetMPIInfo ();];
					| "MPI_Comm_rank"  ->
						let inst_list = (rankMarker g i) in
						ChangeTo inst_list;
					| "MPI_Comm_size"  ->
						let inst_list = worldSizeMarker g @ [i] in
						ChangeTo inst_list;
					| _  -> DoChildren;
				)
			| _  -> DoChildren;

end



let addCrestInitializer f =
	let crestInitTy = TFun (voidType, Some [], false, []) in
	let crestInitFunc = findOrCreateFunc f "__CrestInit" crestInitTy in
	let globalInit = getGlobInit f in
	crestInitFunc.vstorage <- Extern ;
	crestInitFunc.vattr <- [Attr ("crest_skip", [])] ;
	prependToBlock [Call (None, Lval (var crestInitFunc), [], locUnknown)]
	globalInit.sbody


let prepareGlobalForCFG glob =
	match glob with
		(* hComment: this matches a function and prepares it for CFG information *)
		(*  computation by Cil.computeCFGInfo *)
		GFun(func, _) -> prepareCFG func
		(* hComment: this is a wildcard match that matches anything that is *)
		(* not a function *)
		| _ -> ()


(**)
(* hComment: the entry point of this file, i.e., feature *)
(**) 
let feature : featureDescr =
{ 
    (* hComment: the name of this feature. By passing-doFeatureName *)
	(* to "cilly", we can enable this feature. *)
	fd_name = "CrestBranch";
	fd_enabled = ref false;
	fd_description = "instrument a program for use with CREST";
	fd_extraopt = [];
	fd_post_check = true;
	fd_doit =
	
    function (f: file) ->
		((* Simplify the code:
		  *  - simplifying expressions with complex memory references
		  *  - converting loops and switches into goto's and if's
		  *  - transforming functions to have exactly one return *)


		 (* hComment: The simplemem.ml module allows CIL lvalues that *)
		 (* contain memory accesses to be even futher simplified via *)
		 (* the introduction of well-typed temporaries. After this *)
		 (* transformation all lvalues involve at most one memory reference. *)
		 (* @ https://people.eecs.berkeley.edu/~necula/cil/ext.html *)
		 (**)
		 Simplemem.feature.fd_doit f;


		 (* hComment: transform the global functions so as to make them *)
		 (* ready for CFG information generation. Details:  This function *)
		 (* converts all Break, Switch, Default and Continue Cil.stmtkinds *)
		 (* and Cil.labels into Ifs and Gotos, giving the function body a *)
		 (* very CFG-like character. This function modifies its argument in place. *)
		 iterGlobals f prepareGlobalForCFG;


		 (* hComment: make sure each function only have one return*)
		 Oneret.feature.fd_doit f ;	


		 (* To simplify later processing:
		  *  - ensure that every 'if' has a non-empty else block
		  *  - try to transform conditional expressions into predicates
		  *    (e.g. "if (!x) {}" to "if (x == 0) {}") *)
		 (* hComment: "s :> t" denotes s is a subtype of t *)
         (let ncVisitor = new normalizeConditionalsVisitor in
		 visitCilFileSameGlobals (ncVisitor :> cilVisitor) f) ;


		 (* Clear out any existing CFG information. *)
		 Cfg.clearFileCFG f ;


		 (* hComment: why? *)
		 (**)
		 (* Read the ID and statement counts from files.  (This must
		  * occur after clearFileCFG, because clearFileCfg clobbers
		  * the statement counter.) *)
		 readIdCount () ;
		 readStmtCount () ;
		 readFunCount () ;


		 (* hComment: *)
		 (**)
		 (* Compute the control-flow graph. *)
		 Cfg.computeFileCFG f ;


		 (* hComment: why? *)
		 (**)
		 (* Adds function calls to the CFG, by building a map from
		  * function names to the first statements in those functions
		  * and by explicitly adding edges for calls to functions
		  * defined in this file. *)
		 handleCallEdgesAndWriteCfg f ;

		 (* Finally instrument the program. *)
		 (let instVisitor = new crestInstrumentVisitor f in
		  visitCilFileSameGlobals (instVisitor :> cilVisitor) f) ;

		 (* Add a function to initialize the instrumentation library. *)
		 addCrestInitializer f ;

		 (* Write the ID and statement counts, the branches. *)
		 (*         writeIdCount () ;
		  writeStmtCount () ;
		  writeFunCount () ;
		  writeBranches ();
		  *)
		 );

}
