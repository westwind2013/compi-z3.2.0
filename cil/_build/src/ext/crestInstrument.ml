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
  let idArg   = ("id",   idType,   []) in
  let bidArg  = ("bid",  bidType,  []) in
  let fidArg  = ("fid",  fidType,  []) in
  let valArg  = ("val",  valType,  []) in
  let addrArg = ("addr", addrType, []) in
  let opArg   = ("op",   opType,   []) in
  let boolArg = ("b",    boolType, []) in

	(* hComment: create a function that has at least one argument (idArg) *)
  let mkInstFunc name args =
    let ty = TFun (voidType, Some (idArg :: args), false, []) in
    let func = findOrCreateFunc f ("__Crest" ^ name) ty in
      func.vstorage <- Extern ;
      func.vattr <- [Attr ("crest_skip", [])] ;
      func
  in
	
	(* hComment: create specific functions for all types of instructions *)
  let loadFunc         = mkInstFunc "Load"  [addrArg; valArg] in
  let storeFunc        = mkInstFunc "Store" [addrArg] in
  let clearStackFunc   = mkInstFunc "ClearStack" [] in
  let apply1Func       = mkInstFunc "Apply1" [opArg; valArg] in
  let apply2Func       = mkInstFunc "Apply2" [opArg; valArg] in
  let branchFunc       = mkInstFunc "Branch" [bidArg; boolArg] in
  let callFunc         = mkInstFunc "Call" [fidArg] in
  let returnFunc       = mkInstFunc "Return" [] in
  let handleReturnFunc = mkInstFunc "HandleReturn" [valArg] in

  (*
   * Functions to create calls to the above instrumentation functions.
   *)
  let mkInstCall func args =
		(* hComment: add an id to the used function *)
    let args' = integer (getNewId ()) :: args in
      Call (None, Lval (var func), args', locUnknown)
  in

  let unaryOpCode op =
    let c =
      match op with
        | Neg -> 19  | BNot -> 20  |  LNot -> 21
    in
      integer c
  in

  let binaryOpCode op =
    let c =
      match op with
        | PlusA   ->  0  | MinusA  ->  1  | Mult  ->  2  | Div   ->  3
        | Mod     ->  4  | BAnd    ->  5  | BOr   ->  6  | BXor  ->  7
        | Shiftlt ->  8  | Shiftrt ->  9  | LAnd  -> 10  | LOr   -> 11
        | Eq      -> 12  | Ne      -> 13  | Gt    -> 14  | Le    -> 15
        | Lt      -> 16  | Ge      -> 17
            (* Other/unhandled operators discarded and treated concretely. *)
        | _ -> 18
    in
      integer c
  in

	(* hComment: CastE, from CIL, performs type conversion *)
  let toAddr e = CastE (addrType, e) in

  let toValue e =
      if isPointerType (typeOf e) then
        CastE (valType, CastE (addrType, e))
      else
        CastE (valType, e)
  in

  let mkLoad addr value    = mkInstCall loadFunc [toAddr addr; toValue value] in
  let mkStore addr         = mkInstCall storeFunc [toAddr addr] in
  let mkClearStack ()      = mkInstCall clearStackFunc [] in
  let mkApply1 op value    = mkInstCall apply1Func [unaryOpCode op; toValue value] in
  let mkApply2 op value    = mkInstCall apply2Func [binaryOpCode op; toValue value] in
  let mkBranch bid b       = mkInstCall branchFunc [integer bid; integer b] in
  let mkCall fid           = mkInstCall callFunc [integer fid] in
  let mkReturn ()          = mkInstCall returnFunc [] in
  let mkHandleReturn value = mkInstCall handleReturnFunc [toValue value] in


  (*
   * Instrument an expression.
   *)
  let rec instrumentExpr e =
    if isConstant e then
      [mkLoad noAddr e]
    else
      match e with
        | Lval lv when hasAddress  lv ->
            [mkLoad (addressOf lv) e]

        | UnOp (op, e1, _) ->
            (* Should skip this if we don't currently handle 'op'. *)
						(* hComment: symbol '@' is used to concatenate two lists*)
            (instrumentExpr e1) @ [mkApply1 op e]

        | BinOp (op, e1, e2, _) ->
            (* Should skip this if we don't currently handle 'op'. *)
            (instrumentExpr e1) @ (instrumentExpr e2) @ [mkApply2 op e]

        | CastE (_, e) ->
            (* We currently treat cast's as no-ops, which is not precise. *)
            instrumentExpr e

        (* Default case: We cannot instrument, so generate a concrete load
         * and stop recursing. *)
        | _ -> [mkLoad noAddr e]
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
	    (self#queueInstr (instrumentExpr e) ;
			(* hComment: insert some code at the beginning of each branch body*)
	     prependToBlock [mkBranch b1_sid 1] b1 ;
	     prependToBlock [mkBranch b2_sid 0] b2 ;
						 (* hComment: add a 2-tuple to the branch pair *)
             addBranchPair (b1_sid, b2_sid)) ;
            DoChildren

      | Return (Some e, _) ->
          if isSymbolicType (typeOf e) then
            self#queueInstr (instrumentExpr e) ;
          self#queueInstr [mkReturn ()] ;
          SkipChildren

      | Return (None, _) ->
          self#queueInstr [mkReturn ()] ;
          SkipChildren

      | _ -> DoChildren


  (*
   * Instrument assignment and call statements.
   *)
  method vinst(i) =
    match i with
      | Set (lv, e, _) ->
          if (isSymbolicType (typeOf e)) && (hasAddress lv) then
            (self#queueInstr (instrumentExpr e) ;
             self#queueInstr [mkStore (addressOf lv)]) ;
          SkipChildren

      (* Don't instrument calls to functions marked as uninstrumented. *)
      | Call (_, Lval (Var f, NoOffset), _, _)
          when shouldSkipFunction f -> SkipChildren

      | Call (ret, _, args, _) ->
          let isSymbolicExp e = isSymbolicType (typeOf e) in
          let isSymbolicLval lv = isSymbolicType (typeOfLval lv) in
          let argsToInst = List.filter isSymbolicExp args in
            self#queueInstr (concatMap instrumentExpr argsToInst) ;
            (match ret with
               | Some lv when ((isSymbolicLval lv) && (hasAddress lv)) ->
                   ChangeTo [i ;
                             mkHandleReturn (Lval lv) ;
                             mkStore (addressOf lv)]
               | _ ->
                   ChangeTo [i ; mkClearStack ()])

      | _ -> DoChildren


  (*
   * Instrument function entry.
   *)
  method vfunc(f) =
    if shouldSkipFunction f.svar then
      SkipChildren
    else
      let instParam v = mkStore (addressOf (var v)) in
      let isSymbolic v = isSymbolicType v.vtype in
      let (_, _, isVarArgs, _) = splitFunctionType f.svar.vtype in
      let paramsToInst = List.filter isSymbolic f.sformals in
        addFunction () ;
        if (not isVarArgs) then
          prependToBlock (List.rev_map instParam paramsToInst) f.sbody ;
        prependToBlock [mkCall !funCount] f.sbody ;
        DoChildren

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
		fd_name = "CrestInstrument";
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
          writeIdCount () ;
          writeStmtCount () ;
          writeFunCount () ;
          writeBranches ());
  }
