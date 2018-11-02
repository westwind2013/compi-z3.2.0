module H :
  sig
    type ('a, 'b) t = ('a, 'b) Hashtbl.t
    val create : ?random:bool -> int -> ('a, 'b) t
    val clear : ('a, 'b) t -> unit
    val reset : ('a, 'b) t -> unit
    val copy : ('a, 'b) t -> ('a, 'b) t
    val add : ('a, 'b) t -> 'a -> 'b -> unit
    val find : ('a, 'b) t -> 'a -> 'b
    val find_all : ('a, 'b) t -> 'a -> 'b list
    val mem : ('a, 'b) t -> 'a -> bool
    val remove : ('a, 'b) t -> 'a -> unit
    val replace : ('a, 'b) t -> 'a -> 'b -> unit
    val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
    val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
    val length : ('a, 'b) t -> int
    val randomize : unit -> unit
    type statistics =
      Hashtbl.statistics = {
      num_bindings : int;
      num_buckets : int;
      max_bucket_length : int;
      bucket_histogram : int array;
    }
    val stats : ('a, 'b) t -> statistics
    module type HashedType =
      sig type t val equal : t -> t -> bool val hash : t -> int end
    module type S =
      sig
        type key
        type 'a t
        val create : int -> 'a t
        val clear : 'a t -> unit
        val reset : 'a t -> unit
        val copy : 'a t -> 'a t
        val add : 'a t -> key -> 'a -> unit
        val remove : 'a t -> key -> unit
        val find : 'a t -> key -> 'a
        val find_all : 'a t -> key -> 'a list
        val replace : 'a t -> key -> 'a -> unit
        val mem : 'a t -> key -> bool
        val iter : (key -> 'a -> unit) -> 'a t -> unit
        val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
        val length : 'a t -> int
        val stats : 'a t -> statistics
      end
    module Make :
      functor (H : HashedType) ->
        sig
          type key = H.t
          type 'a t = 'a Hashtbl.Make(H).t
          val create : int -> 'a t
          val clear : 'a t -> unit
          val reset : 'a t -> unit
          val copy : 'a t -> 'a t
          val add : 'a t -> key -> 'a -> unit
          val remove : 'a t -> key -> unit
          val find : 'a t -> key -> 'a
          val find_all : 'a t -> key -> 'a list
          val replace : 'a t -> key -> 'a -> unit
          val mem : 'a t -> key -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val length : 'a t -> int
          val stats : 'a t -> statistics
        end
    module type SeededHashedType =
      sig type t val equal : t -> t -> bool val hash : int -> t -> int end
    module type SeededS =
      sig
        type key
        type 'a t
        val create : ?random:bool -> int -> 'a t
        val clear : 'a t -> unit
        val reset : 'a t -> unit
        val copy : 'a t -> 'a t
        val add : 'a t -> key -> 'a -> unit
        val remove : 'a t -> key -> unit
        val find : 'a t -> key -> 'a
        val find_all : 'a t -> key -> 'a list
        val replace : 'a t -> key -> 'a -> unit
        val mem : 'a t -> key -> bool
        val iter : (key -> 'a -> unit) -> 'a t -> unit
        val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
        val length : 'a t -> int
        val stats : 'a t -> statistics
      end
    module MakeSeeded :
      functor (H : SeededHashedType) ->
        sig
          type key = H.t
          type 'a t = 'a Hashtbl.MakeSeeded(H).t
          val create : ?random:bool -> int -> 'a t
          val clear : 'a t -> unit
          val reset : 'a t -> unit
          val copy : 'a t -> 'a t
          val add : 'a t -> key -> 'a -> unit
          val remove : 'a t -> key -> unit
          val find : 'a t -> key -> 'a
          val find_all : 'a t -> key -> 'a list
          val replace : 'a t -> key -> 'a -> unit
          val mem : 'a t -> key -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val length : 'a t -> int
          val stats : 'a t -> statistics
        end
    val hash : 'a -> int
    val seeded_hash : int -> 'a -> int
    val hash_param : int -> int -> 'a -> int
    val seeded_hash_param : int -> int -> int -> 'a -> int
  end
module S :
  sig
    external length : string -> int = "%string_length"
    external get : string -> int -> char = "%string_safe_get"
    external set : string -> int -> char -> unit = "%string_safe_set"
    external create : int -> string = "caml_create_string"
    val make : int -> char -> string
    val copy : string -> string
    val sub : string -> int -> int -> string
    val fill : string -> int -> int -> char -> unit
    val blit : string -> int -> string -> int -> int -> unit
    val concat : string -> string list -> string
    val iter : (char -> unit) -> string -> unit
    val iteri : (int -> char -> unit) -> string -> unit
    val map : (char -> char) -> string -> string
    val trim : string -> string
    val escaped : string -> string
    val index : string -> char -> int
    val rindex : string -> char -> int
    val index_from : string -> int -> char -> int
    val rindex_from : string -> int -> char -> int
    val contains : string -> char -> bool
    val contains_from : string -> int -> char -> bool
    val rcontains_from : string -> int -> char -> bool
    val uppercase : string -> string
    val lowercase : string -> string
    val capitalize : string -> string
    val uncapitalize : string -> string
    type t = string
    val compare : t -> t -> int
    external unsafe_get : string -> int -> char = "%string_unsafe_get"
    external unsafe_set : string -> int -> char -> unit
      = "%string_unsafe_set"
    external unsafe_blit : string -> int -> string -> int -> int -> unit
      = "caml_blit_string" "noalloc"
    external unsafe_fill : string -> int -> int -> char -> unit
      = "caml_fill_string" "noalloc"
  end
exception NotConstant
type llvmBlock = {
  lblabel : string;
  mutable lbbody : llvmInstruction list;
  mutable lbterminator : llvmTerminator;
  mutable lbpreds : llvmBlock list;
}
and llvmInstruction = {
  mutable liresult : llvmLocal option;
  liop : llvmOp;
  mutable liargs : llvmValue list;
}
and llvmTerminator =
    TUnreachable
  | TDead
  | TRet of llvmValue list
  | TBranch of llvmBlock
  | TCond of llvmValue * llvmBlock * llvmBlock
  | TSwitch of llvmValue * llvmBlock * (int64 * llvmBlock) list
and llvmValue =
    LGlobal of llvmGlobal
  | LLocal of llvmLocal
  | LBool of bool
  | LInt of int64 * Cil.ikind
  | LFloat of float * Cil.fkind
  | LUndef
  | LZero
  | LNull of llvmType
  | LPhi of llvmValue * llvmBlock
  | LType of llvmType
  | LGetelementptr of llvmValue list
  | LCast of llvmCast * llvmValue * llvmType
  | LBinary of llvmBinop * llvmValue * llvmValue * llvmType
  | LCmp of llvmCmp * llvmValue * llvmValue
  | LFcmp of llvmFCmp * llvmValue * llvmValue
  | LSelect of llvmValue * llvmValue * llvmValue
and llvmLocal = string * llvmType
and llvmGlobal = string * llvmType
and llvmType = Cil.typ
and llvmOp =
    LIassign
  | LIphi
  | LIgetelementptr
  | LIload
  | LIstore
  | LIcall
  | LIalloca
  | LIbinary of llvmBinop
  | LIcmp of llvmCmp
  | LIfcmp of llvmFCmp
  | LIselect
  | LIcast of llvmCast
  | LIva_arg
and llvmBinop =
    LBadd
  | LBsub
  | LBmul
  | LBudiv
  | LBsdiv
  | LBfdiv
  | LBurem
  | LBsrem
  | LBfrem
  | LBshl
  | LBlshr
  | LBashr
  | LBand
  | LBor
  | LBxor
and llvmCmp =
    LCeq
  | LCne
  | LCslt
  | LCult
  | LCsle
  | LCule
  | LCsgt
  | LCugt
  | LCsge
  | LCuge
and llvmFCmp =
    LCFoeq
  | LCFone
  | LCFolt
  | LCFole
  | LCFogt
  | LCFoge
  | LCFord
  | LCFueq
  | LCFune
  | LCFult
  | LCFule
  | LCFugt
  | LCFuge
and llvmCast =
    LAtrunc
  | LAzext
  | LAsext
  | LAuitofp
  | LAsitofp
  | LAfptoui
  | LAfptosi
  | LAfptrunc
  | LAfpext
  | LAinttoptr
  | LAptrtoint
  | LAbitcast
val binopName : llvmBinop -> string
val cmpName : llvmCmp -> string
val fcmpName : llvmFCmp -> string
val castName : llvmCast -> string
val i1Type : Cil.typ
val i32Type : Cil.typ
val i8starType : Cil.typ
val llvmTypeOf : llvmValue -> llvmType
val llvmLocalType : Cil.typ -> bool
val llvmUseLocal : Cil.varinfo -> bool
val llvmDoNotUseLocal : Cil.varinfo -> bool
val llvmDestinations : llvmTerminator -> llvmBlock list
val llvmValueEqual : llvmValue -> llvmValue -> bool
val llocal : Cil.varinfo -> llvmLocal
val lglobal : Cil.varinfo -> llvmGlobal
val lvar : Cil.varinfo -> llvmValue
val lint : int -> Cil.typ -> llvmValue
val lzero : Cil.typ -> llvmValue
val mkIns : llvmOp -> llvmLocal -> llvmValue list -> llvmInstruction
val mkVoidIns : llvmOp -> llvmValue list -> llvmInstruction
val mkTrueIns : llvmLocal -> llvmValue -> llvmInstruction
val llvmEscape : string -> string
val llvmValueNegate : llvmValue -> llvmValue
val llvmCastOp : Cil.typ -> Cil.typ -> llvmCast
class type llvmGenerator =
  object
    method addString : string -> llvmGlobal
    method addWString : int64 list -> llvmGlobal
    method mkConstant : Cil.constant -> llvmValue
    method mkConstantExp : Cil.exp -> llvmValue
    method mkFunction : Cil.fundec -> llvmBlock list
    method printBlocks : unit -> llvmBlock list -> Pretty.doc
    method printGlobals : unit -> Pretty.doc
    method printValue : unit -> llvmValue -> Pretty.doc
    method printValueNoType : unit -> llvmValue -> Pretty.doc
  end
class llvmGeneratorClass : llvmGenerator
