module E :
  sig
    val logChannel : out_channel ref
    val debugFlag : bool ref
    val verboseFlag : bool ref
    val colorFlag : bool ref
    val redEscStr : string
    val greenEscStr : string
    val yellowEscStr : string
    val blueEscStr : string
    val purpleEscStr : string
    val cyanEscStr : string
    val whiteEscStr : string
    val resetEscStr : string
    val warnFlag : bool ref
    exception Error
    val error : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val bug : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val unimp : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val s : 'a -> 'b
    val hadErrors : bool ref
    val warn : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val warnOpt : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val log : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val logg : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val null : ('a, unit, Pretty.doc, unit) format4 -> 'a
    val pushContext : (unit -> Pretty.doc) -> unit
    val popContext : unit -> unit
    val showContext : unit -> unit
    val withContext : (unit -> Pretty.doc) -> ('a -> 'b) -> 'a -> 'b
    val newline : unit -> unit
    val newHline : unit -> unit
    val getPosition : unit -> int * string * int
    val getHPosition : unit -> int * string
    val setHLine : int -> unit
    val setHFile : string -> unit
    val setCurrentLine : int -> unit
    val setCurrentFile : string -> unit
    type location =
      Errormsg.location = {
      file : string;
      line : int;
      hfile : string;
      hline : int;
    }
    val d_loc : unit -> location -> Pretty.doc
    val d_hloc : unit -> location -> Pretty.doc
    val getLocation : unit -> location
    val parse_error : string -> 'a
    val locUnknown : location
    val readingFromStdin : bool ref
    val startParsing : ?useBasename:bool -> string -> Lexing.lexbuf
    val startParsingFromString :
      ?file:string -> ?line:int -> string -> Lexing.lexbuf
    val finishParsing : unit -> unit
  end
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
val is_bitfield : Cil.offset -> bool
val addr_of_lv : Cil.lhost * Cil.offset -> Cil.exp
class logWriteVisitor :
  object
    val printfFun : Cil.fundec
    method queueInstr : Cil.instr list -> unit
    method unqueueInstr : unit -> Cil.instr list
    method vattr : Cil.attribute -> Cil.attribute list Cil.visitAction
    method vattrparam : Cil.attrparam -> Cil.attrparam Cil.visitAction
    method vblock : Cil.block -> Cil.block Cil.visitAction
    method vexpr : Cil.exp -> Cil.exp Cil.visitAction
    method vfunc : Cil.fundec -> Cil.fundec Cil.visitAction
    method vglob : Cil.global -> Cil.global list Cil.visitAction
    method vinit :
      Cil.varinfo -> Cil.offset -> Cil.init -> Cil.init Cil.visitAction
    method vinitoffs : Cil.offset -> Cil.offset Cil.visitAction
    method vinst : Cil.instr -> Cil.instr list Cil.visitAction
    method vlval : Cil.lval -> Cil.lval Cil.visitAction
    method voffs : Cil.offset -> Cil.offset Cil.visitAction
    method vstmt : Cil.stmt -> Cil.stmt Cil.visitAction
    method vtype : Cil.typ -> Cil.typ Cil.visitAction
    method vvdec : Cil.varinfo -> Cil.varinfo Cil.visitAction
    method vvrbl : Cil.varinfo -> Cil.varinfo Cil.visitAction
  end
val feature : Cil.featureDescr
