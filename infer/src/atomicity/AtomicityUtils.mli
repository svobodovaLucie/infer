(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module Set = Caml.Set

(** Atomicity violations analysis utilities interface. *)

(* ************************************ Modules ************************************************* *)

(** A set of strings. *)
module SSet : module type of Set.Make (String)

(** A module that represents a lock's access path with the number of times the lock has been
    acquired. *)
module Lock : sig
  (** A representation of a lock. *)
  type t [@@deriving compare, equal]

  include PrettyPrintable.PrintableType with type t := t

  val lock : t -> t
  (** Increases the number of times the lock has been acquired. *)

  val unlock : t -> t
  (** Decreases the number of times the lock has been acquired. *)

  val is_locked : t -> bool
  (** Checks whether the lock is locked at least once. *)

  val create : AccessPath.t -> t
  (** Constructs the module from an access path of a lock. *)

  val path : t -> AccessPath.t
  (** Returns an access path of the lock. *)
end

(** A module that represents associations between lock guards and locks. *)
module Guards : sig
  (** A representation of associations between lock guards and locks. *)
  type t [@@deriving compare, equal]

  include PrettyPrintable.PrintableType with type t := t

  val empty : t
  (** Creates an empty module. *)

  val add : AccessPath.t -> AccessPath.t list -> t -> t
  (** Adds a new association between a lock guard and locks. *)

  val remove : AccessPath.t -> t -> t
  (** Removes an existing association between a lock guard and locks. *)

  val reveal_locks : t -> AccessPath.t list -> AccessPath.t list
  (** Changes a list of access paths as follows: i) If the access path in the list belongs to a
      lock, the access path remains unchaned. ii) If the access path in the list belongs to a lock
      guard, the access path is removed from the list, and all the access paths of this guard's
      locks are appended. *)
end

(* ************************************ Constants *********************************************** *)

val inferDir : string
(** The Infer work directory. *)

val atomicSetsFile : string
(** A file for storing atomic sets. *)

val fileCommentChar : char
(** A character used for commenting in files. *)

(* ************************************ Functions *********************************************** *)

val assert_user : bool -> ('a, F.formatter, unit, unit) format4 -> 'a
(** An assertion with a user message. *)

val is_line_empty : string -> bool
(** Checks whether a line in a file is empty. *)

val f_is_ignored : ?actuals:HilExp.t list option -> Procname.t -> bool
(** Checks whether a given function is ignored. *)

val get_exps_paths : HilExp.t list -> AccessPath.t list
(** Returns access paths of given expressions. *)

val get_exp_path : HilExp.t -> AccessPath.t
(** Returns an access path of a given expression. *)

val proc_name_to_access_path : Procname.t -> AccessPath.t
(** Converts a procedure name to an artificial access path. *)
