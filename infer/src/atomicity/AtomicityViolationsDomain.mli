(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format

(** Detection of atomicity violations domain interface. *)

(* ************************************ Astate ************************************************** *)

(** An abstract state of a function. *)
type t [@@deriving compare, equal]

(** An alias for the type 't'. *)
type astate = t [@@deriving compare, equal]

include AbstractDomain.S with type t := t

val initial : t
(** An initial abstract state of an analysed function. *)

val apply_call : fName:string -> Location.t -> t -> t
(** Updates an abstract state on a function call. *)

val apply_locks : AccessPath.t list -> t -> t
(** Updates an abstract state on a lock call. *)

val apply_unlocks : AccessPath.t list -> t -> t
(** Updates an abstract state on an unlock call. *)

val apply_guard_construct : AccessPath.t -> AccessPath.t list -> acquire:bool -> t -> t
(** Updates an abstract state on a lock guard constructor call. *)

val apply_guard_release : AccessPath.t -> t -> t
(** Updates an abstract state on a lock guard release call. *)

val apply_guard_destroy : AccessPath.t -> t -> t
(** Updates an abstract state on a lock guard destructor call. *)

val report_atomicity_violations : f:(Location.t -> msg:string -> unit) -> t -> unit
(** Reports atomicity violations from an abstract state using reporting function. *)

(* ************************************ Summary ************************************************* *)

(** A module that encapsulates a summary of a function. *)
module Summary : sig
  (** A summary of a function. *)
  type t [@@deriving compare, equal]

  include PrettyPrintable.PrintableType with type t := t

  val create : astate -> t
  (** Converts an abstract state to a summary. *)
end

val apply_summary : Summary.t -> Location.t -> t -> t
(** Updates an abstract state on a function call with its summary. *)
