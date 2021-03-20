(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format

(** Detection of atomicity violations domain interface. *)

(* ************************************ Astate ************************************************** *)

include PrettyPrintable.PrintableEquatableOrderedType

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

(* ************************************ Summary ************************************************* *)

(** A module that encapsulates a summary of a function. *)
module Summary : sig
  include PrettyPrintable.PrintableEquatableOrderedType

  val create : astate -> t
  (** Converts an abstract state to a summary. *)

  val is_top_level_fun : Procname.t -> (Procname.t * t) list -> bool
  (** Determines whether a given function is a top level function (using a list of all analysed
      functions with their summaries). *)

  val report_atomicity_violations :
       f:(Location.t -> msg:string -> IssueType.t -> IssueLog.t -> IssueLog.t)
    -> t
    -> IssueLog.t
    -> IssueLog.t
  (** Reports atomicity violations from the summary using a reporting function. *)
end

val apply_summary : Summary.t -> Location.t -> t -> t
(** Updates an abstract state on a function call with its summary. *)
