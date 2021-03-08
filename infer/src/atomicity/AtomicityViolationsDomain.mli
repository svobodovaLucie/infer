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

val apply_call : t -> string -> Location.t -> t
(** Updates an abstract state on a function call. *)

val apply_lock : ?locksPaths:AccessPath.t option list -> t -> t
(** Updates an abstract state on a lock call. *)

val apply_unlock : ?locksPaths:AccessPath.t option list -> t -> t
(** Updates an abstract state on an unlock call. *)

val report_atomicity_violations : t -> f:(Location.t -> msg:string -> unit) -> unit
(** Reports atomicity violations from an abstract state using reporting function. *)

(* ************************************ Summary ************************************************* *)

(** A module that encapsulates a summary of a function. *)
module Summary : sig
  (** A summary of a function. *)
  type t [@@deriving compare, equal]

  include PrettyPrintable.PrintableType with type t := t

  val make : astate -> t
  (** Converts an abstract state to a summary. *)
end

val apply_summary : t -> Summary.t -> Location.t -> t
(** Updates an abstract state on a function call with its summary. *)
