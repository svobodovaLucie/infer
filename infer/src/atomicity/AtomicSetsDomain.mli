(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format

(** Detection of atomic sets domain interface. *)

(* ************************************ Astate ************************************************** *)

(** An abstract state of a function. *)
type t [@@deriving compare, equal]

(** An alias for the type 't'. *)
type astate = t [@@deriving compare, equal]

include AbstractDomain.S with type t := t

val initial : t
(** An initial abstract state of an analysed function. *)

val apply_call : t -> string -> t
(** Updates an abstract state on a function call. *)

val apply_lock : ?locksPaths:AccessPath.t option list -> t -> t
(** Updates an abstract state on a lock call. *)

val apply_unlock : ?locksPaths:AccessPath.t option list -> t -> t
(** Updates an abstract state on an unlock call. *)

val update_at_the_end_of_function : t -> t
(** Updates an abstract state at the end of a function. *)

(* ************************************ Summary ************************************************* *)

(** A module that encapsulates a summary of a function. *)
module Summary : sig
  (** A summary of a function. *)
  type t [@@deriving compare, equal]

  include PrettyPrintable.PrintableType with type t := t

  val make : astate -> t
  (** Converts an abstract state to a summary. *)

  val print_atomic_sets : t -> f_name:string -> Out_channel.t -> int * int
  (** Prints atomic sets from a given summary together with a function name to a given output
      channel. Returns a pair of a number of printed atomic sets and a number of printed atomic
      functions at total. *)
end

val apply_summary : t -> Summary.t -> t
(** Updates an abstract state on a function call with its summary. *)
