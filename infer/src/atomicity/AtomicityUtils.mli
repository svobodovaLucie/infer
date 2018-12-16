(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module Set = Caml.Set

(** Atomicity violations analysis utilities interface. *)

(* ************************************ Modules ************************************************* *)

(** A set of strings. *)
module SSet : module type of Set.Make (String)

(* ************************************ Constants *********************************************** *)

val inferDir : string
(** The Infer work directory. *)

val atomicSetsFile : string
(** A file for storing atomic sets. *)

(* ************************************ Functions *********************************************** *)

val str_contains : haystack:string -> needle:string -> bool
(** Checks whether the second string is a substring of the first string. *)

val f_is_ignored : ?actuals:HilExp.t list option -> Procname.t -> bool
(** Checks whether a given function is ignored. *)

val get_lock_path : HilExp.t -> AccessPath.t option
(** Returns an access path of a given expression. *)
