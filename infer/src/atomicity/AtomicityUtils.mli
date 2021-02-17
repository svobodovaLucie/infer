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

val fileCommentChar : char
(** A character used for commenting in files. *)

val is_line_empty : string -> bool
(** Checks whether a line in a file is empty. *)

(* ************************************ Functions *********************************************** *)

val str_contains : haystack:string -> needle:string -> bool
(** Checks whether the second string is a substring of the first string. *)

val f_is_ignored : ?actuals:HilExp.t list option -> Procname.t -> bool
(** Checks whether a given function is ignored. *)

val get_locks_paths : HilExp.t list -> AccessPath.t option list
(** Returns access paths of given lock expressions. *)
