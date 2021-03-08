(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module Domain = AtomicSetsDomain

(** Detection of atomic sets interface. *)

val analyse_procedure : Domain.Summary.t InterproceduralAnalysis.t -> Domain.Summary.t option
(** An atomic sets detection entry point. Produces a summary for a given function. Should be invoked
    for each function in the analysed program. *)

val print_atomic_sets : Domain.Summary.t InterproceduralAnalysis.file_t -> IssueLog.t
(** Should be invoked after the atomic sets detection of all functions in the analysed program.
    Prints atomic sets from summaries from all analysed functions. *)
