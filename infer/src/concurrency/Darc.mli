(*
 * Author: Lucie Svobodová (xsvobo1x@stud.fit.vutbr.cz), 2022-present
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Faculty of Information Technology, Brno University of Technology, CZ
 *)
 (* Data Race Checker *)

open! IStd

(* main checker function (registered in RegisterCheckers) *)
val checker :
  DarcDomain.summary InterproceduralAnalysis.t -> DarcDomain.summary option