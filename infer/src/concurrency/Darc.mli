(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
(* Data Race Checker *)

open! IStd

val checker :
  DarcDomain.summary InterproceduralAnalysis.t -> DarcDomain.summary option