(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

include AbstractDomain.S

(* module Interval :
  sig *)
    val make : int -> int -> t

    val zero : t
(* end *)

type summary = int

val pp_summary : Format.formatter -> summary -> unit

val pp : Format.formatter -> t -> unit