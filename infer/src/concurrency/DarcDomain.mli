(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
 (* Data Race Checker Domain *)

open! IStd

include AbstractDomain.S

val initial : t

val inc : t -> t

type astate = t

val has_printf : t -> bool

val apply_summary : summary : t -> t -> t

type summary = t
