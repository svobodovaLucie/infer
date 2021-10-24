(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format

(* module Interval = struct *)
    type t = int * int

    let join _a _b = assert false

    let widen ~prev:_ ~next:_ ~num_iters:_ = assert false

    let make lb ub = (lb, ub)

    let zero = (0, 0)

    let leq ~lhs ~rhs = (fst lhs) <= (snd rhs)

    (* let toString itv = F.sprintf "[%d : %d]" (fst itv) (snd itv) *)
(* end *)

type summary = int

let pp fmt sum =
    F.fprintf fmt "Interval: %d" sum
(*
module Locals = Map.Make(Pvar)
module TemporaryLocals = Map.Make (Ident)

type data = {callCount: int; locals: (IntervalCheckerDomain.Interval.t * Location.t) Locals.t, tmp_locals: Pvar.t TemporaryLocals.t}
type astate = data
let initial : data = {callCount = 0; locals = Locals.empty; tmp_locals = TemporaryLocals.empty}

type summary = int
let bounds : make (-20) (20)
*)
(*
let pp_summary fmt astate.callCount =
     (*let pp_variable k v =
       F.fprintf fmt "Interval: %s = %s\n" (Pvar.to_string k) (Interval.toString (fst v))
     in*)
     F.fprintf fmt "Interval: Call count: %d" astate.callCount
     *)