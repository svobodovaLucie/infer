(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format

module FiniteBounds = struct
    type t = int

    let leq ~lhs ~rhs = lhs <= rhs

    let join a b = Stdlib.max a b

    let widen ~prev ~next ~num_iters:_ = join prev next

    let pp fmt astate = F.fprintf fmt "%d" astate
end

module BoundsWithTop = struct
    open AbstractDomain.Types
    include AbstractDomain.TopLifted (FiniteBounds)

    let widening_threshold = 5

    let widen ~prev ~next ~num_iters =
        match (prev, next) with
        | Top, _ | _, Top ->
            Top
        | NonTop prev, NonTop next when num_iters < widening_threshold ->
            NonTop (FiniteBounds.join prev next)
        | NonTop _, NonTop _ ->
            Top
end

module ReturnsPrintf = AbstractDomain.BooleanOr
include AbstractDomain.Pair (BoundsWithTop) (ReturnsPrintf)
open AbstractDomain.Types

(* let inc fc = fc + 1 *)
let inc = function
    | (Top, _) as astate ->
        astate
    | NonTop num, has_printf ->
        (NonTop (num + 1), has_printf)

let initial = (NonTop 0, false)

let apply_summary ~summary:(summary_count, summary_has_printf) (current_count, current_has_printf) =
    let new_count =
        match current_count with
        | Top ->
            Top
        | NonTop current_count ->
            let return_count = if summary_has_printf then 1 else 0 in
            let summary_count =
                match summary_count with Top -> 0 | NonTop count -> count
            in
            NonTop (summary_count + current_count + return_count)
        in
        (new_count, current_has_printf)

type astate = t

type summary = t
