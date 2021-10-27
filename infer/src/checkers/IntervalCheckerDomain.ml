(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format

type t = int

type astate = t

type summary = astate

let leq ~lhs ~rhs = lhs <= rhs

let join a b = Stdlib.max a b

let inc fc = fc + 1

let widen ~prev ~next ~num_iters:_ = join prev next

let pp fmt astate = F.fprintf fmt "%d" astate

let initial = 0


