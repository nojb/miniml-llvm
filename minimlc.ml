(* The MIT License (MIT)

   Copyright (c) 2015 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
   FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
   COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
   IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
   CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. *)

let failwith = Printf.ksprintf failwith

type primitive =
  | Pmakeblock
  | Pgetfield of int
  | Paddint
  | Pmulint

type kind =
  | Ptr
  | Int

module Closure = struct
  type clambda =
    | Cint of int
    | Clabel of string
    | Cvar of string
    | Cifthenelse of string * clambda * clambda
    | Clet of string * kind * clambda * clambda
    | Capply of string * string list
    | Cprimitive of primitive * string list
end

module Llvm = struct
  module Low : sig
    type t
    val int : t -> int -> Llvm.llvalue
    val load : t -> Llvm.llvalue -> Llvm.llvalue
    val lookup_global : t -> string -> Llvm.llvalue
  end = struct
    type t =
      { b : Llvm.llbuilder;
        c : Llvm.llcontext;
        m : Llvm.llmodule }

    let int c n = Llvm.const_int (Llvm.i32_type c.c) n
    let load c v = Llvm.build_load v "" c.b
    let lookup_global c id =
      match Llvm.lookup_global id c.m with
      | None -> failwith "Low: global %S not found" id
      | Some v -> v
  end

  open Closure

  module M = Map.Make (String)

  let compile c env = function
    | Cint n ->
        Low.int c n
    | Clabel id ->
        Low.lookup_global c id
    | Cvar id ->
        begin match M.find id env with
        | (Ptr, v) ->
            Low.load c v
        | (Int, v) ->
            v
        end
end
