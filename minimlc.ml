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

let failwith fmt = Printf.ksprintf failwith fmt

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
    val create : string -> t
    val int : t -> int -> Llvm.llvalue
    val load : t -> Llvm.llvalue -> Llvm.llvalue
    val gep : t -> Llvm.llvalue -> Llvm.llvalue list -> Llvm.llvalue
    val inttoptr : t -> Llvm.llvalue -> Llvm.llvalue
    val ret : t -> Llvm.llvalue -> unit
    val lookup_global : t -> string -> Llvm.llvalue
  end = struct
    type t =
      { c : Llvm.llcontext;
        b : Llvm.llbuilder;
        m : Llvm.llmodule }
    let create name =
      let c = Llvm.create_context () in
      let b = Llvm.builder c in
      let m = Llvm.create_module c name in
      { c; b; m }
    let int c n = Llvm.const_int (Llvm.i32_type c.c) n
    let load c v = Llvm.build_load v "" c.b
    let gep c v vl = Llvm.build_gep v (Array.of_list vl) "" c.b
    let inttoptr c v =
      Llvm.build_inttoptr v (Llvm.pointer_type (Llvm.i32_type c.c)) "" c.b
    let ret c v = ignore (Llvm.build_ret v c.b)
    let lookup_global c id =
      match Llvm.lookup_global id c.m with
      | None -> failwith "Low: global %S not found" id
      | Some v -> v
  end

  open Closure

  module M = Map.Make (String)

  let find id env =
    try M.find id env with Not_found -> failwith "Llvm.find: %S not found" id

  let toptr c id env =
    match find id env with
    | (Ptr, v) -> v
    | (Int, v) -> Low.inttoptr c v

  let rec compile c env = function
    | Cint n ->
        Low.int c n
    | Clabel id ->
        Low.lookup_global c id
    | Cvar id ->
        begin match find id env with
        | (Ptr, v) ->
            Low.load c v
        | (Int, v) ->
            v
        end
    | Clet (id, Int, e1, e2) ->
        compile c (M.add id (Int, compile c env e1) env) e2
    | Cprimitive (Pmakeblock, idl) ->
        let vl = List.map (fun id -> find id env) idl in
        assert false
    | Cprimitive (Pgetfield i, [id]) ->
        let v = toptr c id env in
        Low.gep c v [Low.int c i]

  and compile_tail c env = function
    | Cint _ | Cprimitive _ as e ->
        Low.ret c (compile c env e)
    | Clet (id, Int, e1, e2) ->
        compile_tail c (M.add id (Int, compile c env e1) env) e2
end
