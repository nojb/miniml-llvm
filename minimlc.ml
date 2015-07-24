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
  type program =
    | Prog of (string * (string * kind) list * kind * clambda) list * string
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
    val icmp : t -> Llvm.Icmp.t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
    val cond_br : t -> Llvm.llvalue -> Llvm.llbasicblock * Llvm.llbasicblock
    val position_at_end : t -> Llvm.llbasicblock -> unit
    val lookup_global : t -> string -> Llvm.llvalue
    val pointer_type : t -> Llvm.lltype
    val int_type : t -> Llvm.lltype
    val define_function : t -> string -> Llvm.lltype list -> Llvm.lltype -> Llvm.llvalue
    val dump_module : t -> unit
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
    let icmp c comp v1 v2 = Llvm.build_icmp comp v1 v2 "" c.b
    let cond_br c v =
      let f = Llvm.block_parent (Llvm.insertion_block c.b) in
      let bb1 = Llvm.append_block c.c "" f in
      let bb2 = Llvm.append_block c.c "" f in
      ignore (Llvm.build_cond_br v bb1 bb2 c.b);
      bb1, bb2
    let position_at_end c bb =
      Llvm.position_at_end bb c.b
    let lookup_global c id =
      match Llvm.lookup_global id c.m with
      | None -> failwith "Low: global %S not found" id
      | Some v -> v
    let pointer_type c = Llvm.pointer_type (Llvm.i32_type c.c)
    let int_type c = Llvm.i32_type c.c
    let define_function c name atyps rtype =
      Llvm.define_function name (Llvm.function_type rtype (Array.of_list atyps)) c.m
    let dump_module c = Llvm.dump_module c.m
  end

  open Closure

  module M = Map.Make (String)

  let find id env =
    try M.find id env with Not_found -> failwith "Llvm.find: %S not found" id

  let toptr c id env =
    match find id env with
    | (v, Ptr) -> v
    | (v, Int) -> Low.inttoptr c v

  let rec compile c env = function
    | Cint n ->
        Low.int c n
    | Clabel id ->
        Low.lookup_global c id
    | Cvar id ->
        begin match find id env with
        | (v, Ptr) ->
            Low.load c v
        | (v, Int) ->
            v
        end
    | Cifthenelse (id, e1, e2) ->
        assert false
    | Clet (id, Int, e1, e2) ->
        compile c (M.add id (compile c env e1, Int) env) e2
    | Cprimitive (Pmakeblock, idl) ->
        let vl = List.map (fun id -> find id env) idl in
        assert false
    | Cprimitive (Pgetfield i, [id]) ->
        let v = toptr c id env in
        Low.gep c v [Low.int c i]

  and compile_tail c env = function
    | Cint _ | Cvar _ | Cprimitive _ as e ->
        Low.ret c (compile c env e)
    | Cifthenelse (id, e1, e2) ->
        let v, _ = find id env in
        let v = Low.icmp c Llvm.Icmp.Ne v (Low.int c 0) in
        let bb1, bb2 = Low.cond_br c v in
        Low.position_at_end c bb1;
        compile_tail c env e1;
        Low.position_at_end c bb2;
        compile_tail c env e2
    | Clet (id, Int, e1, e2) ->
        compile_tail c (M.add id (compile c env e1, Int) env) e2

  let compile (Prog (funs, main)) =
    let c = Low.create "miniml" in
    let env =
      List.fold_left (fun env (name, args, ret, _) ->
          let atyps =
            List.map (function (_, Ptr) -> Low.pointer_type c | (_, Int) -> Low.int_type c) args
          in
          let rtype = match ret with Ptr -> Low.pointer_type c | Int -> Low.int_type c in
          let f = Low.define_function c name atyps rtype in
          M.add name (f, Int) env
        ) M.empty funs
    in
    List.iter (fun (name, args, _, body) ->
        let (f, _) = find name env in
        let params = Array.to_list (Llvm.params f) in
        let env =
          List.fold_left2 (fun env (id, k) v -> M.add id (v, k) env) env args params
        in
        Low.position_at_end c (Llvm.entry_block f);
        compile_tail c env body
      ) funs;
    Low.dump_module c
end

let () =
  let prog =
    [
      "test", [], Int, Closure.Cint 0
    ]
  in
  Llvm.compile (Prog (prog, ""))
