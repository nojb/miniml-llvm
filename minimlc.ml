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

module Low : sig
  type t
  val create : string -> t
  val int_type : t -> Llvm.lltype
  val ptr_type : t -> Llvm.lltype
  val int : t -> int -> Llvm.llvalue
  val load : t -> Llvm.llvalue -> Llvm.llvalue
  val store : t -> Llvm.llvalue -> Llvm.llvalue -> unit
  val gep : t -> Llvm.llvalue -> Llvm.llvalue list -> Llvm.llvalue
  val inttoptr : t -> Llvm.llvalue -> Llvm.llvalue
  val ptrtoint : t -> Llvm.llvalue -> Llvm.llvalue
  val ret : t -> Llvm.llvalue -> unit
  val icmp : t -> Llvm.Icmp.t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
  val phi : t -> (Llvm.llvalue * Llvm.llbasicblock) list -> Llvm.llvalue
  val alloca : t -> Llvm.lltype -> Llvm.llvalue
  val cond_br : t -> Llvm.llvalue -> Llvm.llbasicblock * Llvm.llbasicblock
  val append_block : t -> Llvm.llbasicblock
  val position_at_end : t -> Llvm.llbasicblock -> unit
  val entry_block : t -> Llvm.llbasicblock
  val lookup_function : t -> string -> Llvm.llvalue
  val define_function : t -> string -> Llvm.lltype list -> Llvm.lltype -> Llvm.llvalue
  val dump_module : t -> unit
  val insertion_block : t -> Llvm.llbasicblock
  val add : t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
  val call : t -> Llvm.llvalue -> Llvm.llvalue list -> Llvm.llvalue
  val malloc : t -> int -> Llvm.llvalue
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
  let int_type c =
    match Sys.word_size with
    | 32 -> Llvm.i32_type c.c
    | 64 -> Llvm.i64_type c.c
    | _ -> assert false
  let ptr_type c = Llvm.pointer_type (int_type c)
  let int c n = Llvm.const_int (int_type c) n
  let load c v = Llvm.build_load v "" c.b
  let store c v p = ignore (Llvm.build_store v p c.b)
  let gep c v vl =
    let vl = List.map (fun v -> Llvm.build_trunc v (Llvm.i32_type c.c) "" c.b) vl in
    Llvm.build_gep v (Array.of_list vl) "" c.b
  let inttoptr c v = Llvm.build_inttoptr v (ptr_type c) "" c.b
  let ptrtoint c v = Llvm.build_ptrtoint v (int_type c) "" c.b
  let ret c v = ignore (Llvm.build_ret v c.b)
  let icmp c comp v1 v2 = Llvm.build_icmp comp v1 v2 "" c.b
  let phi c l = Llvm.build_phi l "" c.b
  let alloca c t = Llvm.build_alloca t "" c.b
  let cond_br c v =
    let f = Llvm.block_parent (Llvm.insertion_block c.b) in
    let bb1 = Llvm.append_block c.c "" f in
    let bb2 = Llvm.append_block c.c "" f in
    ignore (Llvm.build_cond_br v bb1 bb2 c.b);
    bb1, bb2
  let append_block c =
    let f = Llvm.block_parent (Llvm.insertion_block c.b) in
    Llvm.append_block c.c "" f
  let position_at_end c bb =
    Llvm.position_at_end bb c.b
  let entry_block c =
    let f = Llvm.block_parent (Llvm.insertion_block c.b) in
    Llvm.entry_block f
  let lookup_function c id =
    match Llvm.lookup_function id c.m with
    | None -> failwith "Low: function %S not found" id
    | Some v -> v
  let define_function c name atyps rtype =
    Llvm.define_function name (Llvm.function_type rtype (Array.of_list atyps)) c.m
  let dump_module c = Llvm.dump_module c.m
  let insertion_block c = Llvm.insertion_block c.b
  let add c v1 v2 = Llvm.build_add v1 v2 "" c.b
  let call c v vl = Llvm.build_call v (Array.of_list vl) "" c.b
  let malloc c n =
    let t = Llvm.function_type (ptr_type c) [| Llvm.i32_type c.c |] in
    let f = Llvm.declare_function "malloc" t c.m in
    Llvm.build_call f [| Llvm.const_int (Llvm.i32_type c.c) (n * Sys.word_size / 8) |] "" c.b
end

module Llvmgen = struct
  open Closure

  module M = Map.Make (String)

  let find id env =
    try M.find id env with Not_found -> failwith "Llvmgen.find: %S not found" id

  let toptr c id env =
    match find id env with
    | (v, Ptr) -> v
    | (v, Int) -> Low.inttoptr c v

  let toint c id env =
    match find id env with
    | (v, Ptr) -> Low.ptrtoint c v
    | (v, Int) -> v

  let rec compile c env = function
    | Cint n ->
        Low.int c n
    | Clabel id ->
        Low.lookup_function c id
    | Cvar id ->
        begin match find id env with
        | (v, Ptr) -> Low.load c v
        | (v, Int) -> v
        end
    | Cifthenelse (id, e1, e2) ->
        let v, _ = find id env in
        let v = Low.icmp c Llvm.Icmp.Ne v (Low.int c 0) in
        let bb1, bb2 = Low.cond_br c v in
        Low.position_at_end c bb1;
        let v1 = compile c env e1 in
        let bb1 = Low.insertion_block c in
        Low.position_at_end c bb2;
        let v2 = compile c env e2 in
        let bb2 = Low.insertion_block c in
        let bb = Low.append_block c in
        Low.position_at_end c bb;
        Low.phi c [v1, bb1; v2, bb2]
    | Clet (id, Int, e1, e2) ->
        compile c (M.add id (compile c env e1, Int) env) e2
    | Clet (id, Ptr, e1, e2) ->
        let v = compile c env e1 in
        let bb = Low.insertion_block c in
        Low.position_at_end c (Low.entry_block c);
        let a = Low.alloca c (Low.ptr_type c) in
        Low.position_at_end c bb;
        Low.store c v a;
        let v = compile c (M.add id (a, Ptr) env) e2 in
        Low.store c (Llvm.const_null (Low.ptr_type c)) a;
        v
    | Cprimitive (Pmakeblock, idl) ->
        let vl = List.map (fun id -> toint c id env) idl in
        let v = Low.malloc c (List.length idl) in
        List.iteri (fun i v -> Low.store c v (Low.gep c v [Low.int c i])) vl;
        v
    | Cprimitive (Pgetfield i, [id]) ->
        let v = toptr c id env in
        Low.gep c v [Low.int c i]
    | Cprimitive (Paddint, [id1; id2]) ->
        let v1, _ = find id1 env in
        let v2, _ = find id2 env in
        Low.add c v1 v2
    | Capply (id, idl) ->
        let v = Low.lookup_function c id in
        let vl = List.map (fun id -> fst (find id env)) idl in
        Low.call c v vl

  and compile_tail c env = function
    | Cint _ | Cvar _ | Cprimitive _ | Clabel _ as e -> (* TODO tail call *)
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
    | Clet (id, Ptr, e1, e2) ->
        let v = compile c env e1 in
        let a = Low.alloca c (Low.ptr_type c) in
        Low.store c v a;
        compile_tail c (M.add id (a, Ptr) env) e2
    | Capply _ as e ->
        let v = compile c env e in
        Llvm.set_instruction_call_conv Llvm.CallConv.fast v;
        Low.ret c v

  let compile (Prog (funs, main)) =
    let c = Low.create "miniml" in
    let env =
      List.fold_left (fun env (name, args, ret, _) ->
          let atyps =
            List.map (function (_, Ptr) -> Low.ptr_type c | (_, Int) -> Low.int_type c) args
          in
          let rtype = match ret with Ptr -> Low.ptr_type c | Int -> Low.int_type c in
          let f = Low.define_function c name atyps rtype in
          Llvm.set_function_call_conv Llvm.CallConv.fast f;
          M.add name (f, Int) env
        ) M.empty funs
    in
    List.iter (fun (name, args, _, body) ->
        let (f, _) = find name env in
        let params = Array.to_list (Llvm.params f) in
        let env =
          List.fold_left2 (fun env (id, k) v ->
              Llvm.set_value_name id v;
              M.add id (v, k) env
            ) env args params
        in
        Low.position_at_end c (Llvm.entry_block f);
        compile_tail c env body
      ) funs;
    Low.dump_module c
end

let () =
  let open Closure in
  let prog =
    [
      "test", ["a", Int; "b", Int], Int,
      Clet ("x1", Int, Cint 7,
            Clet ("x2", Int, Cprimitive (Paddint, ["x1"; "b"]),
                  Cprimitive (Paddint, ["a"; "x2"])))
    ]
  in
  Llvmgen.compile (Prog (prog, ""))
