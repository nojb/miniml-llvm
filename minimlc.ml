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
  | Psubint

type kind =
  | Ptr
  | Int

let string_of_kind = function
  | Ptr -> "ptr"
  | Int -> "int"

let string_of_primitive = function
  | Pmakeblock -> "makeblock"
  | Pgetfield i -> Printf.sprintf "getfield %d" i
  | Paddint -> "+"
  | Pmulint -> "*"
  | Psubint -> "-"

module M = Map.Make (String)

let find id env =
  try M.find id env with Not_found -> failwith "find: %S not found" id

module Knf = struct
  type knf =
    | Kint of int
    | Kvar of string
    | Kifthenelse of string * knf * knf
    | Klet of string * kind * knf * knf
    | Kletrec of (string * (string * kind) * kind * knf) list * knf
    | Kapply of string * string list
    | Kprimitive of primitive * string list
end

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

  type value =
    | Vint of int
    | Vtuple of value list
    | Vfun of (value list -> value)
    | Vproxy of value ref

  let rec print_value ppf = function
    | Vint n ->
        Format.pp_print_int ppf n
    | Vtuple vl ->
        Format.fprintf ppf "@[<2>(%a)@]" print_values vl
    | Vfun _ ->
        Format.pp_print_string ppf "<fun>"
    | Vproxy r ->
        print_value ppf !r

  and print_values ppf = function
    | [] -> ()
    | v :: [] -> print_value ppf v
    | v :: vl -> Format.fprintf ppf "%a@ %a" print_value v print_values vl

  let rec eval env = function
    | Cint n -> Vint n
    | Clabel id | Cvar id -> find id env
    | Cifthenelse (id, e1, e2) ->
        let n = match find id env with
          | Vint n -> n
          | _ -> assert false
        in
        if n = 0 then eval env e2 else eval env e1
    | Clet (id, _, e1, e2) ->
        eval (M.add id (eval env e1) env) e2
    | Capply (id, idl) ->
        let f = match find id env with
          | Vfun f
          | Vproxy {contents = Vfun f} -> f
          | _ -> assert false
        in
        f (List.map (fun id -> find id env) idl)
    | Cprimitive (Pmakeblock, idl) ->
        Vtuple (List.map (fun id -> find id env) idl)
    | Cprimitive (Pgetfield i, [id]) ->
        let l = match find id env with
          | Vtuple l ->  l
          | _ -> assert false
        in
        List.nth l i
    | Cprimitive (Paddint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 + n2)
    | Cprimitive (Pmulint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 * n2)
    | Cprimitive (Psubint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 - n2)
    | Cprimitive _ ->
        assert false

  let eval_program (Prog (funs, main)) =
    let env =
      List.fold_left (fun env (name, _, _, _) -> M.add name (Vproxy (ref (Vint 0))) env)
        M.empty funs
    in
    List.iter (fun (name, args, _, body) ->
        let f vl =
          assert (List.length vl = List.length args);
          let env = List.fold_left2 (fun env (id, _) v -> M.add id v env) env args vl in
          eval env body
        in
        let r = match M.find name env with
          | Vproxy r -> r
          | _ -> assert false
        in
        r := Vfun f;
      ) funs;
    eval env (Capply (main, []))

  let rec print ppf = function
    | Cint n ->
        Format.pp_print_int ppf n
    | Clabel id ->
        Format.fprintf ppf "#%s" id
    | Cvar id ->
        Format.pp_print_string ppf id
    | Cifthenelse (id, e1, e2) ->
        Format.fprintf ppf "@[<2>(if %s@ %a@ %a)@]" id print e1 print e2
    | Clet (id, k, e1, e2) ->
        Format.fprintf ppf "@[<2>(let (%s %s@ %a)@ %a)@]" id (string_of_kind k) print e1 print e2
    | Capply (id, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" id print_args idl
    | Cprimitive (prim, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" (string_of_primitive prim) print_args idl

  and print_args ppf = function
    | [] -> ()
    | x :: xs -> Format.fprintf ppf "@ %s%a" x print_args xs

  let rec print_params ppf = function
    | [] -> ()
    | (x, k) :: [] ->
        Format.fprintf ppf "%s %s" x (string_of_kind k)
    | (x, k) :: xs ->
        Format.fprintf ppf "%s %s@ %a" x (string_of_kind k) print_params xs

  let print_fun ppf (name, params, _, body) =
    Format.fprintf ppf "@[<2>(%s@ (%a)@ %a)@]" name print_params params print body

  let rec print_funs ppf = function
    | [] -> ()
    | f :: [] ->
        print_fun ppf f
    | f :: funs ->
        Format.fprintf ppf "%a@ %a" print_fun f print_funs funs

  let print_program ppf (Prog (funs, main)) =
    Format.fprintf ppf "@[<2>(letrec@ @[<v>%a@,(%s)@])@]" print_funs funs main

  open Knf

  let rec compile = function
    | _ -> failwith "Closure.compile: not implemented"
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
  val mul : t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
  val sub : t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
  val call : t -> Llvm.llvalue -> Llvm.llvalue list -> Llvm.llvalue
  val malloc : t -> int -> Llvm.llvalue
  val llmodule : t -> Llvm.llmodule
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
  let mul c v1 v2 = Llvm.build_mul v1 v2 "" c.b
  let sub c v1 v2 = Llvm.build_sub v1 v2 "" c.b
  let call c v vl = Llvm.build_call v (Array.of_list vl) "" c.b
  let malloc c n =
    let t = Llvm.function_type (ptr_type c) [| Llvm.i32_type c.c |] in
    let f = Llvm.declare_function "malloc" t c.m in
    Llvm.build_call f [| Llvm.const_int (Llvm.i32_type c.c) (n * Sys.word_size / 8) |] "" c.b
  let llmodule c = c.m
end

module Llvmgen = struct
  open Closure

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
    | Capply (id, idl) ->
        let v = Low.lookup_function c id in
        let vl = List.map (fun id -> fst (find id env)) idl in
        Low.call c v vl
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
    | Cprimitive (Pmulint, [id1; id2]) ->
        let v1, _ = find id1 env in
        let v2, _ = find id2 env in
        Low.mul c v1 v2
    | Cprimitive (Psubint, [id1; id2]) ->
        let v1, _ = find id1 env in
        let v2, _ = find id2 env in
        Low.sub c v1 v2
    | Cprimitive _ ->
        assert false

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
        Llvm.set_tail_call true v;
        Low.ret c v

  let compile (Prog (funs, main) as prog) =
    Format.printf "@[Compiling...@\n%a@]@." print_program prog;
    Format.printf "@[Running...%a\n@]@." print_value (eval_program prog);
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
    Low.dump_module c;
    Low.llmodule c
end

(*

Example: factorial

(letrec
   (fact (n int) (if n (\* n (fact (- n 1))) 1))
   (fact1 () (fact 10))
   (fact1))

*)

let fact n =
  let open Closure in
  let fact =
    Cifthenelse
      ("n", Clet
         ("c1", Int, Cint 1, Clet
            ("x1", Int, Cprimitive (Psubint, ["n"; "c1"]), Clet
               ("x2", Int, Capply ("fact", ["x1"]), Cprimitive (Pmulint, ["n"; "x2"])))),
       Cint 1)
  in
  let factn n = Clet ("x", Int, Cint n, Capply ("fact", ["x"])) in
  let prog =
    [
      "fact", ["n", Int], Int, fact;
      "factn", [], Int, factn n
    ]
  in
  let m = Llvmgen.compile (Prog (prog, "factn")) in
  if not (Llvm_executionengine.initialize ()) then
    failwith "Execution engine could not be initialized";
  let ee = Llvm_executionengine.create m in
  let f =
    Llvm_executionengine.get_function_address "factn"
      Ctypes.(Foreign.funptr (void @-> returning int)) ee
  in
  let n = f () in
  let c = Llvm.module_context m in
  Llvm_executionengine.dispose ee;
  Llvm.dispose_context c;
  n

let () =
  Printf.printf "fact (10) = %d\n%!" (fact 10)
