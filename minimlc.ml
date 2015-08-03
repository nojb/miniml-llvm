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
(*
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
  | Pgetfield i -> Printf.sprintf "#%d" i
  | Paddint -> "+"
  | Pmulint -> "*"
  | Psubint -> "-"
*)
let gentmp =
  let count = ref 0 in
  fun () -> let i = !count in incr count; Printf.sprintf "T%d" i

module M = Map.Make (String)
module S = Set.Make (String)

let find id env =
  try M.find id env with Not_found -> failwith "find: %S not found" id
(*
module Knf = struct
  type knf =
    | Kint of int
    | Kvar of string
    | Kifthenelse of string * knf * knf
    | Klet of string * kind * knf * knf
    | Kletrec of (string * (string * kind) list * kind * knf) list * knf
    | Kapply of string * string list
    | Kprimitive of primitive * string list

  type value =
    | Vint of int
    | Vtuple of value list
    | Vfun of (value list -> value) ref

  let rec print_value ppf = function
    | Vint n ->
        Format.pp_print_int ppf n
    | Vtuple vl ->
        Format.fprintf ppf "@[<2>(%a)@]" print_values vl
    | Vfun _ ->
        Format.pp_print_string ppf "<fun>"

  and print_values ppf = function
    | [] -> ()
    | v :: [] -> print_value ppf v
    | v :: vl -> Format.fprintf ppf "%a@ %a" print_value v print_values vl

  let rec eval env = function
    | Kint n -> Vint n
    | Kvar id -> find id env
    | Kifthenelse (id, e1, e2) ->
        let n = match find id env with
          | Vint n -> n
          | _ -> assert false
        in
        if n = 0 then eval env e2 else eval env e1
    | Klet (id, _, e1, e2) ->
        eval (M.add id (eval env e1) env) e2
    | Kletrec (funs, e) ->
        let env =
          List.fold_left (fun env (name, _, _, _) -> M.add name (Vfun (ref (fun _ -> Vint 0))) env)
            env funs
        in
        List.iter (fun (name, args, _, body) ->
            let f vl =
              assert (List.length vl = List.length args);
              let env = List.fold_left2 (fun env (id, _) v -> M.add id v env) env args vl in
              eval env body
            in
            let r = match M.find name env with
              | Vfun r -> r
              | _ -> assert false
            in
            r := f;
          ) funs;
        eval env e
    | Kapply (id, idl) ->
        let f = match find id env with
          | Vfun r -> !r
          | _ -> assert false
        in
        f (List.map (fun id -> find id env) idl)
    | Kprimitive (Pmakeblock, idl) ->
        Vtuple (List.map (fun id -> find id env) idl)
    | Kprimitive (Pgetfield i, [id]) ->
        let l = match find id env with
          | Vtuple l ->  l
          | _ -> assert false
        in
        List.nth l i
    | Kprimitive (Paddint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 + n2)
    | Kprimitive (Pmulint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 * n2)
    | Kprimitive (Psubint, [id1; id2]) ->
        let n1, n2 = match find id1 env, find id2 env with
          | Vint n1, Vint n2 -> n1, n2
          | _ -> assert false
        in
        Vint (n1 - n2)
    | Kprimitive _ ->
        assert false

  let rec print ppf = function
    | Kint n ->
        Format.pp_print_int ppf n
    | Kvar id ->
        Format.pp_print_string ppf id
    | Kifthenelse (id, e1, e2) ->
        Format.fprintf ppf "@[<2>(if %s@ %a@ %a)@]" id print e1 print e2
    | Klet (id, k, e1, e2) ->
        Format.fprintf ppf "@[<2>(let (%s %s@ %a)@ %a)@]" id (string_of_kind k) print e1 print e2
    | Kletrec (funs, e) ->
        Format.fprintf ppf "@[<2>(letrec@ @[<v>%a@ %a@])@]" print_funs funs print e
    | Kapply (id, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" id print_args idl
    | Kprimitive (prim, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" (string_of_primitive prim) print_args idl

  and print_args ppf = function
    | [] -> ()
    | x :: xs -> Format.fprintf ppf "@ %s%a" x print_args xs

  and print_params ppf = function
    | [] -> ()
    | (x, k) :: [] ->
        Format.fprintf ppf "%s %s" x (string_of_kind k)
    | (x, k) :: xs ->
        Format.fprintf ppf "%s %s@ %a" x (string_of_kind k) print_params xs

  and print_fun ppf (name, params, _, body) =
    Format.fprintf ppf "@[<2>(%s@ (%a)@ %a)@]" name print_params params print body

  and print_funs ppf = function
    | [] -> ()
    | f :: [] ->
        print_fun ppf f
    | f :: funs ->
        Format.fprintf ppf "%a@ %a" print_fun f print_funs funs

  let rec fv = function
    | Kint _ -> S.empty
    | Kvar id -> S.singleton id
    | Kifthenelse (id, e1, e2) -> S.add id (S.union (fv e1) (fv e2))
    | Klet (id, _, e1, e2) -> S.union (fv e1) (S.remove id (fv e2))
    | Kletrec (funs, e) ->
        List.fold_left S.union (fv e) (List.map fv_fun funs)
    | Kapply (_, idl)
    | Kprimitive (_, idl) ->
        List.fold_left (fun s id -> S.add id s) S.empty idl

  and fv_fun (_, args, _, body) =
    List.fold_left (fun s (id, _) -> S.remove id s) (fv body) args
end
             *)
module Closure = struct
  type typ =
    | Tint
    | Tpointer of typ

  type primitive =
    | Padd
    | Psub
    | Pmul
    | Palloca of typ
    | Pload
    | Pstore
    | Pgep

  type clambda =
    | Cint of nativeint
    | Cvar of string
    | Cifthenelse of string * clambda * clambda
    | Clet of string * typ * clambda * clambda
    | Capply of string * string list
    | Cprimitive of primitive * string list

  type program =
    | Prog of (string * (string * typ) list * typ * clambda) list * string

  (*
  type value =
    | Vint of int
    | Vtuple of value list

  let rec print_value ppf = function
    | Vint n ->
        Format.pp_print_int ppf n
    | Vtuple vl ->
        Format.fprintf ppf "@[<2>(%a)@]" print_values vl

  and print_values ppf = function
    | [] -> ()
    | v :: [] -> print_value ppf v
    | v :: vl -> Format.fprintf ppf "%a@ %a" print_value v print_values vl

  let all_funs = ref M.empty

  let rec eval env = function
    | Cint n -> Vint n
    | Cvar id -> find id env
    | Cifthenelse (id, e1, e2) ->
        let n = match find id env with
          | Vint n -> n
          | _ -> assert false
        in
        if n = 0 then eval env e2 else eval env e1
    | Clet (id, _, e1, e2) ->
        eval (M.add id (eval env e1) env) e2
    | Capply (id, idl) ->
        let f = find id !all_funs in
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
    all_funs := M.empty;
    List.iter (fun (id, args, _, body) ->
        let f vl =
          assert (List.length vl = List.length args);
          let env = List.fold_left2 (fun env (id, _) v -> M.add id v env) M.empty args vl in
          eval env body
        in
        all_funs := M.add id f !all_funs
      ) funs;
    eval M.empty main
*)

  let rec print_type ppf = function
    | Tint -> Format.fprintf ppf "int"
    | Tpointer t -> Format.fprintf ppf "%a*" print_type t

  let print_primitive ppf = function
    | Padd -> Format.fprintf ppf "+"
    | Psub -> Format.fprintf ppf "-"
    | Pmul -> Format.fprintf ppf "*"
    | Palloca t -> Format.fprintf ppf "alloca@ %a" print_type t
    | Pload -> Format.fprintf ppf "load"
    | Pstore -> Format.fprintf ppf "store"
    | Pgep -> Format.fprintf ppf "gep"

  let rec print ppf = function
    | Cint n ->
        Format.fprintf ppf "%nd" n
    | Cvar id ->
        Format.pp_print_string ppf id
    | Cifthenelse (id, e1, e2) ->
        Format.fprintf ppf "@[<2>(if %s@ %a@ %a)@]" id print e1 print e2
    | Clet (id, t, e1, e2) ->
        Format.fprintf ppf "@[<2>(let (%s@ %a@ %a)@ %a)@]" id print_type t print e1 print e2
    | Capply (id, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" id print_args idl
    | Cprimitive (prim, idl) ->
        Format.fprintf ppf "@[<2>(%a%a)@]" print_primitive prim print_args idl

  and print_args ppf = function
    | [] -> ()
    | x :: xs -> Format.fprintf ppf "@ %s%a" x print_args xs

  let rec print_params ppf = function
    | [] -> ()
    | (x, t) :: [] ->
        Format.fprintf ppf "%s@ %a" x print_type t
    | (x, t) :: xs ->
        Format.fprintf ppf "%s@ %a@ %a" x print_type t print_params xs

  let print_fun ppf (name, params, _, body) =
    Format.fprintf ppf "@[<2>(%s@ (%a)@ %a)@]" name print_params params print body

  let rec print_funs ppf = function
    | [] -> ()
    | f :: [] ->
        print_fun ppf f
    | f :: funs ->
        Format.fprintf ppf "%a@ %a" print_fun f print_funs funs

  let print_program ppf (Prog (funs, main)) =
    Format.fprintf ppf "@[<2>(letrec@ @[<v>%a@ (%s)@])@]" print_funs funs main

(*  open Knf

  let all_funs : (string * (string * kind) list * kind * clambda) list ref = ref []

  let rec transl clos env = function
    | Kint n ->
        Cint n
    | Kvar id ->
        Cvar id
    | Kifthenelse (id, e1, e2) ->
        Cifthenelse (id, transl clos env e1, transl clos env e2)
    | Klet (id, k, e1, e2) ->
        Clet (id, k, transl clos env e1, transl clos (M.add id k env) e2)
    | Kletrec (funs, e) ->
        let fvs = List.fold_left S.union S.empty (List.map fv_fun funs) in
        let fvs = S.elements fvs in
        let fvs' = List.map (fun fv -> fv, find fv env) fvs in
        let clos = List.fold_left (fun clos (id, _, _, _) -> M.add id fvs clos) clos funs in
        List.iter (fun (id, args, k, body) ->
            let env = List.fold_left (fun env (id, k) -> M.add id k env) env args in
            let body = transl clos env body in
            all_funs := (id, fvs' @ args, k, body) :: !all_funs
          ) funs;
        transl clos env e
    | Kapply (id, idl) ->
        let fvs = M.find id clos in
        Capply (id, fvs @ idl)
    | Kprimitive (prim, idl) ->
        Cprimitive (prim, idl)

  let transl_program e =
    all_funs := [];
    let e = transl M.empty M.empty e in
    Prog (!all_funs, e) *)
end

module Llvmgen = struct
  open Closure

  type env =
    { m : Llvm.llmodule;
      b : Llvm.llbuilder;
      c : Llvm.llcontext;
      e : Llvm.llvalue M.t }

  let find id env = find id env.e
  let add id x env = {env with e = M.add id x env.e}

  let rec compile_type env = function
    | Tint -> Llvm.i32_type env.c
    | Tpointer t -> Llvm.pointer_type (compile_type env t)

  let rec compile env = function
    | Cint n ->
        Llvm.const_of_int64 (Llvm.i32_type env.c) (Int64.of_nativeint n) true
    | Cvar id ->
        find id env
    | Cifthenelse (id, e1, e2) ->
        let v = find id env in
        let zero = Llvm.const_int (Llvm.i32_type env.c) 0 in
        let v = Llvm.build_icmp Llvm.Icmp.Ne v zero "" env.b in
        let f = Llvm.block_parent (Llvm.insertion_block env.b) in
        let bb1 = Llvm.append_block env.c "" f in
        let bb2 = Llvm.append_block env.c "" f in
        ignore (Llvm.build_cond_br v bb1 bb2 env.b);
        Llvm.position_at_end bb1 env.b;
        let v1 = compile env e1 in
        let bb1 = Llvm.insertion_block env.b in
        Llvm.position_at_end bb2 env.b;
        let v2 = compile env e2 in
        let bb2 = Llvm.insertion_block env.b in
        let bb = Llvm.append_block env.c "" f in
        Llvm.position_at_end bb env.b;
        Llvm.build_phi [v1, bb1; v2, bb2] "" env.b
    | Clet (id, _, e1, e2) ->
        compile (add id (compile env e1) env) e2
(*    | Clet (id, Ptr, e1, e2) ->
        let v = compile c env e1 in
        let a = Low.alloca c (Low.int_type c) in
        Low.store c v a;
        let a' = Low.ptrtoint c a in
        let v = compile c (M.add id (a', Ptr) env) e2 in
        Low.store c (Llvm.const_null (Low.int_type c)) a;
        v *)
    | Capply (id, idl) ->
        let v = match Llvm.lookup_function id env.m with
          | None -> failwith "Function %S not found" id
          | Some f -> f
        in
        let vl = List.map (fun id -> find id env) idl in
        Llvm.build_call v (Array.of_list vl) "" env.b
    | Cprimitive (Padd, [id1; id2]) ->
        Llvm.build_add (find id1 env) (find id2 env) "" env.b
    | Cprimitive (Psub, [id1; id2]) ->
        Llvm.build_sub (find id1 env) (find id2 env) "" env.b
    | Cprimitive (Pmul, [id1; id2]) ->
        Llvm.build_mul (find id1 env) (find id2 env) "" env.b
    | Cprimitive (Palloca t, []) ->
        Llvm.build_alloca (compile_type env t) "" env.b
    | Cprimitive (Pload, [id]) ->
        Llvm.build_load (find id env) "" env.b
    | Cprimitive (Pstore, [idv; idp]) ->
        Llvm.build_store (find idv env) (find idp env) env.b
(*    | Cprimitive (Pmakeblock, idl) ->
        let v = Low.malloc c (List.length idl) in
        let vl = List.map (var c env) idl in
        List.iteri (fun i v' -> Low.store c v' (Low.gep c v [Low.int c i])) vl;
        Low.ptrtoint c v
    | Cprimitive (Pgetfield i, [id]) ->
        let v = var c env id in
        let v = Low.inttoptr c v (Low.ptr_type c) in
        Low.load c (Low.gep c v [Low.int c i])
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
        Low.sub c v1 v2 *)
    | Cprimitive _ ->
        assert false

  and compile_tail env = function
    | Cint _ | Cvar _ | Cprimitive _ as e -> (* TODO tail call *)
        ignore (Llvm.build_ret (compile env e) env.b)
    | Cifthenelse (id, e1, e2) ->
        let v = find id env in
        let zero = Llvm.const_int (Llvm.i32_type env.c) 0 in
        let v = Llvm.build_icmp Llvm.Icmp.Ne v zero "" env.b in
        let f = Llvm.block_parent (Llvm.insertion_block env.b) in
        let bb1 = Llvm.append_block env.c "" f in
        let bb2 = Llvm.append_block env.c "" f in
        ignore (Llvm.build_cond_br v bb1 bb2 env.b);
        Llvm.position_at_end bb1 env.b;
        compile_tail env e1;
        Llvm.position_at_end bb2 env.b;
        compile_tail env e2
    | Clet (id, _, e1, e2) ->
        compile_tail (add id (compile env e1) env) e2
(*    | Clet (id, Ptr, e1, e2) ->
        let v = compile c env e1 in
        let a = Low.alloca c (Low.int_type c) in
        Low.store c v a;
        let a = Low.ptrtoint c a in
        compile_tail c (M.add id (a, Ptr) env) e2 *)
    | Capply _ as e ->
        let v = compile env e in
        Llvm.set_instruction_call_conv Llvm.CallConv.fast v;
        Llvm.set_tail_call true v;
        ignore (Llvm.build_ret v env.b)

  let compile_fun env f body =
    Llvm.position_at_end (Llvm.entry_block f) env.b;
    let bb = Llvm.append_block env.c "" f in
    Llvm.position_at_end bb env.b;
    compile_tail env body;
    Llvm.position_at_end (Llvm.entry_block f) env.b;
    ignore (Llvm.build_br bb env.b)

  let compile_program (Prog (funs, main)) =
    let c = Llvm.create_context () in
    let m = Llvm.create_module c "miniml" in
    let b = Llvm.builder c in
    let env = {c; m; b; e = M.empty} in
    List.iter (fun (name, args, ret, _) ->
        let atyps = List.map (fun (_, t) -> compile_type env t) args in
        let rtype = compile_type env ret in
        let f =
          Llvm.define_function name
            (Llvm.function_type rtype (Array.of_list atyps)) env.m
        in
        Llvm.set_function_call_conv Llvm.CallConv.fast f
      ) funs;
    List.iter (fun (name, args, k, body) ->
        let f = match Llvm.lookup_function name env.m with
          | None -> failwith "Function %S not found" name
          | Some f -> f
        in
        let params = Array.to_list (Llvm.params f) in
        Llvm.position_at_end (Llvm.entry_block f) env.b;
        let env =
          List.fold_left2 (fun env (id, _) v ->
              Llvm.set_value_name id v;
              add id v env
            ) env args params
        in
        compile_fun env f body
      ) funs;
    let mainf =
      Llvm.define_function "main" (Llvm.function_type (Llvm.i32_type env.c) [| |]) env.m
    in
    Llvm.position_at_end (Llvm.entry_block mainf) env.b;
    let f = match Llvm.lookup_function main env.m with
      | None -> failwith "Function %S not found" main
      | Some f -> f
    in
    ignore (Llvm.build_ret (Llvm.build_call f [| |] "" env.b) env.b);
    env.m
end

(*

Example: factorial

(letrec
   (fact (n int) (if n (\* n (fact (- n 1))) 1))
   (fact1 () (fact 10))
   (fact1))

let rec adder n =
  let rec aux m = n + m in aux
in
(adder 3) 5

*)

(*
let adder =
  let open Knf in
  Kletrec
    (["adder", ["n", Int], Int, Kletrec
        (["aux", ["m", Int], Int, Kprimitive
            (Paddint, ["n"; "m"])], Klet ("u", Int, Kint 5, Kapply ("aux", ["u"])))],
     Klet
       ("a", Int, Kint 3, Kapply ("adder", ["a"])))

let fact' =
  let open Knf in
  Kletrec
    (["fact", ["n", Int], Int, Kifthenelse
        ("n", Klet ("c", Int, Kint 1, Klet ("x", Int, Kprimitive (Psubint, ["n"; "c"]),
                                            Klet ("xx", Int, Kapply ("fact", ["x"]),
                                                  Kprimitive (Pmulint, ["n"; "xx"])))),
         Kint 1)], Klet ("u", Int, Kint 10, Kapply ("fact", ["u"])))
*)
let run prog =
  (* Format.printf "%a@.@\n" Knf.print prog; *)
  (* let prog = Closure.transl_program prog in *)
  Format.printf "%a@.@\n" Closure.print_program prog;
  let m = Llvmgen.compile_program prog in
  Llvm.dump_module m;
  if not (Llvm_executionengine.initialize ()) then
    failwith "Execution engine could not be initialized";
  let ee = Llvm_executionengine.create m in
  let f =
    Llvm_executionengine.get_function_address "main"
      Ctypes.(Foreign.funptr (void @-> returning int)) ee
  in
  let n = f () in
  let c = Llvm.module_context m in
  Llvm_executionengine.dispose ee;
  Llvm.dispose_context c;
  n

let fact n =
  let open Closure in
  let fact =
    Cifthenelse
      ("n", Clet
         ("c1", Tint, Cint 1n, Clet
            ("x1", Tint, Cprimitive (Psub, ["n"; "c1"]), Clet
               ("x2", Tint, Capply ("fact", ["x1"]), Cprimitive (Pmul, ["n"; "x2"])))),
       Cint 1n)
  in
  let fact10 = Clet ("x", Tint, Cint 10n, Capply ("fact", ["x"])) in
  let prog =
    [
      "fact", ["n", Tint], Tint, fact;
      "fact10", [], Tint, fact10;
    ]
  in
  Prog (prog, "fact10")

let () =
  Printf.printf "Result: %d\n%!" (run (fact 10));
  (* Printf.printf "Result: %d\n%!" (run fact') *)
  (* run (fact 10) *)

(*
    Format.printf "@[%a@]@." print_program prog;
  Format.printf "@[%a\n@]@." print_value (eval_program prog);
  let m = Llvmgen.compile prog in
  if not (Llvm_executionengine.initialize ()) then
    failwith "Execution engine could not be initialized";
  let ee = Llvm_executionengine.create m in
  let f =
    Llvm_executionengine.get_function_address "main"
      Ctypes.(Foreign.funptr (void @-> returning int)) ee
  in
  let n = f () in
  let c = Llvm.module_context m in
  Llvm_executionengine.dispose ee;
  Llvm.dispose_context c;
  n

let () =
  Printf.printf "fact (10) = %d\n%!" (fact 10)
*)
