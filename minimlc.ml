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
  | Pmalloc
  | Paddint
  | Pmulint
  | Psubint
  | Pload
  | Pstore
  | Palloca
  | Pindex

let string_of_primitive = function
  | Pmalloc -> "malloc"
  | Paddint -> "+"
  | Pmulint -> "*"
  | Psubint -> "-"
  | Pload -> "load"
  | Pstore -> "store"
  | Palloca -> "alloca"
  | Pindex -> "index"

let gentmp =
  let count = ref 0 in
  fun () -> let i = !count in incr count; Printf.sprintf "T%d" i

module M = Map.Make (String)
module S = Set.Make (String)

let find id env =
  try M.find id env with Not_found -> failwith "find: %S not found" id

type type_ =
  | Tint
  | Tpointer of type_
  | Tstruct of string

let rec print_type ppf = function
  | Tint -> Format.pp_print_string ppf "int"
  | Tpointer t -> Format.fprintf ppf "%a*" print_type t
  | Tstruct id -> Format.pp_print_string ppf id

module Knf = struct
  type knf =
    | Kint of nativeint
    | Knil of string
    | Kvar of string
    | Kifthenelse of string * knf * knf
    | Klet of string * type_ * knf * knf
    | Kletrec of (string * (string * type_) list * type_ * knf) list * knf
    | Kapply of string * string list
    | Kprimitive of primitive * string list
    | Kwhile of knf * knf
    | Kbreak

  (*
  type value =
    | Vint of int
    | Vstring of string
    | Varray of value array
    | Vstruct of value array

  let rec print_value ppf = function
    | Vint n ->
        Format.pp_print_int ppf n
    | Vstring s ->
        Format.fprintf ppf "%S" s
    | Varray _
    | Vstruct _ ->
        assert false

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
*)

  let rec print ppf = function
    | Kint n ->
        Format.fprintf ppf "%nd" n
    | Knil _ ->
        Format.pp_print_string ppf "nil"
    | Kvar id ->
        Format.pp_print_string ppf id
    | Kifthenelse (id, e1, e2) ->
        Format.fprintf ppf "@[<2>(if %s@ %a@ %a)@]" id print e1 print e2
    | Klet (id, t, e1, e2) ->
        Format.fprintf ppf "@[<2>(let (%s@ %a@ %a)@ %a)@]" id print_type t print e1 print e2
    | Kletrec (funs, e) ->
        Format.fprintf ppf "@[<2>(letrec@ @[<v>%a@ %a@])@]" print_funs funs print e
    | Kapply (id, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" id print_args idl
    | Kprimitive (prim, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" (string_of_primitive prim) print_args idl
    | Kwhile (e1, e2) ->
        Format.fprintf ppf "@[<2>(while@ %a@ %a)@]" print e1 print e2
    | Kbreak ->
        Format.pp_print_string ppf "(break)"

  and print_args ppf = function
    | [] -> ()
    | x :: xs -> Format.fprintf ppf "@ %s%a" x print_args xs

  and print_params ppf = function
    | [] -> ()
    | (x, t) :: [] ->
        Format.fprintf ppf "%s@ %a" x print_type t
    | (x, t) :: xs ->
        Format.fprintf ppf "%s@ %a@ %a" x print_type t print_params xs

  and print_fun ppf (name, params, _, body) =
    Format.fprintf ppf "@[<2>(%s@ (%a)@ %a)@]" name print_params params print body

  and print_funs ppf = function
    | [] -> ()
    | f :: [] ->
        print_fun ppf f
    | f :: funs ->
        Format.fprintf ppf "%a@ %a" print_fun f print_funs funs

  let rec fv = function
    | Kint _ | Knil _ -> S.empty
    | Kvar id -> S.singleton id
    | Kifthenelse (id, e1, e2) -> S.add id (S.union (fv e1) (fv e2))
    | Klet (id, _, e1, e2) -> S.union (fv e1) (S.remove id (fv e2))
    | Kletrec (funs, e) ->
        List.fold_left S.union (fv e) (List.map fv_fun funs)
    | Kapply (_, idl)
    | Kprimitive (_, idl) ->
        List.fold_left (fun s id -> S.add id s) S.empty idl
    | Kwhile (e1, e2) ->
        S.union (fv e1) (fv e2)
    | Kbreak ->
        S.empty

  and fv_fun (_, args, _, body) =
    List.fold_left (fun s (id, _) -> S.remove id s) (fv body) args
end

module Closure = struct
  type clambda =
    | Cint of nativeint
    | Cnil of string
    | Cvar of string
    | Cifthenelse of string * clambda * clambda
    | Clet of string * type_ * clambda * clambda
    | Capply of string * string list
    | Cprimitive of primitive * string list
    | Cwhile of clambda * clambda
    | Cbreak
  type program =
    | Prog of (string * (string * type_) list * type_ * clambda) list * clambda

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

  (*
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
    | Cprimitive (Pmake, idl) ->
        Vtuple (List.map (fun id -> find id env) idl)
(*    | Cprimitive (Pgetfield i, [id]) ->
        let l = match find id env with
          | Vtuple l ->  l
          | _ -> assert false
        in
        List.nth l i *)
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
  let rec print ppf = function
    | Cint n ->
        Format.fprintf ppf "%nd" n
    | Cnil _ ->
        Format.fprintf ppf "nil"
    | Cvar id ->
        Format.pp_print_string ppf id
    | Cifthenelse (id, e1, e2) ->
        Format.fprintf ppf "@[<2>(if %s@ %a@ %a)@]" id print e1 print e2
    | Clet (id, t, e1, e2) ->
        Format.fprintf ppf "@[<2>(let (%s@ %a@ %a)@ %a)@]" id print_type t print e1 print e2
    | Capply (id, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" id print_args idl
    | Cprimitive (prim, idl) ->
        Format.fprintf ppf "@[<2>(%s%a)@]" (string_of_primitive prim) print_args idl
    | Cwhile (e1, e2) ->
        Format.fprintf ppf "@[<2>(while@ %a@ %a)@]" print e1 print e2
    | Cbreak ->
        Format.pp_print_string ppf "(break)"

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
    Format.fprintf ppf "@[<2>(letrec@ @[<v>%a@ %a@])@]" print_funs funs print main

  open Knf

  let all_funs : (string * (string * type_) list * type_ * clambda) list ref = ref []

  let rec transl clos env = function
    | Kint n ->
        Cint n
    | Knil id ->
        Cnil id
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
    | Kwhile (e1, e2) ->
        Cwhile (transl clos env e1, transl clos env e2)
    | Kbreak ->
        Cbreak

  let transl_program e =
    all_funs := [];
    let e = transl M.empty M.empty e in
    Prog (!all_funs, e)
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
  val inttoptr : t -> Llvm.llvalue -> Llvm.lltype -> Llvm.llvalue
  val ptrtoint : t -> Llvm.llvalue -> Llvm.llvalue
  val ret : t -> Llvm.llvalue -> unit
  val icmp : t -> Llvm.Icmp.t -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue
  val phi : t -> (Llvm.llvalue * Llvm.llbasicblock) list -> Llvm.llvalue
  val alloca : t -> Llvm.lltype -> Llvm.llvalue
  val cond_br : t -> Llvm.llvalue -> Llvm.llbasicblock * Llvm.llbasicblock
  val br : t -> Llvm.llbasicblock -> unit
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
  val pointercast : t -> Llvm.llvalue -> Llvm.lltype -> Llvm.llvalue
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
  let inttoptr c v t = Llvm.build_inttoptr v t "" c.b
  let ptrtoint c v = Llvm.build_ptrtoint v (int_type c) "" c.b
  let ret c v = ignore (Llvm.build_ret v c.b)
  let icmp c comp v1 v2 = Llvm.build_icmp comp v1 v2 "" c.b
  let phi c l = Llvm.build_phi l "" c.b
  let alloca c t =
    let b =
      Llvm.builder_at_end c.c (Llvm.entry_block (Llvm.block_parent (Llvm.insertion_block c.b)))
    in
    Llvm.build_alloca t "" b
  let cond_br c v =
    let f = Llvm.block_parent (Llvm.insertion_block c.b) in
    let bb1 = Llvm.append_block c.c "" f in
    let bb2 = Llvm.append_block c.c "" f in
    ignore (Llvm.build_cond_br v bb1 bb2 c.b);
    bb1, bb2
  let br c bb = ignore (Llvm.build_br bb c.b)
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
  let pointercast c v t = Llvm.build_pointercast v t "" c.b
end

module Llvmgen = struct
  open Closure

  let rec compile c env = function
    | Cint n ->
        Low.int c (Nativeint.to_int n) (* FIXME *)
    | Cnil _ ->
        assert false
    | Cvar id ->
        find id env
    | Cifthenelse (id, e1, e2) ->
        let v = find id env in
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
    | Clet (id, _, e1, e2) ->
        compile c (M.add id (compile c env e1) env) e2
    | Capply (id, idl) ->
        let v = Low.lookup_function c id in
        let vl = List.map (fun id -> find id env) idl in
        Low.call c v vl
    | Cprimitive (Pmalloc, idl) ->
        let v = Low.malloc c (List.length idl) in
        let vl = List.map (fun id -> find id env) idl in
        List.iteri (fun i v' -> Low.store c v' (Low.gep c v [Low.int c i])) vl;
        Low.ptrtoint c v
    | Cprimitive (Paddint, [id1; id2]) ->
        let v1 = find id1 env in
        let v2 = find id2 env in
        Low.add c v1 v2
    | Cprimitive (Pmulint, [id1; id2]) ->
        let v1 = find id1 env in
        let v2 = find id2 env in
        Low.mul c v1 v2
    | Cprimitive (Psubint, [id1; id2]) ->
        let v1 = find id1 env in
        let v2 = find id2 env in
        Low.sub c v1 v2
    | Cprimitive (Pload, [id]) ->
        Low.load c (find id env)
    | Cprimitive (Pstore, [id1; id2]) ->
        Low.store c (find id1 env) (find id2 env);
        Llvm.undef (Low.int_type c)
    | Cprimitive (Palloca, [id]) ->
        let v = find id env in
        let a = Low.alloca c (Llvm.type_of v) in
        Low.store c v a;
        a
    | Cprimitive (Pindex, [id1; id2]) ->
        let v1 = find id1 env in
        let v2 = find id2 env in
        Low.load c (Low.gep c v1 [v2])
    | Cprimitive _ ->
        assert false
    | Cwhile _ | Cbreak ->
        assert false

  and compile_tail c env = function
    | Cint _ | Cnil _ | Cvar _ | Cprimitive _ as e ->
        Low.ret c (compile c env e)
    | Cifthenelse (id, e1, e2) ->
        let v = find id env in
        let v = Low.icmp c Llvm.Icmp.Ne v (Low.int c 0) in
        let bb1, bb2 = Low.cond_br c v in
        Low.position_at_end c bb1;
        compile_tail c env e1;
        Low.position_at_end c bb2;
        compile_tail c env e2
    | Clet (id, _, e1, e2) ->
        compile_tail c (M.add id (compile c env e1) env) e2
(*    | Clet (id, Ptr, e1, e2) ->
        let v = compile c env e1 in
        let a = Low.alloca c (Low.int_type c) in
        Low.store c v a;
        let a = Low.ptrtoint c a in
        compile_tail c (M.add id (a, Ptr) env) e2 *)
    | Capply _ as e ->
        let v = compile c env e in
        Llvm.set_instruction_call_conv Llvm.CallConv.fast v;
        Llvm.set_tail_call true v;
        Low.ret c v
    | Cwhile _ ->
        assert false
    | Cbreak ->
        assert false

  let compile_fun c env f body =
    Low.position_at_end c (Llvm.entry_block f);
    let bb = Low.append_block c in
    Low.position_at_end c bb;
    compile_tail c env body;
    Low.position_at_end c (Llvm.entry_block f);
    Low.br c bb

  let compile_program (Prog (funs, main)) =
    let c = Low.create "miniml" in
    let env =
      List.fold_left (fun env (name, args, ret, _) ->
          let atyps = List.map (fun _ -> Low.int_type c) args in
          let rtype = Low.int_type c in
          let f = Low.define_function c name atyps rtype in
          Llvm.set_function_call_conv Llvm.CallConv.fast f;
          M.add name f env
        ) M.empty funs
    in
    List.iter (fun (name, args, _, body) ->
        let f = find name env in
        let params = Array.to_list (Llvm.params f) in
        Low.position_at_end c (Llvm.entry_block f);
        let env =
          List.fold_left2 (fun env (id, _) v ->
              Llvm.set_value_name id v;
(*              let v = match k with
                | Ptr ->
                    let a = Low.alloca c (Low.int_type c) in
                    Low.store c v a;
                    Llvm.set_value_name id a;
                    Low.ptrtoint c a
                | Int -> v
                in*)
              M.add id v env
            ) env args params
        in
        compile_fun c env f body
      ) funs;
    let mainf = Low.define_function c "main" [] (Low.int_type c) in
    compile_fun c env mainf main;
    Low.llmodule c
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

let adder =
  let open Knf in
  Kletrec
    (["adder", ["n", Tint], Tint, Kletrec
        (["aux", ["m", Tint], Tint, Kprimitive
            (Paddint, ["n"; "m"])], Klet ("u", Tint, Kint 5n, Kapply ("aux", ["u"])))],
     Klet
       ("a", Tint, Kint 3n, Kapply ("adder", ["a"])))

let fact' =
  let open Knf in
  Kletrec
    (["fact", ["n", Tint], Tint, Kifthenelse
        ("n", Klet ("c", Tint, Kint 1n, Klet ("x", Tint, Kprimitive (Psubint, ["n"; "c"]),
                                            Klet ("xx", Tint, Kapply ("fact", ["x"]),
                                                  Kprimitive (Pmulint, ["n"; "xx"])))),
         Kint 1n)], Klet ("u", Tint, Kint 10n, Kapply ("fact", ["u"])))

let run prog =
  Format.printf "%a@.@\n" Knf.print prog;
  let prog = Closure.transl_program prog in
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
            ("x1", Tint, Cprimitive (Psubint, ["n"; "c1"]), Clet
               ("x2", Tint, Capply ("fact", ["x1"]), Cprimitive (Pmulint, ["n"; "x2"])))),
       Cint 1n)
  in
  let prog =
    [
      "fact", ["n", Tint], Tint, fact;
    ]
  in
  let main n = Clet ("x", Tint, Cint n, Capply ("fact", ["x"])) in
  Prog (prog, main n)

let () =
  Printf.printf "Result: %d\n%!" (run adder);
  Printf.printf "Result: %d\n%!" (run fact')
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
