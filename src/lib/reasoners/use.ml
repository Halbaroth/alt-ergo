(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module Util = Alt_ergo_lib_util
module Ast = Alt_ergo_lib_ast
open Util.Options
open Format

module SA = Set.Make (struct
    type t = Ast.Expr.t * Ast.Ex.t

    let compare (s1, _) (s2, _) = Ast.Expr.compare s1 s2
  end)

module X = Shostak.Combine
module MX = Shostak.MXH

type t = (Ast.Expr.Set.t * SA.t) MX.t
type r = X.r

let inter_tpl (x1, y1) (x2, y2) =
  Util.Options.exec_thread_yield ();
  (Ast.Expr.Set.inter x1 x2, SA.inter y1 y2)

let union_tpl (x1, y1) (x2, y2) =
  Util.Options.exec_thread_yield ();
  (Ast.Expr.Set.union x1 x2, SA.union y1 y2)

let one, _ =
  X.make (Ast.Expr.mk_term (Ast.Sy.name "@bottom") [] Ast.Ty.Tint)

let leaves r = match X.leaves r with [] -> [ one ] | l -> l

let find k m =
  try MX.find k m with Not_found -> (Ast.Expr.Set.empty, SA.empty)

let add_term k t mp =
  let g_t, g_a = find k mp in
  MX.add k (Ast.Expr.Set.add t g_t, g_a) mp

let up_add g t rt lvs =
  let g =
    if MX.mem rt g then g else MX.add rt (Ast.Expr.Set.empty, SA.empty) g
  in
  match Ast.Expr.term_view t with
  | Ast.Expr.Term { Ast.Expr.xs = []; _ } -> g
  | Ast.Expr.Term _ -> List.fold_left (fun g x -> add_term x t g) g lvs
  | _ -> assert false

let congr_add g lvs =
  match lvs with
  | [] -> Ast.Expr.Set.empty
  | x :: ls ->
    List.fold_left
      (fun acc y -> Ast.Expr.Set.inter (fst (find y g)) acc)
      (fst (find x g))
      ls

let up_close_up g p v =
  let lvs = leaves v in
  let g_p = find p g in
  List.fold_left (fun gg l -> MX.add l (union_tpl g_p (find l g)) gg) g lvs

let congr_close_up g p touched =
  let inter = function
    | [] -> (Ast.Expr.Set.empty, SA.empty)
    | rx :: l ->
      List.fold_left (fun acc x -> inter_tpl acc (find x g)) (find rx g) l
  in
  List.fold_left
    (fun (st, sa) tch -> union_tpl (st, sa) (inter (leaves tch)))
    (find p g) touched

let print g =
  if get_debug_use () then (
    let sterms fmt =
      Ast.Expr.Set.iter (fprintf fmt "%a " Ast.Expr.print)
    in
    let satoms fmt =
      SA.iter (fun (a, e) ->
          fprintf fmt "%a %a" Ast.Expr.print a Ast.Ex.print e)
    in
    let print_sterms_and_atoms fmt (st, sa) =
      match (Ast.Expr.Set.is_empty st, SA.is_empty sa) with
      | true, true -> fprintf fmt ""
      | false, true -> fprintf fmt " is used by {%a}" sterms st
      | true, false -> fprintf fmt " is used by {%a}" satoms sa
      | false, false ->
        fprintf fmt " is used by {%a} and {%a}" sterms st satoms sa
    in
    Util.Printer.print_dbg ~module_name:"Use" ~function_name:"print"
      "@[<v 2>gamma :@ ";
    MX.iter
      (fun t (st, sa) ->
         Util.Printer.print_dbg ~header:false "%a " X.print t;
         Util.Printer.print_dbg ~header:false "%a@ " print_sterms_and_atoms
           (st, sa))
      g;
    Util.Printer.print_dbg ~header:false "@]")

let mem = MX.mem
let add = MX.add
let empty = MX.empty
