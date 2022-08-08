(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Util = Alt_ergo_lib_util
module Ast = Alt_ergo_lib_ast
open Ast.Satml_types

exception Sat
exception Unsat of Ast.Satml_types.Atom.clause list option
exception Last_UIP_reason of Atom.Set.t

type conflict_origin =
  | C_none
  | C_bool of Atom.clause
  | C_theory of Ast.Ex.t

module type SAT_ML = sig
  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit

  val set_new_proxies :
    t ->
    (Ast.Satml_types.Atom.atom * Ast.Satml_types.Atom.atom list * bool)
      Util.Util.MI.t ->
    unit

  val new_vars :
    t ->
    nbv:int ->
    (* nb made vars *)
    Ast.Satml_types.Atom.var list ->
    Ast.Satml_types.Atom.atom list list ->
    Ast.Satml_types.Atom.atom list list ->
    Ast.Satml_types.Atom.atom list list
    * Ast.Satml_types.Atom.atom list list

  val assume :
    t ->
    Ast.Satml_types.Atom.atom list list ->
    Ast.Satml_types.Atom.atom list list ->
    Ast.Expr.t ->
    cnumber:int ->
    Ast.Satml_types.Atom.atom option Flat_Formula.Map.t ->
    dec_lvl:int ->
    unit

  val boolean_model : t -> Ast.Satml_types.Atom.atom list

  val instantiation_context :
    t ->
    Ast.Satml_types.Flat_Formula.hcons_env ->
    Ast.Satml_types.Atom.Set.t

  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val empty : unit -> t
  val assume_th_elt : t -> Ast.Expr.th_elt -> Ast.Ex.t -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val update_lazy_cnf :
    t ->
    do_bcp:bool ->
    Ast.Satml_types.Atom.atom option Flat_Formula.Map.t ->
    dec_lvl:int ->
    unit

  val exists_in_lazy_cnf : t -> Flat_Formula.t -> bool
  val known_lazy_formulas : t -> int Flat_Formula.Map.t
  val reason_of_deduction : Atom.atom -> Atom.Set.t
  val assume_simple : t -> Atom.atom list list -> unit
  val decide : t -> Atom.atom -> unit
  val conflict_analyze_and_fix : t -> conflict_origin -> unit
  val push : t -> Ast.Satml_types.Atom.atom -> unit
  val pop : t -> unit
end

module Make (Th : Theory.S) : SAT_ML with type th = Th.t
