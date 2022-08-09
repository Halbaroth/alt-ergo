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
module Intf = Alt_ergo_lib_intf

[@@@ocaml.warning "-33"]

open Util.Options

module type S = sig
  type t
  type r = Shostak.Combine.r

  val empty : unit -> t
  val empty_facts : unit -> r Intf.Relation.facts
  val add_fact : r Intf.Relation.facts -> r Intf.Relation.fact -> unit

  val add_term :
    t ->
    r Intf.Relation.facts ->
    (* acc *)
    Ast.Expr.t ->
    Ast.Ex.t ->
    t * r Intf.Relation.facts

  val add :
    t ->
    r Intf.Relation.facts ->
    (* acc *)
    Ast.Expr.t ->
    Ast.Ex.t ->
    t * r Intf.Relation.facts

  val assume_literals :
    t ->
    (r Intf.Relation.literal * Ast.Ex.t * Ast.Th_util.lit_origin) list ->
    r Intf.Relation.facts ->
    t * (r Intf.Relation.literal * Ast.Ex.t * Ast.Th_util.lit_origin) list

  val case_split :
    t ->
    for_model:bool ->
    (r Ast.Xliteral.view * bool * Ast.Th_util.lit_origin) list * t

  val query : t -> Ast.Expr.t -> Ast.Th_util.answer
  val new_terms : t -> Ast.Expr.Set.t
  val class_of : t -> Ast.Expr.t -> Ast.Expr.t list

  val are_equal :
    t -> Ast.Expr.t -> Ast.Expr.t -> init_terms:bool -> Ast.Th_util.answer

  val are_distinct : t -> Ast.Expr.t -> Ast.Expr.t -> Ast.Th_util.answer
  val cl_extract : t -> Ast.Expr.Set.t list
  val term_repr : t -> Ast.Expr.t -> init_term:bool -> Ast.Expr.t
  val print_model : Format.formatter -> t -> unit
  val get_union_find : t -> Uf.t
  val assume_th_elt : t -> Ast.Expr.th_elt -> Ast.Ex.t -> t

  val theories_instances :
    do_syntactic_matching:bool ->
    Ast.Matching_types.info Ast.Expr.Map.t
    * Ast.Expr.t list Ast.Expr.Map.t Ast.Sy.Map.t ->
    t ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    t * Intf.Relation.instances
end

module Main : S
