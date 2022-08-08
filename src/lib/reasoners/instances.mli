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

module type S = sig
  type t
  type tbox
  type instances = (Ast.Expr.gformula * Ast.Ex.t) list

  val empty : t
  val add_terms : t -> Ast.Expr.Set.t -> Ast.Expr.gformula -> t
  val add_lemma : t -> Ast.Expr.gformula -> Ast.Ex.t -> t

  val add_predicate :
    t ->
    guard:Ast.Expr.t ->
    name:string ->
    Ast.Expr.gformula ->
    Ast.Ex.t ->
    t

  (* the first returned expr is the guard (incremental mode),
     the second one is the defn of the given predicate *)
  val ground_pred_defn :
    Ast.Expr.t ->
    t ->
    (Ast.Expr.t * Ast.Expr.t * Ast.Ex.t) option

  val pop : t -> guard:Ast.Expr.t -> t

  val m_lemmas :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t ->
    Matching_types.info Ast.Expr.Map.t
    * Ast.Expr.t list Ast.Expr.Map.t Ast.Sy.Map.t
end

module Make (X : Theory.S) : S with type tbox = X.t
