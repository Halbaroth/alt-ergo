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

type 'a literal = LTerm of Ast.Expr.t | LSem of 'a Ast.Xliteral.view

type instances =
  (Ast.Expr.t list * Ast.Expr.gformula * Ast.Ex.t) list

type 'a input =
  'a Ast.Xliteral.view
  * Ast.Expr.t option
  * Ast.Ex.t
  * Th_util.lit_origin

type 'a fact = 'a literal * Ast.Ex.t * Th_util.lit_origin

type 'a facts = {
  equas : 'a fact Queue.t;
  diseqs : 'a fact Queue.t;
  ineqs : 'a fact Queue.t;
  mutable touched : 'a Util.Util.MI.t;
}

type 'a result = { assume : 'a fact list; remove : Ast.Expr.t list }

module type RELATION = sig
  type t

  val empty : Ast.Expr.Set.t list -> t

  val assume :
    t -> Uf.t -> Shostak.Combine.r input list -> t * Shostak.Combine.r result

  val query : t -> Uf.t -> Shostak.Combine.r input -> Th_util.answer

  val case_split :
    t ->
    Uf.t ->
    for_model:bool ->
    (Shostak.Combine.r Ast.Xliteral.view * bool * Th_util.lit_origin) list
  (** case_split env returns a list of equalities *)

  val add :
    t ->
    Uf.t ->
    Shostak.Combine.r ->
    Ast.Expr.t ->
    t * (Shostak.Combine.r Ast.Xliteral.view * Ast.Ex.t) list
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Ast.Expr.Map.t
    * Ast.Expr.t list Ast.Expr.Map.t Ast.Sy.Map.t ->
    t ->
    Uf.t ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    t * instances

  val print_model :
    Format.formatter -> t -> (Ast.Expr.t * Shostak.Combine.r) list -> unit

  val new_terms : t -> Ast.Expr.Set.t
  val assume_th_elt : t -> Ast.Expr.th_elt -> Ast.Ex.t -> t
end
