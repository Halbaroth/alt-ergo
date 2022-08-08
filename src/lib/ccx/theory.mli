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

module Ast = Alt_ergo_lib_ast

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Ast.Expr.t * Ast.Ex.t * int * int) list ->
    t ->
    t * Ast.Expr.Set.t * int

  val query : Ast.Expr.t -> t -> Ast.Th_util.answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Ast.Expr.Set.t list
  val extract_ground_terms : t -> Ast.Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> t * Ast.Expr.Set.t
  val add_term : t -> Ast.Expr.t -> add_in_cs:bool -> t
  val compute_concrete_model : t -> t
  val assume_th_elt : t -> Ast.Expr.th_elt -> Ast.Ex.t -> t

  val theories_instances :
    do_syntactic_matching:bool ->
    Ast.Matching_types.info Ast.Expr.Map.t
    * Ast.Expr.t list Ast.Expr.Map.t Ast.Sy.Map.t ->
    t ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    int ->
    int ->
    t * Sig_rel.instances

  val get_assumed : t -> Ast.Expr.Set.t
end

module Main_Default : S
module Main_Empty : S
