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
module Structs = Alt_ergo_lib_structs

[@@@ocaml.warning "-33"]

open Util.Options
open Sig

module type S = sig
  type t
  type r = Shostak.Combine.r

  val empty : unit -> t
  val empty_facts : unit -> r Sig_rel.facts
  val add_fact : r Sig_rel.facts -> r Sig_rel.fact -> unit

  val add_term :
    t ->
    r Sig_rel.facts ->
    (* acc *)
    Structs.Expr.t ->
    Structs.Ex.t ->
    t * r Sig_rel.facts

  val add :
    t ->
    r Sig_rel.facts ->
    (* acc *)
    Structs.Expr.t ->
    Structs.Ex.t ->
    t * r Sig_rel.facts

  val assume_literals :
    t ->
    (r Sig_rel.literal * Structs.Ex.t * Th_util.lit_origin) list ->
    r Sig_rel.facts ->
    t * (r Sig_rel.literal * Structs.Ex.t * Th_util.lit_origin) list

  val case_split :
    t ->
    for_model:bool ->
    (r Structs.Xliteral.view * bool * Th_util.lit_origin) list * t

  val query : t -> Structs.Expr.t -> Th_util.answer
  val new_terms : t -> Structs.Expr.Set.t
  val class_of : t -> Structs.Expr.t -> Structs.Expr.t list

  val are_equal :
    t -> Structs.Expr.t -> Structs.Expr.t -> init_terms:bool -> Th_util.answer

  val are_distinct : t -> Structs.Expr.t -> Structs.Expr.t -> Th_util.answer
  val cl_extract : t -> Structs.Expr.Set.t list
  val term_repr : t -> Structs.Expr.t -> init_term:bool -> Structs.Expr.t
  val print_model : Format.formatter -> t -> unit
  val get_union_find : t -> Uf.t
  val assume_th_elt : t -> Structs.Expr.th_elt -> Structs.Ex.t -> t

  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Structs.Expr.Map.t
    * Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t ->
    t ->
    (Structs.Expr.t -> Structs.Expr.t -> bool) ->
    t * Sig_rel.instances
end

module Main : S
