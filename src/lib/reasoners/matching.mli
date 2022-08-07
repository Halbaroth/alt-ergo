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

module type S = sig
  type t
  type theory

  open Matching_types

  val empty : t

  val make :
    max_t_depth:int ->
    Matching_types.info Structs.Expr.Map.t ->
    Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t ->
    Matching_types.trigger_info list ->
    t

  val add_term : term_info -> Structs.Expr.t -> t -> t
  val max_term_depth : t -> int -> t

  val add_triggers :
    Util.Util.matching_env ->
    t ->
    (Structs.Expr.t * int * Structs.Ex.t) Structs.Expr.Map.t ->
    t

  val terms_info :
    t ->
    info Structs.Expr.Map.t
    * Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t

  val query :
    Util.Util.matching_env -> t -> theory -> (trigger_info * gsubst list) list
end

module type Arg = sig
  type t

  val term_repr : t -> Structs.Expr.t -> init_term:bool -> Structs.Expr.t

  val are_equal :
    t -> Structs.Expr.t -> Structs.Expr.t -> init_terms:bool -> Th_util.answer

  val class_of : t -> Structs.Expr.t -> Structs.Expr.t list
end

module Make (X : Arg) : S with type theory = X.t
