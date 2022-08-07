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

type 'a literal = LTerm of Structs.Expr.t | LSem of 'a Structs.Xliteral.view

type instances =
  (Structs.Expr.t list * Structs.Expr.gformula * Structs.Ex.t) list

type 'a input =
  'a Structs.Xliteral.view
  * Structs.Expr.t option
  * Structs.Ex.t
  * Th_util.lit_origin

type 'a fact = 'a literal * Structs.Ex.t * Th_util.lit_origin

type 'a facts = {
  equas : 'a fact Queue.t;
  diseqs : 'a fact Queue.t;
  ineqs : 'a fact Queue.t;
  mutable touched : 'a Util.Util.MI.t;
}

type 'a result = { assume : 'a fact list; remove : Structs.Expr.t list }

module type RELATION = sig
  type t

  val empty : Structs.Expr.Set.t list -> t

  val assume :
    t -> Uf.t -> Shostak.Combine.r input list -> t * Shostak.Combine.r result

  val query : t -> Uf.t -> Shostak.Combine.r input -> Th_util.answer

  val case_split :
    t ->
    Uf.t ->
    for_model:bool ->
    (Shostak.Combine.r Structs.Xliteral.view * bool * Th_util.lit_origin) list
  (** case_split env returns a list of equalities *)

  val add :
    t ->
    Uf.t ->
    Shostak.Combine.r ->
    Structs.Expr.t ->
    t * (Shostak.Combine.r Structs.Xliteral.view * Structs.Ex.t) list
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Structs.Expr.Map.t
    * Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t ->
    t ->
    Uf.t ->
    (Structs.Expr.t -> Structs.Expr.t -> bool) ->
    t * instances

  val print_model :
    Format.formatter -> t -> (Structs.Expr.t * Shostak.Combine.r) list -> unit

  val new_terms : t -> Structs.Expr.Set.t
  val assume_th_elt : t -> Structs.Expr.th_elt -> Structs.Ex.t -> t
end
