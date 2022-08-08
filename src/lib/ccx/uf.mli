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

type t
type r = Shostak.Combine.r

module LX : Ast.Xliteral.S with type elt = r

val empty : unit -> t
val add : t -> Ast.Expr.t -> t * Ast.Expr.t list
val mem : t -> Ast.Expr.t -> bool
val find : t -> Ast.Expr.t -> r * Ast.Ex.t
val find_r : t -> r -> r * Ast.Ex.t

val union :
  t -> r -> r -> Ast.Ex.t -> t * (r * (r * r * Ast.Ex.t) list * r) list

val distinct : t -> r list -> Ast.Ex.t -> t

val are_equal :
  t -> Ast.Expr.t -> Ast.Expr.t -> added_terms:bool -> Ast.Th_util.answer

val are_distinct : t -> Ast.Expr.t -> Ast.Expr.t -> Ast.Th_util.answer
val already_distinct : t -> r list -> bool
val class_of : t -> Ast.Expr.t -> Ast.Expr.t list
val rclass_of : t -> r -> Ast.Expr.Set.t
val cl_extract : t -> Ast.Expr.Set.t list

val model :
  t ->
  (r * Ast.Expr.t list * (Ast.Expr.t * r) list) list
  * Ast.Expr.t list list

val print : t -> unit
val term_repr : t -> Ast.Expr.t -> Ast.Expr.t
val make : t -> Ast.Expr.t -> r (* may raise Not_found *)
val is_normalized : t -> r -> bool

val assign_next :
  t -> (r Ast.Xliteral.view * bool * Ast.Th_util.lit_origin) list * t

val output_concrete_model : t -> unit
