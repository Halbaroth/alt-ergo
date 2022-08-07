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

type t
type r = Shostak.Combine.r

module LX : Structs.Xliteral.S with type elt = r

val empty : unit -> t
val add : t -> Structs.Expr.t -> t * Structs.Expr.t list
val mem : t -> Structs.Expr.t -> bool
val find : t -> Structs.Expr.t -> r * Structs.Ex.t
val find_r : t -> r -> r * Structs.Ex.t

val union :
  t -> r -> r -> Structs.Ex.t -> t * (r * (r * r * Structs.Ex.t) list * r) list

val distinct : t -> r list -> Structs.Ex.t -> t

val are_equal :
  t -> Structs.Expr.t -> Structs.Expr.t -> added_terms:bool -> Th_util.answer

val are_distinct : t -> Structs.Expr.t -> Structs.Expr.t -> Th_util.answer
val already_distinct : t -> r list -> bool
val class_of : t -> Structs.Expr.t -> Structs.Expr.t list
val rclass_of : t -> r -> Structs.Expr.Set.t
val cl_extract : t -> Structs.Expr.Set.t list

val model :
  t ->
  (r * Structs.Expr.t list * (Structs.Expr.t * r) list) list
  * Structs.Expr.t list list

val print : t -> unit
val term_repr : t -> Structs.Expr.t -> Structs.Expr.t
val make : t -> Structs.Expr.t -> r (* may raise Not_found *)
val is_normalized : t -> r -> bool

val assign_next :
  t -> (r Structs.Xliteral.view * bool * Th_util.lit_origin) list * t

val output_concrete_model : t -> unit
