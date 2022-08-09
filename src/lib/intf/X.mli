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

type 'a ac = 'a Solvable_theory.ac

module type Sig = sig
  type r

  val make : Ast.Expr.t -> r * Ast.Expr.t list
  val type_info : r -> Ast.Ty.t
  val str_cmp : r -> r -> int
  val hash_cmp : r -> r -> int
  val equal : r -> r -> bool
  val hash : r -> int
  val leaves : r -> r list
  val subst : r -> r -> r -> r
  val solve : r -> r -> (r * r) list
  val term_embed : Ast.Expr.t -> r
  val term_extract : r -> Ast.Expr.t option * bool (* original term ? *)
  val ac_embed : r ac -> r
  val ac_extract : r -> r ac option
  val color : r ac -> r
  val fully_interpreted : Ast.Sy.t -> Ast.Ty.t -> bool
  val is_a_leaf : r -> bool
  val print : Format.formatter -> r -> unit
  val abstract_selectors : r -> (r * r) list -> r * (r * r) list
  val top : unit -> r
  val bot : unit -> r
  val is_solvable_theory_symbol : Ast.Sy.t -> Ast.Ty.t -> bool

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Ast.Expr.t * r) list -> (Ast.Expr.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model :
    Ast.Expr.t -> r -> (Ast.Expr.t * r) list -> r * string
end
