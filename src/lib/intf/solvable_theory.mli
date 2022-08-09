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

type 'a ac = {
  h : Ast.Sy.t;
  t : Ast.Ty.t;
  l : ('a * int) list;
  distribute : bool;
}

type 'a solve_pb = { sbt : ('a * 'a) list; eqs : ('a * 'a) list }

module type Sig = sig
  type t
  (**Type of terms of the theory*)

  type r
  (**Type of representants of terms of the theory*)

  val name : string
  (** Name of the theory*)

  val is_mine_symb : Ast.Sy.t -> Ast.Ty.t -> bool
  (** return true if the symbol and the type are owned by the theory*)

  val make : Ast.Expr.t -> r * Ast.Expr.t list
  (** Give a representant of a term of the theory*)

  val term_extract : r -> Ast.Expr.t option * bool (* original term ? *)
  val color : r ac -> r
  val type_info : t -> Ast.Ty.t
  val embed : r -> t
  val is_mine : t -> r

  val leaves : t -> r list
  (** Give the leaves of a term of the theory *)

  val subst : r -> r -> t -> r
  val compare : r -> r -> int

  (* tests if two values are equal (using tags) *)
  val equal : t -> t -> bool

  val hash : t -> int
  (** solve r1 r2, solve the equality r1=r2 and return the substitution *)

  val solve : r -> r -> r solve_pb -> r solve_pb
  val print : Format.formatter -> t -> unit
  val fully_interpreted : Ast.Sy.t -> bool
  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

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

