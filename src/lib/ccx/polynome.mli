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
module Intf = Alt_ergo_lib_intf

exception Not_a_num
exception Maybe_zero

(* TODO: move this module type in the interface directory. *)
(** Module type of a solvable theory whose the semantic
    values are multipliable. *)
module type S = sig
  include Intf.X.Sig

  val mult : r -> r -> r
  (** [mult v1 v2] computes the multiplication of the semantic value [v1]
      by the semantic value [v2]. *)
end

(** Module type of polynomials of semantic values. *)
module type T = sig
  (** Let [ty] denotes an {{!type:Ast.Ty.t}Alt-Ergo type}.
      A polynomial [p] of type [ty] is an expression of the form
      {math p = c + \sum_{v \in V} a_v \cdot v}
      where {m V} is the set of {{!type:r}semantic values} of Alt-Ergo
      type [ty], {m a_v} and {m c} are rational numbers and all but
      finitely many of the {m a_v} are zero.
      The nonzero numbers {m a_v} are the {e coefficients}
      of [p], {m c} is the {e constant term} of [p] and the expressions
      {m a_v \cdot v} are its monomials.

      The monomials of [p] are ordered using the
      {{:https://en.wikipedia.org/wiki/Duality_(order_theory)}dual order}
      of the total order given by the function {!val:S.str_cmp}. *)

  (** {1 Types} *)

  type r
  (** Type of {{!type:Shostak.Combine.r}semantic values} appearing in
      polynomials. *)

  type t
  (** Type of {e polynomials}. *)

  (** {1 Constructors and destructors} *)

  val zero : Ast.Ty.t -> t
  (** [zero ty] is the zero polynomial of type [ty]. *)

  val one  : Ast.Ty.t -> t
  (** [one ty] is the one polynomial of type [ty]. *)

  val create :
    (Util.Numbers.Q.t * r) list -> Util.Numbers.Q.t -> Ast.Ty.t -> t
  (** [create lst c ty] creates a new polynomial whose the coefficients are
      given by the list [lst], the constant term is [c] and the Alt-Ergo type
      is [ty]. *)

  val to_list : t -> (Util.Numbers.Q.t * r) list * Util.Numbers.Q.t
  (** [to_list p] converts the polynomial [p] to a list.

      @returns [(lst, c)] where [lst] is the list of the monomial
      of [p] and [c] is its constant term. *)

  val to_monomial : t -> (Util.Numbers.Q.t * r * Util.Numbers.Q.t) option
  (** [to_monomial p] converts [p] to a monomial description.contents

      @returns [Some (a, v, c)] if [p] is the monomial {m av + c}.
      Otherwise the function returns [None]. *)

  val to_rational : t -> Util.Numbers.Q.t option
  (** [to_rational p] converts [p] to a rational representation.

      @returns [Some c] if [p] is constant and [c]
      is its constant term. Otherwise, the function returns [None]. *)

  val coef : r -> t -> Util.Numbers.Q.t
  (** [coef v p] gives the coefficient of the semantic value [v]
      in the polynomial [p]. *)

  val choose : t -> r * Util.Numbers.Q.t
  (** [choose p] returns the smallest monome of [p]. The order on the monome
      is given by the dual order of the order {!val:S.str_cmp} on
      semantic values. *)

  (** {1 Comparison functions} *)

  val compare : t -> t -> int
  (** [compare p q] compares the polynomial [p] and [q] using a
      lexicographic order. *)

  val equal : t -> t -> bool
  (** [equal p q] is true if and only if [p] and [q] have the
      same coefficients and constant terms. *)

  val hash : t -> int
  (** [hash p] computes the hash of the polynomial [p]. If
      {m p = c + \sum_{i=1}^d a_i \cdot v_i} with {m (v_i)} a
      nonincreasing sequence of semantic values 
      for the order {!val:S.str_cmp}, the hash of [p] is
      given by the formula
      {math  23^d(19 h_c + 17 h_{ty}) + \sum_{i=1}^d 23^{d-i} h_{a_i} h_{v_i}}
      where
      {ul
        {- {m h_c} is the hash of the constant term given by the function
           {!val:Util.Numbers.Q.hash}.}
        {- {m h_{ty}} is the hash of the Alt-Ergo type [ty] of [p] given
           by the function {!val:Ast.Ty.hash}.}
        {- {m h_{a_i}} is the hash of the coefficient {m a_i} given by
           the function {!val:Util.Numbers.Q.hash}.}
        {- {m h_{v_i}} is the hash of the semantic value {m v_i} given
           by the function {!val:S.hash}.}}
      *)

  (** {1 Operations} *)

  (** {2 Algebraic operations} *)

  val add : t -> t -> t
  (** [add p q] computes the addition of the polynomials [p] and [q]. If
      {m p = c + \sum_{v \in V} a_v \cdot v}
      and {m q = d + \sum_{v \in V} b_v \cdot v},
      then the result is of the form
      {math c + d + \sum_{v \in V} (a_v + b_v) \cdot v} *)

  val sub : t -> t -> t
  (** [sub p q] computes the substraction of the polynomials [p] and [q]. If
      {m p = c + \sum_{v \in V} a_v \cdot v}
      and {m q = d + \sum_{v \in V} b_v \cdot v},
      then the result is of the form
      {math c - d + \sum_{v \in V} (a_v - b_v) \cdot v} *)

  val mult : t -> t -> t
  (** [mult p q] multiplies the polynomial [p] by [q]. If
      {m p = c + \sum_{v \in V} a_v \cdot v} and
      {m q = d + \sum_{v \in V} b_v \cdot v},
      then the result is of the form
      {math c \cdot d + \sum_{v, w \in V} a_v d_w \cdot v w}
      where the multiplication {m vw} is performed by
      the function {!val:S.mult}. *)

  val add_const : Util.Numbers.Q.t -> t -> t
  (** [add_const q p] adds the rational number [q] to the constant term of
      [p]. If {m p = b + \sum_{v \in V} a_v \cdot v},
      then the result is of the form
      {math p = b + q + \sum_{v \in V} a_v \cdot v} *)

  val mult_const : Util.Numbers.Q.t -> t -> t
  (** [mult_const q p] multiplies the coefficients and the constant
      term of [p] by the rational number [q].
      If {m p = c + \sum_{v \in V} a_v \cdot v}
      then the result is of the form
      {math p = qc + \sum_{v \in V} q a_v \cdot v} *)

  (** {2 Arithmetical operations} *)

  val ppmc_denominators : t -> Util.Numbers.Q.t
  (** [ppmc_denominators p] computes the {e positive lcm} of the denominators
      of the coefficients of [p]. If {m p = c + \sum_{v \in V} a_v \cdot v }
      and {m a_v = \frac{n_v}{d_v}} with {m n_v} and {m d_v} two integers such
      that {m n_v \wedge d_v = 1}, then the
      result is {m \wedge_{v \in V} d_v}. *)

  val pgcd_numerators : t -> Util.Numbers.Q.t
  (** [pgcd_numerators p] computes the {e positive gcd} of the numerators of
      the coefficients of [p]. If {m p = c + \sum_{v \in V} a_v \cdot v }
      and {m a_v = \frac{n_v}{d_v}} with {m n_v} and {m d_v} two integers such
      that {m n_v \wedge d_v = 1}, then the
      result is {m \lor_{v \in V} d_v}. *)

  val modulo : t -> t -> t
  (** [modulo p q] computes {e residue} of the constant term of [p]
      modulo the constant term of [q].

      @returns the residue as a constant polynomial. *)

  (** {1 Misc} *)

  val div : t -> t -> t * bool
  (** [div p q] divides the constant term of [p]
      by the constant term of [q].

      @returns the division as a constant polynomial. *)

  val is_const : t -> bool
  (** [is_const p] is true if and only if the polynomial
      [p] has no nonzero coefficient. *)

  val subst : r -> t -> t -> t
  (** [subst v p q] substitutes the coefficient of the semantic value [v]
      in [q] by its coefficient in [p]. *)

  val remove : r -> t -> t
  (** [remove v p] set the coefficient of the semantiv value [v] in
      the polynomial [p] to zero. *)

  val leaves : t -> r list
  (** [leaves p] returns a list of the leaves of semantic values appearing
      in the polynomial [p]. The produced list is without duplicate
      elements and is not ordered. *)

  val print : Format.formatter -> t -> unit
  (** [print fmt p] pretty prints the polynomial [p] using the formatter
      [fmt]. *)

  val type_info : t -> Ast.Ty.t
  (** [type_info p] gives the Alt-Ergo type of the polynomial [p]. *)

  (* TODO: finish the documentation. *)
  (** {1 Undocumented } *)

  (* retourne un polynome sans constante et sa constante
     et la constante multiplicative:
     normal_form p = (p',c,d) <=> p = (p' + c) * d *)
  val normal_form : t -> t * Util.Numbers.Q.t * Util.Numbers.Q.t

  (* comme normal_form mais le signe est aussi normalise *)
  val normal_form_pos : t -> t * Util.Numbers.Q.t * Util.Numbers.Q.t


  val abstract_selectors : t -> (r * r) list -> t * (r * r) list
  val separate_constant : t -> t * Util.Numbers.Q.t
end

module type EXTENDED_Polynome = sig
  include T

  val extract : r -> t option
  val embed : t -> r
end

(** Functor building an implementation of polynomials for
    the semantic values of type {!type:X.r}. *)
module Make (X : S) : T with type r = X.r
