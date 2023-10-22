(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type answer = (Explanation.t * Expr.Set.t list) option

type theory =
  | Th_arith
  | Th_sum
  | Th_adt
  | Th_arrays
  | Th_bitv
  | Th_UF
[@@deriving show]

(** Indicates where asserted literals come from.

    Note that literals are deduplicated before being propagated to the
    relations. {!Subst} literals are preserved, but other kinds of literals may
    be subsumed. *)
type lit_origin =
  | Subst
  (** Only equalities can be {!Subst} literals, and they are oriented: the
      left-hand side is always an uninterpreted term or AC symbol application.
      Effectively, {!Subst} literals are the substitutions generated by calls
      to [X.solve] and propagated through the CC(X) and AC(X) algorithms.

      In practice, a {!Subst} equality [r = rr] is generated when the
      corresponding substitution is performed by CC(X), i.e. when [rr] becomes
      the class representative for [r]. *)
  | CS of theory * Numbers.Q.t
  (** Literals of {!CS} origin come from the case splits performed by a
      specific theory. Usually, they are equalities of the shape [x = v] where
      [x] is an uninterpreted term and [v] a value; however, this is not
      necessarily the case (e.g. {!CS} literals from the theory of arrays are
      often disequalities).

      Depending on the theory, the shape of {!CS} literals can be restricted.
      In particular, {!CS} literals of the {!Th_UF} theory: those come from
      model generation in the union-find, and are assignments, i.e.  equalities
      [x = v] where [x] is uninterpreted and [v] is a value.

      The rational argument estimates the size of the split -- usually, the
      number of possible values the theory could choose for this specific
      uninterpreted term. *)
  | NCS of theory * Numbers.Q.t
  (** Literals of {!NCS} origin are created from a literal of {!CS} origin when
      the choice made in a case split turns out to be unsatisfiable. The
      literal is a negation of a {!CS} literal that was built by the
      corresponding theory, with the restrictions that this implies. *)
  | Other
  (** Literals of {!Other} are those that are not covered by any of the cases
      described above. In particular, user assertions, SAT decisions, SAT
      propagations and theory propagations all have the {!Other} origin. *)

type case_split = Shostak.Combine.r Xliteral.view * bool * lit_origin
(** A case split is a triple [(a, is_cs, origin)].

    The literal [a] is simply the literal that is the source of the split, or
    its negation (depending on [origin]).

    The [origin] should be either [CS] or [NCS]. Case splits returned by
    relations have an origin of [CS], which is then flipped to [NCS] if a
    contradiction is found involving [a].

    The [is_cs] flag should *always* be [true], unless the literal [a] is a
    *unit fact*, i.e. a fact that is true in all possible environments, not
    merely the current one. Note that it is acceptable for unit facts to be
    returned with [is_cs = true]; but if the [is_cs] flag is [false], the
    solver *will* assume that the literal can't take part in any conflict.
    Returning [is_cs = false] if the literal is not an unit fact **is
    unsound**.

    TL;DR: When in doubt, just set [is_cs] to [true]. *)

type optimized_split = {
  value : Objective.Value.t;
  case_split : case_split;
  (** The underlying case-split. Notice that the value propagate by this
      case-split doesn't always agree with the objective value [value].
      Indeed, [value] isn't always a proper model value when the problem
      is unbounded or some objective functions involved strict inequalities. *)
}
