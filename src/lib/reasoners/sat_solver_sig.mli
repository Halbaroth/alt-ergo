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

  exception Sat of t
  exception Unsat of Structs.Ex.t
  exception I_dont_know of t

  val empty : unit -> t
  (** the empty sat-solver context *)

  val empty_with_inst : (Structs.Expr.t -> bool) -> t

  val push : t -> int -> t
  (** [push env n] add n new assertion levels.
      A guard g is added for every expression e assumed at the current
      assertion level.
      Ie. assuming e after the push will become g -> e,
      a g will be forced to be true (but not propagated at level 0) *)

  val pop : t -> int -> t
  (** [pop env n] remove an assertion level.
      Internally, the guard g introduced in the push correponsding to this pop
      will be propagated to false (at level 0) *)

  val assume : t -> Structs.Expr.gformula -> Structs.Ex.t -> t
  (** [assume env f] assume a new formula [f] in [env]. Raises Unsat if
      [f] is unsatisfiable in [env] *)

  val assume_th_elt : t -> Structs.Expr.th_elt -> Structs.Ex.t -> t
  (** [assume env f exp] assume a new formula [f] with the explanation [exp]
      in the theories environment of [env]. *)

  val pred_def :
    t -> Structs.Expr.t -> string -> Structs.Ex.t -> Util.Loc.t -> t
  (** [pred_def env f] assume a new predicate definition [f] in [env]. *)

  val unsat : t -> Structs.Expr.gformula -> Structs.Ex.t
  (** [unsat env f size] checks the unsatisfiability of [f] in
      [env]. Raises I_dont_know when the proof tree's height reaches
      [size]. Raises Sat if [f] is satisfiable in [env] *)

  val print_model : header:bool -> Format.formatter -> t -> unit
  (** [print_model header fmt env] print propositional model and theory model
      on the corresponding fmt. *)

  val reset_refs : unit -> unit
end

module type SatContainer = sig
  module Make (Th : Theory.S) : S
end
