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
module Combine : Intf.X.Sig

module Ite = Alt_ergo_lib_ite

module Polynome : Polynome.T with type r = Combine.r
module Arith : Intf.Solvable_theory.Sig with type r = Combine.r and type t = Polynome.t

module Records :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Records.abstract

module Bitv :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Bitv.abstract

module Arrays :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Arrays.abstract

module Enum :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Enum.abstract

module Adt :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Adt.abstract

module Ite_ :
  Intf.Solvable_theory.Sig with type r = Combine.r and type t = Combine.r Ite.Theory.abstract

module Ac : Ac.S with type r = Combine.r and type t = Combine.r Intf.Solvable_theory.ac

module MXH : Map.S with type key = Combine.r
(** map of semantic values using Combine.hash_cmp *)

module SXH : Set.S with type elt = Combine.r
(** set of semantic values using Combine.hash_cmp *)

module MXS : Map.S with type key = Combine.r
(** map of semantic values using structural compare Combine.str_cmp *)

module SXS : Set.S with type elt = Combine.r
(** set of semantic values using structural compare Combine.str_cmp *)
