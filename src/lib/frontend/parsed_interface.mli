(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module Util = Alt_ergo_lib_util
module Ast = Alt_ergo_lib_ast
open Ast.Parsed

(** Declaration of types  **)

val mk_abstract_type_decl :
  (Util.Loc.t -> string list -> string -> decl
   [@ocaml.ppwarning "TODO: add documentation for every function in this file"])

val mk_enum_type_decl :
  Util.Loc.t -> string list -> string -> string list -> decl

val mk_algebraic_type_decl :
  Util.Loc.t ->
  string list ->
  string ->
  (string * (string * ppure_type) list) list ->
  decl

val mk_record_type_decl :
  Util.Loc.t ->
  string list ->
  string ->
  ?constr:string ->
  (string * ppure_type) list ->
  decl

val mk_rec_type_decl : type_decl list -> decl

(** Declaration of symbols, functions, predicates, and goals *)

val mk_logic :
  Util.Loc.t ->
  Ast.Sy.name_kind ->
  (string * string) list ->
  plogic_type ->
  decl

val mk_function_def :
  Util.Loc.t ->
  string * string ->
  (Util.Loc.t * string * ppure_type) list ->
  ppure_type ->
  lexpr ->
  decl

val mk_ground_predicate_def : Util.Loc.t -> string * string -> lexpr -> decl

val mk_non_ground_predicate_def :
  Util.Loc.t ->
  string * string ->
  (Util.Loc.t * string * ppure_type) list ->
  lexpr ->
  decl

val mk_goal : Util.Loc.t -> string -> lexpr -> decl

(** Declaration of theories, generic axioms and rewriting rules **)

val mk_theory : Util.Loc.t -> string -> string -> decl list -> decl
val mk_generic_axiom : Util.Loc.t -> string -> lexpr -> decl
val mk_rewriting : Util.Loc.t -> string -> lexpr list -> decl

(** Declaration of theory axioms and case-splits **)

val mk_theory_axiom : Util.Loc.t -> string -> lexpr -> decl
val mk_theory_case_split : Util.Loc.t -> string -> lexpr -> decl

(** Declaration of stack assertions commands *)

val mk_push : Util.Loc.t -> int -> decl
val mk_pop : Util.Loc.t -> int -> decl

(** Making pure and logic types *)

val int_type : ppure_type
val bool_type : ppure_type
val real_type : ppure_type
val unit_type : ppure_type
val mk_bitv_type : string -> ppure_type
val mk_external_type : Util.Loc.t -> ppure_type list -> string -> ppure_type
val mk_var_type : Util.Loc.t -> string -> ppure_type
val mk_logic_type : ppure_type list -> ppure_type option -> plogic_type

(** Making arithmetic expressions and predicates **)

val mk_int_const : Util.Loc.t -> string -> lexpr
val mk_real_const : Util.Loc.t -> Num.num -> lexpr
val mk_add : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_sub : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_mul : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_div : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_mod : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pow_int : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pow_real : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_minus : Util.Loc.t -> lexpr -> lexpr
val mk_pred_lt : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pred_le : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pred_gt : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pred_ge : Util.Loc.t -> lexpr -> lexpr -> lexpr

(** Making Record expressions **)

val mk_record : Util.Loc.t -> (string * lexpr) list -> lexpr
val mk_with_record : Util.Loc.t -> lexpr -> (string * lexpr) list -> lexpr
val mk_dot_record : Util.Loc.t -> lexpr -> string -> lexpr

(** Making Array expressions **)

val mk_array_get : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_array_set : Util.Loc.t -> lexpr -> lexpr -> lexpr -> lexpr

(** Making Bit-vector expressions **)

val mk_bitv_const : Util.Loc.t -> string -> lexpr
val mk_bitv_extract : Util.Loc.t -> lexpr -> string -> string -> lexpr
val mk_bitv_concat : Util.Loc.t -> lexpr -> lexpr -> lexpr

(** Making Boolean / Propositional expressions **)

val mk_true_const : Util.Loc.t -> lexpr
val mk_false_const : Util.Loc.t -> lexpr
val mk_and : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_or : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_xor : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_iff : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_implies : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_not : Util.Loc.t -> lexpr -> lexpr
val mk_distinct : Util.Loc.t -> lexpr list -> lexpr
val mk_pred_eq : Util.Loc.t -> lexpr -> lexpr -> lexpr
val mk_pred_not_eq : Util.Loc.t -> lexpr -> lexpr -> lexpr

(** Making quantified formulas **)

val mk_forall :
  Util.Loc.t ->
  (string * string * ppure_type) list ->
  (lexpr list * bool) list ->
  lexpr list ->
  lexpr ->
  lexpr

val mk_exists :
  Util.Loc.t ->
  (string * string * ppure_type) list ->
  (lexpr list * bool) list ->
  lexpr list ->
  lexpr ->
  lexpr

(** Naming and casting types of expressions **)

val mk_type_cast : Util.Loc.t -> lexpr -> ppure_type -> lexpr
val mk_named : Util.Loc.t -> string -> lexpr -> lexpr

(** Making vars, applications, if-then-else, and let expressions **)

val mk_var : Util.Loc.t -> string -> lexpr
val mk_application : Util.Loc.t -> string -> lexpr list -> lexpr
val mk_pattern : Util.Loc.t -> string -> string list -> pattern
val mk_ite : Util.Loc.t -> lexpr -> lexpr -> lexpr -> lexpr
val mk_let : Util.Loc.t -> (string * lexpr) list -> lexpr -> lexpr
val mk_void : Util.Loc.t -> lexpr

(** Making particular expression used in semantic triggers **)

val mk_in_interval :
  Util.Loc.t -> lexpr -> bool -> lexpr -> lexpr -> bool -> lexpr

val mk_maps_to : Util.Loc.t -> string -> lexpr -> lexpr

(** Making cuts and checks **)

val mk_check : Util.Loc.t -> lexpr -> lexpr
val mk_cut : Util.Loc.t -> lexpr -> lexpr
val mk_match : Util.Loc.t -> lexpr -> (pattern * lexpr) list -> lexpr
val mk_algebraic_test : Util.Loc.t -> lexpr -> string -> lexpr

val mk_algebraic_project :
  Util.Loc.t -> guarded:bool -> lexpr -> string -> lexpr
