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

module Make (Th : Theory.S) : sig
  type t

  exception Bottom of Ast.Ex.t * Ast.Expr.Set.t list * t

  val empty : unit -> t
  val is_true : t -> Ast.Expr.t -> (Ast.Ex.t Lazy.t * int) option
  val assume : bool -> t -> (Ast.Expr.gformula * Ast.Ex.t) list -> t
  val decide : t -> Ast.Expr.t -> int -> t

  (* forget decisions one by one *)
  val forget_decision : t -> Ast.Expr.t -> int -> t
  val reset_decisions : t -> t
  (*val solve : t -> t*)

  val get_decisions : t -> (int * Ast.Expr.t) list
end
