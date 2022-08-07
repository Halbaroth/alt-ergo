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
module Structs = Alt_ergo_lib_structs

module Make (Th : Theory.S) : sig
  type t

  exception Bottom of Structs.Ex.t * Structs.Expr.Set.t list * t

  val empty : unit -> t
  val is_true : t -> Structs.Expr.t -> (Structs.Ex.t Lazy.t * int) option
  val assume : bool -> t -> (Structs.Expr.gformula * Structs.Ex.t) list -> t
  val decide : t -> Structs.Expr.t -> int -> t

  (* forget decisions one by one *)
  val forget_decision : t -> Structs.Expr.t -> int -> t
  val reset_decisions : t -> t
  (*val solve : t -> t*)

  val get_decisions : t -> (int * Structs.Expr.t) list
end
