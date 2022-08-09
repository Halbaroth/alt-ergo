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
module Intf = Alt_ergo_lib_intf

type 'a abstract =
  | Constr of {
      c_name : Util.Hstring.t;
      c_ty : Ast.Ty.t;
      c_args : (Util.Hstring.t * 'a) list;
    }
  | Select of { d_name : Util.Hstring.t; d_ty : Ast.Ty.t; d_arg : 'a }
  | Tester of { t_name : Util.Hstring.t; t_arg : 'a }
  (* tester is currently not used to build values *)
  | Alien of 'a

module type ALIEN = sig
  include Intf.X.Sig

  val embed : r abstract -> r
  val extract : r -> r abstract option
end

module Shostak (X : ALIEN) :
  Intf.Solvable_theory.Sig with type r = X.r and type t = X.r abstract
