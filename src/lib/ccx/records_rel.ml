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

type t = unit
type r = Shostak.Combine.r
type uf = Uf.t

let empty _ = ()
let assume _ _ _ = ((), { Intf.Relation.assume = []; remove = [] })
let query _ _ _ = None
let case_split _ _ ~for_model:_ = []
let add env _ _ _ = (env, [])
let print_model _ _ _ = ()
let new_terms _ = Ast.Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = (env, [])

let assume_th_elt t th_elt _ =
  match th_elt.Ast.Expr.extends with
  | Util.Util.Records ->
    failwith "This Theory does not support theories extension"
  | _ -> t
