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

let get_current () =
  match Util.Options.get_sat_solver () with
  | Util.Util.Tableaux | Util.Util.Tableaux_CDCL ->
      if Util.Options.get_verbose () then
        Util.Printer.print_dbg ~module_name:"Sat_solver"
          "use Tableaux-like solver";
      (module Fun_sat : Sat_solver_sig.SatContainer)
  | Util.Util.CDCL | Util.Util.CDCL_Tableaux ->
      if Util.Options.get_verbose () then
        Util.Printer.print_dbg ~module_name:"Sat_solver" "use CDCL solver";
      (module Satml_frontend : Sat_solver_sig.SatContainer)
