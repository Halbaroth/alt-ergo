(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** {1 Parse_command module used at start-up to parse the command line} *)

val parse_cmdline_arguments : unit -> unit
(** Only exported function. Calling it will parse the command line options
    and set them accordingly for the rest of the execution *)

exception Exit_parse_command of int
(** Exception used to exit with corresponding retcode *)
