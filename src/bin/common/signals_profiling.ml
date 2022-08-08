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

module Ast = Alt_ergo_lib_ast
module Util = Alt_ergo_lib_util
open Util.Options

let timers = Util.Timers.empty ()
let get_timers () = timers

let init_sigterm_6 () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint (*-6*)
    (Sys.Signal_handle
       (fun _ ->
          if Util.Options.get_profiling () then
            Ast.Profiling.switch (get_fmt_err ())
          else (
            Util.Printer.print_wrn "User wants me to stop.";
            Util.Printer.print_std "unknown";
            exit 1)))

let init_sigterm_11_9 () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Util.Options.get_profiling () then
    List.iter
      (fun sign ->
         Sys.set_signal sign
           (Sys.Signal_handle
              (fun _ ->
                 Ast.Profiling.print true (Util.Steps.get_steps ()) timers
                   (get_fmt_err ());
                 exit 1)))
      [ Sys.sigterm (*-11*); Sys.sigquit (*-9*) ]

let init_sigterm_21 () =
  (* put the test here because Windows does not handle Sys.Signal_handle
     correctly *)
  if Util.Options.get_profiling () then
    Sys.set_signal Sys.sigprof (*-21*)
      (Sys.Signal_handle
         (fun _ ->
            Ast.Profiling.print false (Util.Steps.get_steps ()) timers
              (get_fmt_err ())))

let init_sigalarm () =
  if not (get_model ()) then
    try
      Sys.set_signal Sys.sigvtalrm
        (Sys.Signal_handle (fun _ -> Util.Options.exec_timeout ()))
    with Invalid_argument _ -> ()

let init_profiling () =
  if Util.Options.get_profiling () then (
    Util.Timers.reset timers;
    assert (Util.Options.get_timers ());
    Util.Timers.set_timer_start (Util.Timers.start timers);
    Util.Timers.set_timer_pause (Util.Timers.pause timers);
    Ast.Profiling.init ())

let init_signals () =
  init_sigterm_6 ();
  init_sigterm_11_9 ();
  init_sigterm_21 ();
  init_sigalarm ()
