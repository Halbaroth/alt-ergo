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

module Frontend = Alt_ergo_lib_frontend
module Util = Alt_ergo_lib_util
module Structs = Alt_ergo_lib_structs
module Reasoners = Alt_ergo_lib_reasoners
open Util.Options

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  ctx : Frontend.Commands.sat_tdecl list;
  local : Frontend.Commands.sat_tdecl list;
  global : Frontend.Commands.sat_tdecl list;
}

let main () =
  let module SatCont = (val Reasoners.Sat_solver.get_current ()
                          : Reasoners.Sat_solver_sig.SatContainer)
  in
  let module TH = (val if Util.Options.get_no_theory () then
                         (module Reasoners.Theory.Main_Empty
                         : Reasoners.Theory.S)
                       else
                         (module Reasoners.Theory.Main_Default
                         : Reasoners.Theory.S) : Reasoners.Theory.S)
  in
  let module SAT = SatCont.Make (TH) in
  let module FE = Frontend.Frontend.Make (SAT) in
  let solve all_context (cnf, goal_name) =
    let used_context = FE.choose_used_context all_context ~goal_name in
    let consistent_dep_stack = Stack.create () in
    Signals_profiling.init_profiling ();
    try
      if Util.Options.get_timelimit_per_goal () then (
        Util.Options.Time.start ();
        Util.Options.Time.set_timeout ~is_gui:false
          (Util.Options.get_timelimit ()));
      SAT.reset_refs ();
      let _ =
        List.fold_left
          (FE.process_decl FE.print_status used_context consistent_dep_stack)
          (SAT.empty (), true, Structs.Ex.empty)
          cnf
      in
      if Util.Options.get_timelimit_per_goal () then
        Util.Options.Time.unset_timeout ~is_gui:false;
      if Util.Options.get_profiling () then
        Structs.Profiling.print true (Util.Steps.get_steps ())
          (Signals_profiling.get_timers ())
          (get_fmt_err ())
    with Util.Util.Timeout ->
      if not (Util.Options.get_timelimit_per_goal ()) then exit 142
  in

  let typed_loop all_context state td =
    if get_type_only () then state
    else
      match td.Structs.Typed.c with
      | Structs.Typed.TGoal (_, kind, name, _) -> (
          let l = state.local @ state.global @ state.ctx in
          let cnf = List.rev @@ Frontend.Cnf.make l td in
          let () = solve all_context (cnf, name) in
          match kind with
          | Structs.Typed.Check | Structs.Typed.Cut -> { state with local = [] }
          | _ -> { state with global = []; local = [] })
      | Structs.Typed.TAxiom (_, s, _, _) when Structs.Typed.is_global_hyp s ->
          let cnf = Frontend.Cnf.make state.global td in
          { state with global = cnf }
      | Structs.Typed.TAxiom (_, s, _, _) when Structs.Typed.is_local_hyp s ->
          let cnf = Frontend.Cnf.make state.local td in
          { state with local = cnf }
      | _ ->
          let cnf = Frontend.Cnf.make state.ctx td in
          { state with ctx = cnf }
  in

  let (module I : Frontend.Input.S) =
    Frontend.Input.find (Util.Options.get_frontend ())
  in

  let parsed () =
    try
      Util.Options.Time.start ();
      if not (Util.Options.get_timelimit_per_goal ()) then
        Util.Options.Time.set_timeout ~is_gui:false
          (Util.Options.get_timelimit ());

      Util.Options.set_is_gui false;
      Signals_profiling.init_profiling ();

      let filename = get_file () in
      let preludes = Util.Options.get_preludes () in
      I.parse_files ~filename ~preludes
    with
    | Util.Util.Timeout ->
        FE.print_status (FE.Timeout None) 0;
        exit 142
    | Parsing.Parse_error ->
        Util.Printer.print_err "%a" Structs.Errors.report
          (Syntax_error ((Lexing.dummy_pos, Lexing.dummy_pos), ""));
        exit 1
    | Structs.Errors.Error e ->
        Util.Printer.print_err "%a" Structs.Errors.report e;
        exit 1
  in

  let all_used_context = FE.init_all_used_context () in
  if Util.Options.get_timelimit_per_goal () then FE.print_status FE.Preprocess 0;
  let assertion_stack = Stack.create () in
  let typing_loop state p =
    if get_parse_only () then state
    else
      try
        let l, env = I.type_parsed state.env assertion_stack p in
        List.fold_left (typed_loop all_used_context) { state with env } l
      with Structs.Errors.Error e ->
        if e != Warning_as_error then
          Util.Printer.print_err "%a" Structs.Errors.report e;
        exit 1
  in

  let state = { env = I.empty_env; ctx = []; local = []; global = [] } in
  try
    let (_ : _ state) = Seq.fold_left typing_loop state (parsed ()) in
    Util.Options.Time.unset_timeout ~is_gui:false
  with Util.Util.Timeout ->
    FE.print_status (FE.Timeout None) 0;
    exit 142
