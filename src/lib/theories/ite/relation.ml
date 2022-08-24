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

module Make (X : Intf.X.Sig) (UF : Intf.Uf.Sig) = struct
  open Util.Options


module EX2 = struct
  type t = Ast.Expr.t * Ast.Expr.t

  let compare (s1, s2) (t1, t2) =
    let c = Ast.Expr.compare s1 t1 in
    if c <> 0 then c else Ast.Expr.compare s2 t2
end

module ME2 = Map.Make (EX2)
module SE2 = Set.Make (EX2)

module TB = Map.Make (struct
    type t = Ast.Expr.t * bool

    let compare (a1, b1) (a2, b2) =
      let c = Ast.Expr.compare a1 a2 in
      if c <> 0 then c else Stdlib.compare b1 b2
              end)

type r = X.r
type uf = UF.t

type t = {
  pending_deds : Ast.Ex.t ME2.t;
  guarded_pos_deds : SE2.t Ast.Expr.Map.t;
  guarded_neg_deds : SE2.t Ast.Expr.Map.t;
  assumed_pos_preds : Ast.Ex.t Ast.Expr.Map.t;
  assumed_neg_preds : Ast.Ex.t Ast.Expr.Map.t;
}

let empty _ =
  {
    pending_deds = ME2.empty;
    guarded_pos_deds = Ast.Expr.Map.empty;
    guarded_neg_deds = Ast.Expr.Map.empty;
    assumed_pos_preds = Ast.Expr.Map.empty;
    assumed_neg_preds = Ast.Expr.Map.empty;
  }

let is_ite =
  let ite = Ast.Sy.Op Ast.Sy.Tite in
  fun t ->
    match Ast.Expr.term_view t with
    | Ast.Expr.Not_a_term _ -> assert false
    | Ast.Expr.Term { Ast.Expr.f; xs = [ p; t1; t2 ]; _ }
      when Ast.Sy.equal f ite ->
      Some (p, t1, t2)
    | _ -> None

let add_to_guarded p s t mp =
  let st = try Ast.Expr.Map.find p mp with Not_found -> SE2.empty in
  Ast.Expr.Map.add p (SE2.add (s, t) st) mp

let add_aux env t =
  if Util.Options.get_disable_ites () then env
  else
    match is_ite t with
    | None -> env
    | Some (p, t1, t2) -> (
        if get_debug_ite () then
          Util.Printer.print_dbg ~module_name:"Ite_rel" ~function_name:"add_aux"
            "(if %a then %a else %a)" Ast.Expr.print p Ast.Expr.print t1
            Ast.Expr.print t2;
        try
          let ex = Ast.Expr.Map.find p env.assumed_pos_preds in
          { env with pending_deds = ME2.add (t, t1) ex env.pending_deds }
        with Not_found -> (
            try
              let ex = Ast.Expr.Map.find p env.assumed_neg_preds in
              { env with pending_deds = ME2.add (t, t2) ex env.pending_deds }
            with Not_found ->
              let guarded_pos_deds = add_to_guarded p t t1 env.guarded_pos_deds in
              let guarded_neg_deds = add_to_guarded p t t2 env.guarded_neg_deds in
              { env with guarded_pos_deds; guarded_neg_deds }))

let add env _ _ t = (add_aux env t, [])

let extract_preds env la =
  List.fold_left
    (fun acc (_ra, root, expl, _orig) ->
       match root with
       | None -> acc
       | Some a -> (
           match Ast.Expr.lit_view a with
           | Ast.Expr.Pred (t, is_neg)
             when (not (Ast.Expr.Map.mem t env.assumed_pos_preds))
               && not (Ast.Expr.Map.mem t env.assumed_neg_preds) ->
             if get_debug_ite () then
               Util.Printer.print_dbg ~module_name:"Ite_rel"
                 ~function_name:"assume" "%a" Ast.Expr.print a;
             TB.add (t, is_neg) expl acc
           | _ -> acc))
    TB.empty la

let extract_pending_deductions env =
  let l =
    ME2.fold
      (fun (s, t) ex acc ->
         let a =
           (Ast.Expr.mk_eq ~iff:false s t
            [@ocaml.ppwarning "TODO: build IFF instead ?"])
         in
         if get_debug_ite () then
           Util.Printer.print_dbg ~module_name:"Ite_rel" ~function_name:"assume"
             "deduce that %a with expl %a" Ast.Expr.print a Ast.Ex.print
             ex;
         (Intf.Relation.LTerm a, ex, Ast.Th_util.Other) :: acc)
      env.pending_deds []
  in
  ({ env with pending_deds = ME2.empty }, l)

let assume env _ la =
  if Util.Options.get_disable_ites () then
    (env, { Intf.Relation.assume = []; remove = [] })
  else
    let env =
      TB.fold
        (fun (t, is_neg) ex env ->
           if is_neg then
             let assumed_neg_preds =
               Ast.Expr.Map.add t ex env.assumed_neg_preds
             in
             let deds =
               try Ast.Expr.Map.find t env.guarded_neg_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             { env with assumed_neg_preds; pending_deds }
           else
             let assumed_pos_preds =
               Ast.Expr.Map.add t ex env.assumed_pos_preds
             in
             let deds =
               try Ast.Expr.Map.find t env.guarded_pos_deds
               with Not_found -> SE2.empty
             in
             let pending_deds =
               SE2.fold (fun e acc -> ME2.add e ex acc) deds env.pending_deds
             in
             { env with assumed_pos_preds; pending_deds })
        (extract_preds env la) env
    in
    let env, deds = extract_pending_deductions env in
    (env, { Intf.Relation.assume = deds; remove = [] })

let assume env uf la =
  if Util.Options.get_timers () then (
    try
      Util.Timers.exec_timer_start Util.Timers.M_Arrays Util.Timers.F_assume;
      let res = assume env uf la in
      Util.Timers.exec_timer_pause Util.Timers.M_Arrays Util.Timers.F_assume;
      res
    with e ->
      Util.Timers.exec_timer_pause Util.Timers.M_Arrays Util.Timers.F_assume;
      raise e)
  else assume env uf la

let case_split _ _ ~for_model:_ = []
let query _ _ _ = None
let print_model _ _ _ = ()
let new_terms _ = Ast.Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = (env, [])
let assume_th_elt t _ _ = t
end
