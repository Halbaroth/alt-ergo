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
module Structs = Alt_ergo_lib_structs
open Format
open Util.Options
open Sig_rel
module X = Shostak.Combine
module A = Structs.Xliteral
module LR = Uf.LX
module CC_X = Ccx.Main

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Structs.Expr.t * Structs.Ex.t * int * int) list ->
    t ->
    t * Structs.Expr.Set.t * int

  val query : Structs.Expr.t -> t -> Th_util.answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Structs.Expr.Set.t list
  val extract_ground_terms : t -> Structs.Expr.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
  val do_case_split : t -> t * Structs.Expr.Set.t
  val add_term : t -> Structs.Expr.t -> add_in_cs:bool -> t
  val compute_concrete_model : t -> t
  val assume_th_elt : t -> Structs.Expr.th_elt -> Structs.Ex.t -> t

  val theories_instances :
    do_syntactic_matching:bool ->
    Matching_types.info Structs.Expr.Map.t
    * Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t ->
    t ->
    (Structs.Expr.t -> Structs.Expr.t -> bool) ->
    int ->
    int ->
    t * Sig_rel.instances

  val get_assumed : t -> Structs.Expr.Set.t
end

module Main_Default : S = struct
  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Util.Printer

    let subterms_of_assumed l =
      List.fold_left
        (List.fold_left (fun st (a, _, _) ->
             Structs.Expr.Set.union st
               (Structs.Expr.sub_terms Structs.Expr.Set.empty a)))
        Structs.Expr.Set.empty l

    let types_of_subterms st =
      Structs.Expr.Set.fold
        (fun t acc -> Structs.Ty.Set.add (Structs.Expr.type_info t) acc)
        st Structs.Ty.Set.empty

    let generalize_types ty1 ty2 =
      match (ty1, ty2) with
      | Structs.Ty.Tvar _, _ -> ty1
      | _, Structs.Ty.Tvar _ -> ty2
      | _ -> Structs.Ty.fresh_tvar ()

    let logics_of_assumed st =
      Structs.Expr.Set.fold
        (fun t mp ->
          match Structs.Expr.term_view t with
          | Structs.Expr.Not_a_term _ -> assert false
          | Structs.Expr.Term
              {
                Structs.Expr.f =
                  Structs.Sy.Name
                    (hs, ((Structs.Sy.Ac | Structs.Sy.Other) as is_ac));
                xs;
                ty;
                _;
              } ->
              let xs = List.map Structs.Expr.type_info xs in
              let xs, ty =
                try
                  let xs', ty', is_ac' = Util.Hstring.Map.find hs mp in
                  assert (is_ac == is_ac');
                  let ty = generalize_types ty ty' in
                  let xs =
                    try List.map2 generalize_types xs xs'
                    with _ -> assert false
                  in
                  (xs, ty)
                with Not_found -> (xs, ty)
              in
              Util.Hstring.Map.add hs (xs, ty, is_ac) mp
          | _ -> mp)
        st Util.Hstring.Map.empty

    let types_of_assumed sty =
      let open Structs.Ty in
      Structs.Ty.Set.fold
        (fun ty mp ->
          match ty with
          | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> mp
          | Tvar _ -> assert false
          | (Text (_, hs) | Tsum (hs, _) | Trecord { name = hs; _ })
            when Util.Hstring.Map.mem hs mp ->
              mp
          | Text (l, hs) ->
              let l = List.map (fun _ -> Structs.Ty.fresh_tvar ()) l in
              Util.Hstring.Map.add hs (Text (l, hs)) mp
          | Tsum (hs, _) -> Util.Hstring.Map.add hs ty mp
          | Trecord { name; _ } ->
              (* cannot do better for records ? *)
              Util.Hstring.Map.add name ty mp
          | Tadt (hs, _) ->
              (* cannot do better for ADT ? *)
              Util.Hstring.Map.add hs ty mp)
        sty Util.Hstring.Map.empty

    let print_types_decls ?(header = true) types =
      let open Structs.Ty in
      print_dbg ~flushed:false ~header "@[<v 2>(* types decls: *)@ ";
      Util.Hstring.Map.iter
        (fun _ ty ->
          match ty with
          | Tint | Treal | Tbool | Tunit | Tbitv _ | Tfarray _ -> ()
          | Tvar _ -> assert false
          | Text _ -> print_dbg ~flushed:false "type %a@ " Structs.Ty.print ty
          | Tsum (_, l) -> (
              print_dbg ~flushed:false ~header:false "type %a = "
                Structs.Ty.print ty;
              match l with
              | [] -> assert false
              | e :: l ->
                  let print fmt e = fprintf fmt " | %s" (Util.Hstring.view e) in
                  print_dbg ~flushed:false ~header:false "%s@ %a@ "
                    (Util.Hstring.view e) (pp_list_no_space print) l)
          | Trecord { Structs.Ty.lbs; _ } -> (
              print_dbg ~flushed:false ~header:false "type %a = "
                Structs.Ty.print ty;
              match lbs with
              | [] -> assert false
              | (lbl, ty) :: l ->
                  let print fmt (lbl, ty) =
                    fprintf fmt " ; %s :%a" (Util.Hstring.view lbl)
                      Structs.Ty.print ty
                  in
                  print_dbg ~flushed:false ~header:false "{ %s : %a%a"
                    (Util.Hstring.view lbl) Structs.Ty.print ty
                    (pp_list_no_space print) l;
                  print_dbg ~flushed:false ~header:false " }@ ")
          | Tadt _ ->
              print_dbg ~flushed:false ~header:false "%a@ "
                Structs.Ty.print_full ty)
        types;
      print_dbg ~header:false "@]"

    let print_arrow_type fmt xs =
      match xs with
      | [] -> ()
      | e :: l ->
          fprintf fmt "%a" Structs.Ty.print e;
          List.iter (fprintf fmt ", %a" Structs.Ty.print) l;
          fprintf fmt " -> "

    let print_logics ?(header = true) logics =
      print_dbg ~header "@[<v 2>(* logics: *)@ ";
      Util.Hstring.Map.iter
        (fun hs (xs, ty, is_ac) ->
          print_dbg ~flushed:false ~header:false "logic %s%s : %a%a@ "
            (if is_ac == Structs.Sy.Ac then "ac " else "")
            (Util.Hstring.view hs) print_arrow_type xs Structs.Ty.print ty)
        logics;
      print_dbg ~header:false "@]"

    let print_declarations ?(header = true) l =
      let st = subterms_of_assumed l in
      let sty = types_of_subterms st in
      let types = types_of_assumed sty in
      let logics = logics_of_assumed st in
      print_types_decls ~header types;
      print_logics ~header logics

    let assumed =
      let cpt = ref 0 in
      fun l ->
        if get_debug_cc () then (
          print_dbg ~module_name:"Theory" ~function_name:"assumed"
            "Assumed facts (in this order):";
          print_declarations ~header:false l;
          incr cpt;
          print_dbg ~flushed:false ~header:false "goal g_%d :@ " !cpt;
          List.iter
            (fun l ->
              print_dbg ~flushed:false ~header:false "(* call to assume *)@ ";
              match List.rev l with
              | [] -> assert false
              | (a, dlvl, plvl) :: l ->
                  print_dbg ~flushed:false ~header:false "( (* %d , %d *) %a "
                    dlvl plvl Structs.Expr.print a;
                  List.iter
                    (fun (a, dlvl, plvl) ->
                      print_dbg ~flushed:false ~header:false
                        " and@ (* %d , %d *) %a " dlvl plvl Structs.Expr.print a)
                    l;
                  print_dbg ~flushed:false ~header:false ") ->@ ")
            (List.rev l);
          print_dbg ~header:false "false")

    let theory_of k =
      match k with
      | Th_util.Th_arith -> "Th_arith "
      | Th_util.Th_sum -> "Th_sum   "
      | Th_util.Th_adt -> "Th_adt   "
      | Th_util.Th_arrays -> "Th_arrays"
      | Th_util.Th_UF -> "Th_UF"

    let made_choices fmt choices =
      match choices with
      | [] -> ()
      | _ ->
          fprintf fmt "@[<v 2>Stack of choices:@ ";
          List.iter
            (fun (rx, lit_orig, _, ex) ->
              match lit_orig with
              | Th_util.CS (k, _) ->
                  fprintf fmt "  > %s  cs: %a (because %a)@ " (theory_of k)
                    LR.print (LR.make rx) Structs.Ex.print ex
              | Th_util.NCS (k, _) ->
                  fprintf fmt "  > %s ncs: %a (because %a)@ " (theory_of k)
                    LR.print (LR.make rx) Structs.Ex.print ex
              | _ -> assert false)
            choices;
          fprintf fmt "==============================================@."

    let begin_case_split choices =
      if get_debug_split () then
        print_dbg ~module_name:"Theory" ~function_name:"begin_case_split" "%a"
          made_choices choices

    let end_case_split choices =
      if get_debug_split () then
        print_dbg ~module_name:"Theory" ~function_name:"end_case_split" "%a"
          made_choices choices

    (* unused --
       let split_size sz =
       if get_debug_split () then
        print_dbg
        ">size case-split: %s" (Numbers.Q.to_string sz)
    *)

    let print_lr_view fmt ch = LR.print fmt (LR.make ch)

    let split_backtrack neg_c ex_c =
      if get_debug_split () then
        print_dbg ~module_name:"Theory" ~function_name:"split_backtrack"
          "I backtrack on %a : %a" print_lr_view neg_c Structs.Ex.print ex_c

    let split_assume c ex_c =
      if get_debug_split () then
        print_dbg ~module_name:"Theory" ~function_name:"split assume"
          "I assume %a : %a" print_lr_view c Structs.Ex.print ex_c

    let split_backjump c dep =
      if get_debug_split () then
        print_dbg ~module_name:"Theory" ~function_name:"split_backjump"
          "I backjump on %a : %a" print_lr_view c Structs.Ex.print dep

    let query a =
      if get_debug_cc () then
        print_dbg ~module_name:"Theory" ~function_name:"query" "query : %a"
          Structs.Expr.print a

    let split_sat_contradicts_cs filt_choices =
      if get_debug_split () then
        print_dbg ~module_name:"Theory"
          ~function_name:"split_sat_contradicts_cs"
          "The SAT contradicts CS! I'll replay choices@ %a" made_choices
          filt_choices
  end
  (*BISECT-IGNORE-END*)

  type choice_sign =
    | CPos of Structs.Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)

  type choice =
    X.r Structs.Xliteral.view * Th_util.lit_origin * choice_sign * Structs.Ex.t
  (** the choice, the size, choice_sign,  the explication set,
        the explication for this choice. *)

  type t = {
    assumed_set : Structs.Expr.Set.t;
    assumed : (Structs.Expr.t * int * int) list list;
    cs_pending_facts : (Structs.Expr.t * Structs.Ex.t * int * int) list list;
    terms : Structs.Expr.Set.t;
    gamma : CC_X.t;
    gamma_finite : CC_X.t;
    choices : choice list;
  }

  let look_for_sat ?(bad_last = None) ch t base_env l ~for_model =
    let rec aux ch bad_last dl base_env li =
      Util.Options.exec_thread_yield ();
      match (li, bad_last) with
      | [], _ -> (
          Util.Options.tool_req 3 "TR-CCX-CS-Case-Split";
          let l, base_env = CC_X.case_split base_env ~for_model in
          match l with
          | [] -> ({ t with gamma_finite = base_env; choices = List.rev dl }, ch)
          | l ->
              let l =
                List.map
                  (fun (c, is_cs, size) ->
                    Util.Steps.incr_cs_steps ();
                    let exp = Structs.Ex.fresh_exp () in
                    let ex_c_exp =
                      if is_cs then Structs.Ex.add_fresh exp Structs.Ex.empty
                      else Structs.Ex.empty
                    in
                    (* A new explanation in order to track the choice *)
                    (c, size, CPos exp, ex_c_exp))
                  l
              in
              aux ch None dl base_env l)
      | ((c, lit_orig, CNeg, ex_c) as a) :: l, _ ->
          let facts = CC_X.empty_facts () in
          CC_X.add_fact facts (LSem c, ex_c, lit_orig);
          let base_env, ch = CC_X.assume_literals base_env ch facts in
          aux ch bad_last (a :: dl) base_env l
      (* This optimisation is not correct with the current explanation *)
      (* | [(c, lit_orig, CPos exp, ex_c)], Yes (dep,_) -> *)
      (*     let neg_c = CC_X.Rel.choice_mk_not c in *)
      (*     let ex_c = Structs.Ex.union ex_c dep in *)
      (*     Debug.split_backtrack neg_c ex_c; *)
      (*     aux ch No dl base_env [neg_c, Numbers.Q.Int 1, CNeg, ex_c] *)
      | ((c, lit_orig, CPos exp, ex_c_exp) as a) :: l, _ -> (
          try
            Debug.split_assume c ex_c_exp;
            let facts = CC_X.empty_facts () in
            CC_X.add_fact facts (LSem c, ex_c_exp, lit_orig);
            let base_env, ch = CC_X.assume_literals base_env ch facts in
            Util.Options.tool_req 3 "TR-CCX-CS-Normal-Run";
            aux ch bad_last (a :: dl) base_env l
          with Structs.Ex.Inconsistent (dep, classes) -> (
            match Structs.Ex.remove_fresh exp dep with
            | None ->
                (* The choice doesn't participate to the inconsistency *)
                Debug.split_backjump c dep;
                Util.Options.tool_req 3 "TR-CCX-CS-Case-Split-Conflict";
                raise (Structs.Ex.Inconsistent (dep, classes))
            | Some dep ->
                Util.Options.tool_req 3 "TR-CCX-CS-Case-Split-Progress";
                (* The choice participates to the inconsistency *)
                let neg_c = LR.view (LR.neg (LR.make c)) in
                let lit_orig =
                  match lit_orig with
                  | Th_util.CS (k, sz) -> Th_util.NCS (k, sz)
                  | _ -> assert false
                in
                Debug.split_backtrack neg_c dep;
                if get_bottom_classes () then
                  Util.Printer.print_dbg "bottom (case-split):%a"
                    Structs.Expr.print_tagged_classes classes;
                aux ch None dl base_env [ (neg_c, lit_orig, CNeg, dep) ]))
    in
    aux ch bad_last (List.rev t.choices) base_env l

  (* remove old choices involving fresh variables that are no longer in UF *)
  let filter_valid_choice uf (ra, _, _, _) =
    let l =
      match ra with
      | A.Eq (r1, r2) -> [ r1; r2 ]
      | A.Distinct (_, l) -> l
      | A.Builtin (_, _, l) -> l
      | A.Pred (p, _) -> [ p ]
    in
    List.for_all
      (fun r ->
        List.for_all
          (fun x ->
            match X.term_extract x with Some t, _ -> Uf.mem uf t | _ -> true)
          (X.leaves r))
      l

  (* 1. Remove case-split decisions contain fresh variables (introduced by
     theories solvers) that are not in the theories' environment anymore
     (because of backtrack)
     2. Remove implications that are due to decisions removed in 1. *)
  let filter_choices uf (choices : choice list) =
    let candidates_to_keep, to_ignore =
      List.partition (filter_valid_choice uf) choices
    in
    let ignored_decisions =
      List.fold_left
        (fun ex (_, _, ch, _) ->
          match ch with
          | CPos (Structs.Ex.Fresh _ as e) -> Structs.Ex.add_fresh e ex
          | CPos _ -> assert false
          | CNeg -> ex)
        Structs.Ex.empty to_ignore
    in
    List.filter
      (fun (_, _, _, ex) ->
        try
          Structs.Ex.iter_atoms
            (function
              | Structs.Ex.Fresh _ as fr
                when Structs.Ex.mem fr ignored_decisions ->
                  raise Exit
              | _ -> ())
            ex;
          true
        with Exit -> (* ignore implicated related to ignored decisions *)
                     false)
      candidates_to_keep

  let try_it t facts ~for_model =
    Util.Options.exec_thread_yield ();
    Debug.begin_case_split t.choices;
    let r =
      try
        if t.choices == [] then look_for_sat [] t t.gamma [] ~for_model
        else
          try
            let env, ch = CC_X.assume_literals t.gamma_finite [] facts in
            look_for_sat ch t env [] ~for_model
          with Structs.Ex.Inconsistent (dep, classes) ->
            Util.Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
            (* we replay the conflict in look_for_sat, so we can
               safely ignore the explanation which is not useful *)
            let uf = CC_X.get_union_find t.gamma in
            let filt_choices = filter_choices uf t.choices in
            Debug.split_sat_contradicts_cs filt_choices;
            look_for_sat
              ~bad_last:(Some (dep, classes))
              [] { t with choices = [] } t.gamma filt_choices ~for_model
      with Structs.Ex.Inconsistent (d, cl) ->
        Debug.end_case_split t.choices;
        Util.Options.tool_req 3 "TR-CCX-CS-Conflict";
        raise (Structs.Ex.Inconsistent (d, cl))
    in
    Debug.end_case_split (fst r).choices;
    r

  let extract_from_semvalues acc l =
    List.fold_left
      (fun acc r ->
        match X.term_extract r with
        | Some t, _ -> Structs.Expr.Set.add t acc
        | _ -> acc)
      acc l

  let extract_terms_from_choices =
    List.fold_left (fun acc (a, _, _, _) ->
        match a with
        | A.Eq (r1, r2) -> extract_from_semvalues acc [ r1; r2 ]
        | A.Distinct (_, l) -> extract_from_semvalues acc l
        | A.Pred (p, _) -> extract_from_semvalues acc [ p ]
        | _ -> acc)

  let extract_terms_from_assumed =
    List.fold_left (fun acc (a, _, _) ->
        match a with
        | LTerm r -> (
            match Structs.Expr.lit_view r with
            | Structs.Expr.Not_a_lit _ -> assert false
            | Structs.Expr.Eq (t1, t2) ->
                Structs.Expr.Set.add t1 (Structs.Expr.Set.add t2 acc)
            | Structs.Expr.Eql l
            | Structs.Expr.Distinct l
            | Structs.Expr.Builtin (_, _, l) ->
                List.fold_right Structs.Expr.Set.add l acc
            | Structs.Expr.Pred (t1, _) -> Structs.Expr.Set.add t1 acc)
        | _ -> acc)

  let rec is_ordered_list l =
    match l with
    | [] | [ [ _ ] ] -> true
    | [] :: r -> is_ordered_list r
    | [ e ] :: r1 :: r2 -> is_ordered_list ((e :: r1) :: r2)
    | (e1 :: e2 :: l) :: r ->
        let _, d1, p1 = e1 in
        let _, d2, p2 = e2 in
        (d1 > d2 || (d1 = d2 && p1 > p2)) && is_ordered_list ((e2 :: l) :: r)

  let do_case_split t =
    let in_facts_l = t.cs_pending_facts in
    let t = { t with cs_pending_facts = [] } in
    let facts = CC_X.empty_facts () in
    List.iter
      (List.iter (fun (a, ex, _dlvl, _plvl) ->
           CC_X.add_fact facts (LTerm a, ex, Th_util.Other)))
      in_facts_l;

    let t, ch = try_it t facts ~for_model:false in
    let choices = extract_terms_from_choices Structs.Expr.Set.empty t.choices in
    let choices_terms = extract_terms_from_assumed choices ch in

    ( { t with terms = Structs.Expr.Set.union t.terms choices_terms },
      choices_terms )

  (* facts are sorted in decreasing order with respect to (dlvl, plvl) *)
  let assume ordered in_facts t =
    let facts = CC_X.empty_facts () in
    let assumed, assumed_set, cpt =
      List.fold_left
        (fun ((assumed, assumed_set, cpt) as accu) (a, ex, dlvl, plvl) ->
          if Structs.Expr.Set.mem a assumed_set then accu
          else (
            CC_X.add_fact facts (LTerm a, ex, Th_util.Other);
            ( (a, dlvl, plvl) :: assumed,
              Structs.Expr.Set.add a assumed_set,
              cpt + 1 )))
        ([], t.assumed_set, 0) in_facts
    in
    if assumed == [] then (t, Structs.Expr.Set.empty, 0)
    else
      let t =
        {
          t with
          assumed_set;
          assumed = assumed :: t.assumed;
          cs_pending_facts = in_facts :: t.cs_pending_facts;
        }
      in
      if Util.Options.get_profiling () then Structs.Profiling.assume cpt;
      Debug.assumed t.assumed;
      assert ((not ordered) || is_ordered_list t.assumed);

      let gamma, _ = CC_X.assume_literals t.gamma [] facts in
      let new_terms = CC_X.new_terms gamma in
      ( { t with gamma; terms = Structs.Expr.Set.union t.terms new_terms },
        new_terms,
        cpt )

  let get_debug_theories_instances th_instances ilvl dlvl =
    let module MF = Structs.Expr.Map in
    Util.Printer.print_dbg ~flushed:false ~module_name:"Theory"
      ~function_name:"theories_instances"
      "@[<v 2>dec. level = %d, instant.level = %d, %d new Th instances@ " dlvl
      ilvl (List.length th_instances);
    let mp =
      List.fold_left
        (fun acc ((hyps : Structs.Expr.t list), gf, _) ->
          match gf.Structs.Expr.lem with
          | None -> assert false
          | Some lem ->
              let inst = try MF.find lem acc with Not_found -> MF.empty in
              MF.add lem (MF.add gf.Structs.Expr.ff hyps inst) acc)
        MF.empty th_instances
    in
    let l =
      MF.fold (fun f inst acc -> (f, MF.cardinal inst, inst) :: acc) mp []
    in
    let l = List.fast_sort (fun (_, m, _) (_, n, _) -> n - m) l in
    List.iter
      (fun (f, m, inst) ->
        Util.Printer.print_dbg ~flushed:false ~header:false "%3d  -->  %a@ " m
          Structs.Expr.print f;
        if true then
          MF.iter
            (fun f hyps ->
              Util.Printer.print_dbg ~flushed:false ~header:false
                "@[<v 2>[inst]@ ";
              List.iter
                (fun h ->
                  Util.Printer.print_dbg ~flushed:false ~header:false
                    "hypothesis: %a@ " Structs.Expr.print h)
                hyps;
              Util.Printer.print_dbg ~flushed:false ~header:false
                "@]conclusion: %a@ " Structs.Expr.print f)
            inst)
      l;
    Util.Printer.print_dbg ~header:false "@]"

  let theories_instances ~do_syntactic_matching t_match t selector dlvl ilvl =
    let gamma, instances =
      CC_X.theories_instances ~do_syntactic_matching t_match t.gamma selector
    in
    if get_debug_fpa () > 0 then
      get_debug_theories_instances instances dlvl ilvl;
    ({ t with gamma }, instances)

  let query =
    let add_and_process_conseqs a t =
      (* !!! query does not modify gamma_finite anymore *)
      Util.Options.exec_thread_yield ();
      let gamma, facts =
        CC_X.add t.gamma (CC_X.empty_facts ()) a Structs.Ex.empty
      in
      let gamma, _ = CC_X.assume_literals gamma [] facts in
      { t with gamma }
    in
    fun a t ->
      if Util.Options.get_profiling () then Structs.Profiling.query ();
      Util.Options.exec_thread_yield ();
      Debug.query a;
      try
        match Structs.Expr.lit_view a with
        | Structs.Expr.Eq (t1, t2) ->
            let t = add_and_process_conseqs a t in
            CC_X.are_equal t.gamma t1 t2 ~init_terms:false
        | Structs.Expr.Distinct [ t1; t2 ] ->
            let na = Structs.Expr.neg a in
            let t = add_and_process_conseqs na t in
            (* na ? *)
            CC_X.are_distinct t.gamma t1 t2
        | Structs.Expr.Distinct _ | Structs.Expr.Eql _ ->
            (* we only assume toplevel distinct with more that one arg.
               not interesting to do a query in this case ?? or query ? *)
            None
        | Structs.Expr.Pred (t1, b) ->
            let t = add_and_process_conseqs a t in
            if b then CC_X.are_distinct t.gamma t1 Structs.Expr.vrai
            else CC_X.are_equal t.gamma t1 Structs.Expr.vrai ~init_terms:false
        | _ ->
            let na = Structs.Expr.neg a in
            let t = add_and_process_conseqs na t in
            CC_X.query t.gamma na
      with Structs.Ex.Inconsistent (d, classes) -> Some (d, classes)

  let add_term_in_gm gm t =
    let facts = CC_X.empty_facts () in
    let gm, facts = CC_X.add_term gm facts t Structs.Ex.empty in
    fst (CC_X.assume_literals gm [] facts)
  (* may raise Inconsistent *)

  let add_term env t ~add_in_cs =
    let gm = add_term_in_gm env.gamma t in
    if not add_in_cs then { env with gamma = gm }
    else
      { env with gamma = gm; gamma_finite = add_term_in_gm env.gamma_finite t }

  let empty () =
    let env = CC_X.empty () in
    let env, _ =
      CC_X.add_term env (CC_X.empty_facts ()) Structs.Expr.vrai Structs.Ex.empty
    in
    let env, _ =
      CC_X.add_term env (CC_X.empty_facts ()) Structs.Expr.faux Structs.Ex.empty
    in
    let t =
      {
        gamma = env;
        gamma_finite = env;
        choices = [];
        assumed_set = Structs.Expr.Set.empty;
        assumed = [];
        cs_pending_facts = [];
        terms = Structs.Expr.Set.empty;
      }
    in
    let a =
      Structs.Expr.mk_distinct ~iff:false
        [ Structs.Expr.vrai; Structs.Expr.faux ]
    in
    let t, _, _ = assume true [ (a, Structs.Ex.empty, 0, -1) ] t in
    t

  let print_model fmt t = CC_X.print_model fmt t.gamma_finite
  let cl_extract env = CC_X.cl_extract env.gamma

  let assume ?(ordered = true) facts t =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_CC Util.Timers.F_assume;
        let res = assume ordered facts t in
        Util.Timers.exec_timer_pause Util.Timers.M_CC Util.Timers.F_assume;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_CC Util.Timers.F_assume;
        raise e)
    else assume ordered facts t

  let query a t =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_CC Util.Timers.F_query;
        let res = query a t in
        Util.Timers.exec_timer_pause Util.Timers.M_CC Util.Timers.F_query;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_CC Util.Timers.F_query;
        raise e)
    else query a t

  let extract_ground_terms env = env.terms
  let get_real_env t = t.gamma
  let get_case_split_env t = t.gamma_finite

  let compute_concrete_model env =
    fst (try_it env (CC_X.empty_facts ()) ~for_model:true)

  let assume_th_elt t th_elt dep =
    { t with gamma = CC_X.assume_th_elt t.gamma th_elt dep }

  let get_assumed env = env.assumed_set
end

module Main_Empty : S = struct
  type t = { assumed_set : Structs.Expr.Set.t }

  let empty () = { assumed_set = Structs.Expr.Set.empty }

  let assume ?ordered:(_ = true) in_facts t =
    let assumed_set =
      List.fold_left
        (fun assumed_set (a, _, _, _) ->
          if Structs.Expr.Set.mem a assumed_set then assumed_set
          else Structs.Expr.Set.add a assumed_set)
        t.assumed_set in_facts
    in
    ({ assumed_set }, Structs.Expr.Set.empty, 0)

  let query _ _ = None
  let print_model _ _ = ()
  let cl_extract _ = []
  let extract_ground_terms _ = Structs.Expr.Set.empty
  let empty_ccx = CC_X.empty ()
  let get_real_env _ = empty_ccx
  let get_case_split_env _ = empty_ccx
  let do_case_split env = (env, Structs.Expr.Set.empty)
  let add_term env _ ~add_in_cs:_ = env
  let compute_concrete_model e = e
  let assume_th_elt e _ _ = e
  let theories_instances ~do_syntactic_matching:_ _ e _ _ _ = (e, [])
  let get_assumed env = env.assumed_set
end
