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
open Util.Options

module type S = sig
  type t
  type tbox
  type instances = (Ast.Expr.gformula * Ast.Ex.t) list

  val empty : t
  val add_terms : t -> Ast.Expr.Set.t -> Ast.Expr.gformula -> t
  val add_lemma : t -> Ast.Expr.gformula -> Ast.Ex.t -> t

  val add_predicate :
    t ->
    guard:Ast.Expr.t ->
    name:string ->
    Ast.Expr.gformula ->
    Ast.Ex.t ->
    t

  val ground_pred_defn :
    Ast.Expr.t ->
    t ->
    (Ast.Expr.t * Ast.Expr.t * Ast.Ex.t) option

  val pop : t -> guard:Ast.Expr.t -> t

  val m_lemmas :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Ast.Expr.t -> Ast.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t ->
    Ast.Matching_types.info Ast.Expr.Map.t
    * Ast.Expr.t list Ast.Expr.Map.t Ast.Sy.Map.t
end

module Make (X : Theory.S) : S with type tbox = X.t = struct
  module EM = Matching.Make (struct
      include Ccx.Main

      (* This function from Ccx.Main is wrapped to ensure Fresh explanations
         will not leak through Ccx during matching, in which case assertions
         in various places will be raised. *)
      let term_repr t e ~init_term =
        try Ccx.Main.term_repr t ~init_term e
        with Ast.Ex.Inconsistent (d, _) as exn ->
          if Ast.Ex.exists_fresh d then e else raise exn
    end)

  type tbox = X.t
  type instances = (Ast.Expr.gformula * Ast.Ex.t) list
  type guard = Ast.Expr.t

  type t = {
    guards : (Ast.Expr.t * bool) list Ast.Expr.Map.t;
    (* from guards to list of guarded predicates.
       bool = true <-> pred is ground *)
    lemmas : (guard * int * Ast.Ex.t) Ast.Expr.Map.t;
    predicates : (guard * int * Ast.Ex.t) Ast.Expr.Map.t;
    ground_preds : (guard * Ast.Expr.t * Ast.Ex.t) Ast.Expr.Map.t;
    (* key <-> f *)
    matching : EM.t;
  }

  let empty =
    {
      guards = Ast.Expr.Map.empty;
      lemmas = Ast.Expr.Map.empty;
      matching = EM.empty;
      predicates = Ast.Expr.Map.empty;
      ground_preds = Ast.Expr.Map.empty;
    }

  module Debug = struct
    open Util.Printer

    let new_facts_of_axiom ax insts_ok =
      if get_debug_matching () >= 1 && insts_ok != Ast.Expr.Map.empty then
        let name =
          match Ast.Expr.form_view ax with
          | Ast.Expr.Lemma { Ast.Expr.name = s; _ } -> s
          | Ast.Expr.Unit _ | Ast.Expr.Clause _ | Ast.Expr.Literal _
          | Ast.Expr.Skolem _ | Ast.Expr.Let _ | Ast.Expr.Iff _
          | Ast.Expr.Xor _ ->
            "!(no-name)"
          | Ast.Expr.Not_a_form -> assert false
        in
        print_dbg ~module_name:"Instances" ~function_name:"new_facts_of_axiom"
          "[Instances.split_and_filter_insts]@ %3d different new instances \
           generated for %s"
          (Ast.Expr.Map.cardinal insts_ok)
          name

    let new_mround ilvl kind =
      if get_debug_matching () >= 1 then
        print_dbg ~module_name:"Instance" ~function_name:"new_mround"
          "[matching] new %s matching round: ilevel = %d..." kind ilvl
  end

  let add_terms env s gf =
    let infos =
      {
        Ast.Matching_types.term_age = gf.Ast.Expr.age;
        term_from_goal = gf.Ast.Expr.gf;
        term_from_formula = gf.Ast.Expr.lem;
        term_from_terms = gf.Ast.Expr.from_terms;
      }
    in
    {
      env with
      matching = Ast.Expr.Set.fold (EM.add_term infos) s env.matching;
    }

  let add_ground_pred env ~guard p np defn ex =
    let gp = Ast.Expr.Map.add p (guard, defn, ex) env.ground_preds in
    let gp = Ast.Expr.Map.add np (guard, Ast.Expr.neg defn, ex) gp in
    let guarded =
      try Ast.Expr.Map.find guard env.guards with Not_found -> []
    in
    let guarded = (p, true) :: (np, true) :: guarded in
    {
      env with
      ground_preds = gp;
      guards = Ast.Expr.Map.add guard guarded env.guards;
    }

  let add_predicate env ~guard ~name gf ex =
    let { Ast.Expr.ff = f; age; _ } = gf in
    let env =
      {
        env with
        matching = EM.max_term_depth env.matching (Ast.Expr.depth f);
      }
    in
    match Ast.Expr.form_view f with
    | Ast.Expr.Iff (f1, f2) ->
      let p =
        Ast.Expr.mk_term (Ast.Sy.name name) [] Ast.Ty.Tbool
      in
      let np = Ast.Expr.neg p in
      let defn =
        if Ast.Expr.equal f1 p then f2
        else if Ast.Expr.equal f2 p then f1
        else assert false
      in
      add_ground_pred env ~guard p np defn ex
    | Ast.Expr.Literal _ ->
      let p =
        Ast.Expr.mk_term (Ast.Sy.name name) [] Ast.Ty.Tbool
      in
      let np = Ast.Expr.neg p in
      let defn =
        if Ast.Expr.equal p f then Ast.Expr.vrai
        else if Ast.Expr.equal np f then Ast.Expr.faux
        else assert false
      in
      add_ground_pred env ~guard p np defn ex
    | Ast.Expr.Lemma _ ->
      let guarded =
        try Ast.Expr.Map.find guard env.guards with Not_found -> []
      in
      {
        env with
        predicates = Ast.Expr.Map.add f (guard, age, ex) env.predicates;
        guards = Ast.Expr.Map.add guard ((f, false) :: guarded) env.guards;
      }
    | Ast.Expr.Not_a_form | Ast.Expr.Unit _ | Ast.Expr.Clause _
    | Ast.Expr.Xor _ | Ast.Expr.Skolem _ | Ast.Expr.Let _ ->
      assert false

  let pop env ~guard =
    try
      let guarded = Ast.Expr.Map.find guard env.guards in
      let ground, non_ground =
        List.fold_left
          (fun (ground, non_ground) (f, is_ground) ->
             if is_ground then (Ast.Expr.Map.remove f ground, non_ground)
             else (ground, Ast.Expr.Map.remove f non_ground))
          (env.ground_preds, env.predicates)
          guarded
      in
      {
        env with
        guards = Ast.Expr.Map.remove guard env.guards;
        predicates = non_ground;
        ground_preds = ground;
      }
    with Not_found -> env

  let ground_pred_defn (p : Ast.Expr.t) env =
    try Some (Ast.Expr.Map.find p env.ground_preds) with Not_found -> None

  let register_max_term_depth env mx =
    { env with matching = EM.max_term_depth env.matching mx }

  let record_this_instance f accepted lorig =
    match Ast.Expr.form_view lorig with
    | Ast.Expr.Lemma { Ast.Expr.name; loc; _ } ->
      Ast.Profiling.new_instance_of name f loc accepted
    | Ast.Expr.Unit _ | Ast.Expr.Clause _ | Ast.Expr.Literal _
    | Ast.Expr.Skolem _ | Ast.Expr.Let _ | Ast.Expr.Iff _
    | Ast.Expr.Xor _ | Ast.Expr.Not_a_form ->
      assert false

  let profile_produced_terms env lorig nf s trs =
    let st0 =
      List.fold_left
        (fun st t -> Ast.Expr.sub_terms st (Ast.Expr.apply_subst s t))
        Ast.Expr.Set.empty trs
    in
    let name, loc, _ =
      match Ast.Expr.form_view lorig with
      | Ast.Expr.Lemma { Ast.Expr.name; main; loc; _ } ->
        (name, loc, main)
      | Ast.Expr.Unit _ | Ast.Expr.Clause _ | Ast.Expr.Literal _
      | Ast.Expr.Skolem _ | Ast.Expr.Let _ | Ast.Expr.Iff _
      | Ast.Expr.Xor _ | Ast.Expr.Not_a_form ->
        assert false
    in
    let st1 = Ast.Expr.max_ground_terms_rec_of_form nf in
    let diff = Ast.Expr.Set.diff st1 st0 in
    let info, _ = EM.terms_info env.matching in
    let _new =
      Ast.Expr.Set.filter (fun t -> not (Ast.Expr.Map.mem t info)) diff
    in
    Ast.Profiling.register_produced_terms name loc st0 st1 diff _new

  let inst_is_seen_during_this_round orig f insts =
    try
      let mp_orig_ok, mp_orig_ko = Ast.Expr.Map.find orig insts in
      Ast.Expr.Map.mem f mp_orig_ok || Ast.Expr.Set.mem f mp_orig_ko
    with Not_found -> false

  let add_accepted_to_acc orig f item insts =
    let mp_orig_ok, mp_orig_ko =
      try Ast.Expr.Map.find orig insts
      with Not_found -> (Ast.Expr.Map.empty, Ast.Expr.Set.empty)
    in
    assert (not (Ast.Expr.Map.mem f mp_orig_ok));
    assert (not (Ast.Expr.Set.mem f mp_orig_ko));
    Ast.Expr.Map.add orig
      (Ast.Expr.Map.add f item mp_orig_ok, mp_orig_ko)
      insts

  let add_rejected_to_acc orig f insts =
    let mp_orig_ok, mp_orig_ko =
      try Ast.Expr.Map.find orig insts
      with Not_found -> (Ast.Expr.Map.empty, Ast.Expr.Set.empty)
    in
    assert (not (Ast.Expr.Map.mem f mp_orig_ok));
    assert (not (Ast.Expr.Set.mem f mp_orig_ko));
    Ast.Expr.Map.add orig
      (mp_orig_ok, Ast.Expr.Set.add f mp_orig_ko)
      insts

  let new_facts _env tbox selector substs =
    List.fold_left
      (fun acc
        ( {
          Ast.Matching_types.trigger_formula = f;
          trigger_age = age;
          trigger_dep = dep;
          trigger_orig = orig;
          trigger = tr;
          trigger_increm_guard;
        },
          subst_list ) ->
        let cpt = ref 0 in
        let kept = ref 0 in
        List.fold_left
          (fun acc
            {
              Ast.Matching_types.sbs;
              sty;
              gen = g;
              goal = b;
              s_term_orig = torig;
              s_lem_orig = lorig;
            } ->
            incr cpt;
            let s = (sbs, sty) in
            match tr.Ast.Expr.guard with
            | Some a when X.query (Ast.Expr.apply_subst s a) tbox == None ->
              acc
            | _ ->
              let nf = Ast.Expr.apply_subst s f in
              (* add the incrementaly guard to nf, if any *)
              let nf = Ast.Expr.mk_imp trigger_increm_guard nf 0 in
              if inst_is_seen_during_this_round orig nf acc then acc
              else
                let accepted = selector nf orig in
                if not accepted then add_rejected_to_acc orig nf acc
                else
                  let p =
                    {
                      Ast.Expr.ff = nf;
                      origin_name = Ast.Expr.name_of_lemma lorig;
                      gdist = -1;
                      hdist = -1;
                      trigger_depth = tr.Ast.Expr.t_depth;
                      nb_reductions = 0;
                      age = 1 + max g age;
                      mf = true;
                      gf = b;
                      lem = Some lorig;
                      from_terms = torig;
                      theory_elim = true;
                    }
                  in
                  let dep =
                    if
                      not
                        (Util.Options.get_unsat_core ()
                         || Util.Options.get_profiling ())
                    then dep
                    else
                      (* Dep lorig used to track conflicted instances
                         in profiling mode *)
                      Ast.Ex.union dep
                        (Ast.Ex.singleton (Ast.Ex.Dep lorig))
                  in
                  incr kept;
                  add_accepted_to_acc orig nf
                    (p, dep, s, tr.Ast.Expr.content)
                    acc)
          acc subst_list)
      Ast.Expr.Map.empty substs

  let split_and_filter_insts env insts =
    Ast.Expr.Map.fold
      (fun orig (mp_orig_ok, mp_orig_ko) acc ->
         Debug.new_facts_of_axiom orig mp_orig_ok;
         let acc =
           Ast.Expr.Map.fold
             (fun _ (p, dep, _, _) (gd, ngd) ->
                if p.Ast.Expr.gf then ((p, dep) :: gd, ngd)
                else (gd, (p, dep) :: ngd))
             mp_orig_ok acc
         in
         if Util.Options.get_profiling () then (
           (* update profiler data *)
           Ast.Expr.Set.iter
             (fun f -> record_this_instance f false orig)
             mp_orig_ko;
           Ast.Expr.Map.iter
             (fun f (_, _, name, tr_ctt) ->
                profile_produced_terms env orig f name tr_ctt;
                record_this_instance f true orig)
             mp_orig_ok);
         acc)
      insts ([], [])

  let sort_facts =
    let rec size f =
      match Ast.Expr.form_view f with
      | Ast.Expr.Unit (f1, f2) -> max (size f1) (size f2)
      | Ast.Expr.Lemma _ | Ast.Expr.Clause _ | Ast.Expr.Literal _
      | Ast.Expr.Skolem _ | Ast.Expr.Let _ | Ast.Expr.Iff _
      | Ast.Expr.Xor _ ->
        Ast.Expr.size f
      | Ast.Expr.Not_a_form -> assert false
    in
    fun lf ->
      List.fast_sort
        (fun (p1, _) (p2, _) ->
           let c = size p1.Ast.Expr.ff - size p2.Ast.Expr.ff in
           if c <> 0 then c
           else Ast.Expr.compare p2.Ast.Expr.ff p1.Ast.Expr.ff)
        lf

  let new_facts env tbox selector substs =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match Util.Timers.F_new_facts;
        let res = new_facts env tbox selector substs in
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_new_facts;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_new_facts;
        raise e)
    else new_facts env tbox selector substs

  let mround env axs tbox selector ilvl kind mconf =
    Debug.new_mround ilvl kind;
    Util.Options.tool_req 2 "TR-Sat-Mround";
    let env = { env with matching = EM.add_triggers mconf env.matching axs } in
    let ccx_tbox =
      if mconf.Util.Util.use_cs || mconf.Util.Util.greedy then
        X.get_case_split_env tbox
      else X.get_real_env tbox
    in
    let substs = EM.query mconf env.matching ccx_tbox in
    let insts = new_facts env tbox selector substs in
    let gd, ngd = split_and_filter_insts env insts in
    (sort_facts gd, sort_facts ngd)

  let m_lemmas env tbox selector ilvl mconf =
    mround env env.lemmas tbox selector ilvl "axioms" mconf

  let m_predicates env tbox selector ilvl mconf =
    mround env env.predicates tbox selector ilvl "predicates" mconf

  let add_lemma env gf dep =
    let guard = Ast.Expr.vrai in
    (* lemmas are already guarded outside instances.ml *)
    let { Ast.Expr.ff = orig; age; _ } = gf in
    let age, dep =
      try
        let _, age', dep' = Ast.Expr.Map.find orig env.lemmas in
        (min age age', Ast.Ex.union dep dep')
      with Not_found -> (age, dep)
    in
    { env with lemmas = Ast.Expr.Map.add orig (guard, age, dep) env.lemmas }

  (*** add wrappers to profile exported functions ***)

  let add_terms env s gf =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match Util.Timers.F_add_terms;
        let res = add_terms env s gf in
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_add_terms;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_add_terms;
        raise e)
    else add_terms env s gf

  let add_lemma env gf dep =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match Util.Timers.F_add_lemma;
        let res = add_lemma env gf dep in
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_add_lemma;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_add_lemma;
        raise e)
    else add_lemma env gf dep

  let add_predicate env ~guard ~name gf =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match
          Util.Timers.F_add_predicate;
        let res = add_predicate env ~guard ~name gf in
        Util.Timers.exec_timer_pause Util.Timers.M_Match
          Util.Timers.F_add_predicate;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match
          Util.Timers.F_add_predicate;
        raise e)
    else add_predicate env ~guard ~name gf

  let m_lemmas mconf env tbox selector ilvl =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match Util.Timers.F_m_lemmas;
        let res = m_lemmas env tbox selector ilvl mconf in
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_m_lemmas;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match Util.Timers.F_m_lemmas;
        raise e)
    else m_lemmas env tbox selector ilvl mconf

  let m_predicates mconf env tbox selector ilvl =
    if Util.Options.get_timers () then (
      try
        Util.Timers.exec_timer_start Util.Timers.M_Match
          Util.Timers.F_m_predicates;
        let res = m_predicates env tbox selector ilvl mconf in
        Util.Timers.exec_timer_pause Util.Timers.M_Match
          Util.Timers.F_m_predicates;
        res
      with e ->
        Util.Timers.exec_timer_pause Util.Timers.M_Match
          Util.Timers.F_m_predicates;
        raise e)
    else m_predicates env tbox selector ilvl mconf

  let matching_terms_info env = EM.terms_info env.matching
end
