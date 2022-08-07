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
open Util.Options

module type S = sig
  type t
  type tbox
  type instances = (Structs.Expr.gformula * Structs.Ex.t) list

  val empty : t
  val add_terms : t -> Structs.Expr.Set.t -> Structs.Expr.gformula -> t
  val add_lemma : t -> Structs.Expr.gformula -> Structs.Ex.t -> t

  val add_predicate :
    t ->
    guard:Structs.Expr.t ->
    name:string ->
    Structs.Expr.gformula ->
    Structs.Ex.t ->
    t

  val ground_pred_defn :
    Structs.Expr.t ->
    t ->
    (Structs.Expr.t * Structs.Expr.t * Structs.Ex.t) option

  val pop : t -> guard:Structs.Expr.t -> t

  val m_lemmas :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Structs.Expr.t -> Structs.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    Util.Util.matching_env ->
    t ->
    tbox ->
    (Structs.Expr.t -> Structs.Expr.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val register_max_term_depth : t -> int -> t

  val matching_terms_info :
    t ->
    Matching_types.info Structs.Expr.Map.t
    * Structs.Expr.t list Structs.Expr.Map.t Structs.Sy.Map.t
end

module Make (X : Theory.S) : S with type tbox = X.t = struct
  module EM = Matching.Make (struct
    include Ccx.Main

    (* This function from Ccx.Main is wrapped to ensure Fresh explanations
       will not leak through Ccx during matching, in which case assertions
       in various places will be raised. *)
    let term_repr t e ~init_term =
      try Ccx.Main.term_repr t ~init_term e
      with Structs.Ex.Inconsistent (d, _) as exn ->
        if Structs.Ex.exists_fresh d then e else raise exn
  end)

  type tbox = X.t
  type instances = (Structs.Expr.gformula * Structs.Ex.t) list
  type guard = Structs.Expr.t

  type t = {
    guards : (Structs.Expr.t * bool) list Structs.Expr.Map.t;
    (* from guards to list of guarded predicates.
       bool = true <-> pred is ground *)
    lemmas : (guard * int * Structs.Ex.t) Structs.Expr.Map.t;
    predicates : (guard * int * Structs.Ex.t) Structs.Expr.Map.t;
    ground_preds : (guard * Structs.Expr.t * Structs.Ex.t) Structs.Expr.Map.t;
        (* key <-> f *)
    matching : EM.t;
  }

  let empty =
    {
      guards = Structs.Expr.Map.empty;
      lemmas = Structs.Expr.Map.empty;
      matching = EM.empty;
      predicates = Structs.Expr.Map.empty;
      ground_preds = Structs.Expr.Map.empty;
    }

  module Debug = struct
    open Util.Printer

    let new_facts_of_axiom ax insts_ok =
      if get_debug_matching () >= 1 && insts_ok != Structs.Expr.Map.empty then
        let name =
          match Structs.Expr.form_view ax with
          | Structs.Expr.Lemma { Structs.Expr.name = s; _ } -> s
          | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
          | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
          | Structs.Expr.Xor _ ->
              "!(no-name)"
          | Structs.Expr.Not_a_form -> assert false
        in
        print_dbg ~module_name:"Instances" ~function_name:"new_facts_of_axiom"
          "[Instances.split_and_filter_insts]@ %3d different new instances \
           generated for %s"
          (Structs.Expr.Map.cardinal insts_ok)
          name

    let new_mround ilvl kind =
      if get_debug_matching () >= 1 then
        print_dbg ~module_name:"Instance" ~function_name:"new_mround"
          "[matching] new %s matching round: ilevel = %d..." kind ilvl
  end

  let add_terms env s gf =
    let infos =
      {
        Matching_types.term_age = gf.Structs.Expr.age;
        term_from_goal = gf.Structs.Expr.gf;
        term_from_formula = gf.Structs.Expr.lem;
        term_from_terms = gf.Structs.Expr.from_terms;
      }
    in
    {
      env with
      matching = Structs.Expr.Set.fold (EM.add_term infos) s env.matching;
    }

  let add_ground_pred env ~guard p np defn ex =
    let gp = Structs.Expr.Map.add p (guard, defn, ex) env.ground_preds in
    let gp = Structs.Expr.Map.add np (guard, Structs.Expr.neg defn, ex) gp in
    let guarded =
      try Structs.Expr.Map.find guard env.guards with Not_found -> []
    in
    let guarded = (p, true) :: (np, true) :: guarded in
    {
      env with
      ground_preds = gp;
      guards = Structs.Expr.Map.add guard guarded env.guards;
    }

  let add_predicate env ~guard ~name gf ex =
    let { Structs.Expr.ff = f; age; _ } = gf in
    let env =
      {
        env with
        matching = EM.max_term_depth env.matching (Structs.Expr.depth f);
      }
    in
    match Structs.Expr.form_view f with
    | Structs.Expr.Iff (f1, f2) ->
        let p =
          Structs.Expr.mk_term (Structs.Sy.name name) [] Structs.Ty.Tbool
        in
        let np = Structs.Expr.neg p in
        let defn =
          if Structs.Expr.equal f1 p then f2
          else if Structs.Expr.equal f2 p then f1
          else assert false
        in
        add_ground_pred env ~guard p np defn ex
    | Structs.Expr.Literal _ ->
        let p =
          Structs.Expr.mk_term (Structs.Sy.name name) [] Structs.Ty.Tbool
        in
        let np = Structs.Expr.neg p in
        let defn =
          if Structs.Expr.equal p f then Structs.Expr.vrai
          else if Structs.Expr.equal np f then Structs.Expr.faux
          else assert false
        in
        add_ground_pred env ~guard p np defn ex
    | Structs.Expr.Lemma _ ->
        let guarded =
          try Structs.Expr.Map.find guard env.guards with Not_found -> []
        in
        {
          env with
          predicates = Structs.Expr.Map.add f (guard, age, ex) env.predicates;
          guards = Structs.Expr.Map.add guard ((f, false) :: guarded) env.guards;
        }
    | Structs.Expr.Not_a_form | Structs.Expr.Unit _ | Structs.Expr.Clause _
    | Structs.Expr.Xor _ | Structs.Expr.Skolem _ | Structs.Expr.Let _ ->
        assert false

  let pop env ~guard =
    try
      let guarded = Structs.Expr.Map.find guard env.guards in
      let ground, non_ground =
        List.fold_left
          (fun (ground, non_ground) (f, is_ground) ->
            if is_ground then (Structs.Expr.Map.remove f ground, non_ground)
            else (ground, Structs.Expr.Map.remove f non_ground))
          (env.ground_preds, env.predicates)
          guarded
      in
      {
        env with
        guards = Structs.Expr.Map.remove guard env.guards;
        predicates = non_ground;
        ground_preds = ground;
      }
    with Not_found -> env

  let ground_pred_defn (p : Structs.Expr.t) env =
    try Some (Structs.Expr.Map.find p env.ground_preds) with Not_found -> None

  let register_max_term_depth env mx =
    { env with matching = EM.max_term_depth env.matching mx }

  let record_this_instance f accepted lorig =
    match Structs.Expr.form_view lorig with
    | Structs.Expr.Lemma { Structs.Expr.name; loc; _ } ->
        Structs.Profiling.new_instance_of name f loc accepted
    | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
    | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
    | Structs.Expr.Xor _ | Structs.Expr.Not_a_form ->
        assert false

  let profile_produced_terms env lorig nf s trs =
    let st0 =
      List.fold_left
        (fun st t -> Structs.Expr.sub_terms st (Structs.Expr.apply_subst s t))
        Structs.Expr.Set.empty trs
    in
    let name, loc, _ =
      match Structs.Expr.form_view lorig with
      | Structs.Expr.Lemma { Structs.Expr.name; main; loc; _ } ->
          (name, loc, main)
      | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
      | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
      | Structs.Expr.Xor _ | Structs.Expr.Not_a_form ->
          assert false
    in
    let st1 = Structs.Expr.max_ground_terms_rec_of_form nf in
    let diff = Structs.Expr.Set.diff st1 st0 in
    let info, _ = EM.terms_info env.matching in
    let _new =
      Structs.Expr.Set.filter (fun t -> not (Structs.Expr.Map.mem t info)) diff
    in
    Structs.Profiling.register_produced_terms name loc st0 st1 diff _new

  let inst_is_seen_during_this_round orig f insts =
    try
      let mp_orig_ok, mp_orig_ko = Structs.Expr.Map.find orig insts in
      Structs.Expr.Map.mem f mp_orig_ok || Structs.Expr.Set.mem f mp_orig_ko
    with Not_found -> false

  let add_accepted_to_acc orig f item insts =
    let mp_orig_ok, mp_orig_ko =
      try Structs.Expr.Map.find orig insts
      with Not_found -> (Structs.Expr.Map.empty, Structs.Expr.Set.empty)
    in
    assert (not (Structs.Expr.Map.mem f mp_orig_ok));
    assert (not (Structs.Expr.Set.mem f mp_orig_ko));
    Structs.Expr.Map.add orig
      (Structs.Expr.Map.add f item mp_orig_ok, mp_orig_ko)
      insts

  let add_rejected_to_acc orig f insts =
    let mp_orig_ok, mp_orig_ko =
      try Structs.Expr.Map.find orig insts
      with Not_found -> (Structs.Expr.Map.empty, Structs.Expr.Set.empty)
    in
    assert (not (Structs.Expr.Map.mem f mp_orig_ok));
    assert (not (Structs.Expr.Set.mem f mp_orig_ko));
    Structs.Expr.Map.add orig
      (mp_orig_ok, Structs.Expr.Set.add f mp_orig_ko)
      insts

  let new_facts _env tbox selector substs =
    List.fold_left
      (fun acc
           ( {
               Matching_types.trigger_formula = f;
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
                 Matching_types.sbs;
                 sty;
                 gen = g;
                 goal = b;
                 s_term_orig = torig;
                 s_lem_orig = lorig;
               } ->
            incr cpt;
            let s = (sbs, sty) in
            match tr.Structs.Expr.guard with
            | Some a when X.query (Structs.Expr.apply_subst s a) tbox == None ->
                acc
            | _ ->
                let nf = Structs.Expr.apply_subst s f in
                (* add the incrementaly guard to nf, if any *)
                let nf = Structs.Expr.mk_imp trigger_increm_guard nf 0 in
                if inst_is_seen_during_this_round orig nf acc then acc
                else
                  let accepted = selector nf orig in
                  if not accepted then add_rejected_to_acc orig nf acc
                  else
                    let p =
                      {
                        Structs.Expr.ff = nf;
                        origin_name = Structs.Expr.name_of_lemma lorig;
                        gdist = -1;
                        hdist = -1;
                        trigger_depth = tr.Structs.Expr.t_depth;
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
                        Structs.Ex.union dep
                          (Structs.Ex.singleton (Structs.Ex.Dep lorig))
                    in
                    incr kept;
                    add_accepted_to_acc orig nf
                      (p, dep, s, tr.Structs.Expr.content)
                      acc)
          acc subst_list)
      Structs.Expr.Map.empty substs

  let split_and_filter_insts env insts =
    Structs.Expr.Map.fold
      (fun orig (mp_orig_ok, mp_orig_ko) acc ->
        Debug.new_facts_of_axiom orig mp_orig_ok;
        let acc =
          Structs.Expr.Map.fold
            (fun _ (p, dep, _, _) (gd, ngd) ->
              if p.Structs.Expr.gf then ((p, dep) :: gd, ngd)
              else (gd, (p, dep) :: ngd))
            mp_orig_ok acc
        in
        if Util.Options.get_profiling () then (
          (* update profiler data *)
          Structs.Expr.Set.iter
            (fun f -> record_this_instance f false orig)
            mp_orig_ko;
          Structs.Expr.Map.iter
            (fun f (_, _, name, tr_ctt) ->
              profile_produced_terms env orig f name tr_ctt;
              record_this_instance f true orig)
            mp_orig_ok);
        acc)
      insts ([], [])

  let sort_facts =
    let rec size f =
      match Structs.Expr.form_view f with
      | Structs.Expr.Unit (f1, f2) -> max (size f1) (size f2)
      | Structs.Expr.Lemma _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
      | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
      | Structs.Expr.Xor _ ->
          Structs.Expr.size f
      | Structs.Expr.Not_a_form -> assert false
    in
    fun lf ->
      List.fast_sort
        (fun (p1, _) (p2, _) ->
          let c = size p1.Structs.Expr.ff - size p2.Structs.Expr.ff in
          if c <> 0 then c
          else Structs.Expr.compare p2.Structs.Expr.ff p1.Structs.Expr.ff)
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
    let guard = Structs.Expr.vrai in
    (* lemmas are already guarded outside instances.ml *)
    let { Structs.Expr.ff = orig; age; _ } = gf in
    let age, dep =
      try
        let _, age', dep' = Structs.Expr.Map.find orig env.lemmas in
        (min age age', Structs.Ex.union dep dep')
      with Not_found -> (age, dep)
    in
    { env with lemmas = Structs.Expr.Map.add orig (guard, age, dep) env.lemmas }

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
