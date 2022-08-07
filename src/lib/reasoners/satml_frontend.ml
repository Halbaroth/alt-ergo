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

module Make (Th : Theory.S) : Sat_solver_sig.S = struct
  open Util.Options
  open Format
  module SAT = Satml.Make (Th)
  module Inst = Instances.Make (Th)
  module Atom = Structs.Satml_types.Atom
  module FF = Structs.Satml_types.Flat_Formula

  let reset_refs () = Util.Steps.reset_steps ()

  type guards = {
    current_guard : Structs.Expr.t;
    stack_guard : Structs.Expr.t Stack.t;
  }

  type t = {
    satml : SAT.t;
    ff_hcons_env : FF.hcons_env;
    nb_mrounds : int;
    last_forced_normal : int;
    last_forced_greedy : int;
    gamma : (int * FF.t option) Structs.Expr.Map.t;
    conj : (int * Structs.Expr.Set.t) FF.Map.t;
    abstr_of_axs : (FF.t * Atom.atom) Structs.Expr.Map.t;
    axs_of_abstr : (Structs.Expr.t * Atom.atom) Structs.Expr.Map.t;
    proxies : (Atom.atom * Atom.atom list * bool) Util.Util.MI.t;
    inst : Inst.t;
    skolems : Structs.Expr.gformula Structs.Expr.Map.t; (* key <-> f *)
    add_inst : Structs.Expr.t -> bool;
    guards : guards;
  }

  let empty_guards () =
    { current_guard = Structs.Expr.vrai; stack_guard = Stack.create () }

  let init_guards () =
    let guards = empty_guards () in
    Stack.push Structs.Expr.vrai guards.stack_guard;
    guards

  let empty () =
    {
      gamma = Structs.Expr.Map.empty;
      satml = SAT.empty ();
      ff_hcons_env = FF.empty_hcons_env ();
      nb_mrounds = 0;
      last_forced_normal = 0;
      last_forced_greedy = 0;
      conj = FF.Map.empty;
      abstr_of_axs = Structs.Expr.Map.empty;
      axs_of_abstr = Structs.Expr.Map.empty;
      proxies = Util.Util.MI.empty;
      inst = Inst.empty;
      skolems = Structs.Expr.Map.empty;
      guards = init_guards ();
      add_inst = (fun _ -> true);
    }

  let empty_with_inst add_inst = { (empty ()) with add_inst }

  exception Sat of t
  exception Unsat of Structs.Ex.t
  exception I_dont_know of t
  exception IUnsat of t * Structs.Ex.t

  let mk_gf f =
    {
      Structs.Expr.ff = f;
      trigger_depth = max_int;
      nb_reductions = 0;
      origin_name = "<none>";
      age = 0;
      lem = None;
      mf = false;
      gf = false;
      gdist = -1;
      hdist = -1;
      from_terms = [];
      theory_elim = true;
    }

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Util.Printer

    let pred_def f =
      if get_debug_sat () then
        print_dbg ~module_name:"Satml_frontend" ~function_name:"pred_def"
          "I assume a predicate: %a" Structs.Expr.print f

    let unsat gf =
      if get_debug_sat () then
        print_dbg ~module_name:"Satml_frontend" ~function_name:"unsat"
          "unsat of %a ?" Structs.Expr.print gf.Structs.Expr.ff

    let assume gf =
      let { Structs.Expr.ff = f; lem; from_terms = terms; _ } = gf in
      if get_debug_sat () then
        match Structs.Expr.form_view f with
        | Structs.Expr.Not_a_form -> assert false
        | Structs.Expr.Unit _ -> ()
        | Structs.Expr.Clause _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume a clause %a" Structs.Expr.print f
        | Structs.Expr.Lemma _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume a [%d-atom] lemma: %a" (Structs.Expr.size f)
              Structs.Expr.print f
        | Structs.Expr.Literal a ->
            let n =
              match lem with
              | None -> ""
              | Some ff -> (
                  match Structs.Expr.form_view ff with
                  | Structs.Expr.Lemma xx -> xx.Structs.Expr.name
                  | Structs.Expr.Unit _ | Structs.Expr.Clause _
                  | Structs.Expr.Literal _ | Structs.Expr.Skolem _
                  | Structs.Expr.Let _ | Structs.Expr.Iff _ | Structs.Expr.Xor _
                    ->
                      ""
                  | Structs.Expr.Not_a_form -> assert false)
            in
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "@[<v 0>I assume a literal (%s : %a) %a@,\
               ================================================@]"
              n Structs.Expr.print_list terms Structs.Expr.print a
        | Structs.Expr.Skolem _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume a skolem %a" Structs.Expr.print f
        | Structs.Expr.Let _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume a let-In %a" Structs.Expr.print f
        | Structs.Expr.Iff _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume an equivalence %a" Structs.Expr.print f
        | Structs.Expr.Xor _ ->
            print_dbg ~module_name:"Satml_frontend" ~function_name:"assume"
              "I assume a neg-equivalence/Xor %a" Structs.Expr.print f

    let simplified_form f f' =
      if get_debug_sat () && get_verbose () then
        print_dbg ~module_name:"Satml_frontend" ~function_name:"simplified_form"
          "@[<v 2>Simplified form of: %a@,is: %a@]" Structs.Expr.print f
          FF.print f'

    (* unused --
       let cnf_form f unit non_unit =
       if get_debug_sat () && get_verbose () then begin
        print_dbg "[sat] CFF form of: %a" FF.print f;
        print_dbg "  is:";
        List.iter
          (List.iter (fun a ->
          print_dbg "UNIT: %a" Atom.pr_atom a))
          unit;
        List.iter
          (fun c ->
             print_dbg "CLAUSE: ";
             List.iter (fun a ->
             print_dbg "%a or " Atom.pr_atom a) c;
          )non_unit
       end
    *)

    let model fmt env =
      if get_debug_sat () then
        let model = SAT.boolean_model env.satml in
        let print fmt a =
          fprintf fmt " %f | %a@," (Atom.weight a) Atom.pr_atom a
        in
        fprintf fmt "@[<v 2>(2) satML's model:@,%a@]" (pp_list_no_space print)
          (List.rev model)

    let new_instances mode env =
      if get_debug_sat () then (
        print_dbg ~flushed:false ~module_name:"Satml_frontend"
          ~function_name:"new_instances"
          "@[<v 2>I GENERATE NEW INSTANCES (%s)#################@,\
           @[<v 2>(1) ground problem:@,"
          mode;
        FF.Map.iter
          (fun f (md, _) ->
            print_dbg ~flushed:false ~header:false "-> %d : %a@," md FF.print f)
          env.conj;
        print_dbg ~header:false "@]@,%a" model env)

    (* unused --
       let generated_instances l =
       if get_verbose () && get_debug_sat () then begin
        print_dbg "[new_instances] %d generated" (List.length l);
        List.iter (fun { Structs.Expr.ff = f; origin_name; _ } ->
            print_dbg " instance(origin = %s): %a" origin_name Structs.Expr.print f;
          ) l
       end
    *)

    (* unused --
       let trivial_fact p inst =
       if get_verbose () && get_debug_sat () then begin
        if inst then
        print_dbg "already known instance: %a" Structs.Expr.print p
        else
        print_dbg "already known skolem: %a" Structs.Expr.print p
       end
    *)

    (* unused --
       let generated_skolems l =
       if get_verbose () && get_debug_sat () then begin
        print_dbg "[new_skolems] %d generated" (List.length l);
        List.iter (fun { Structs.Expr.ff = f; _ } ->
        print_dbg " skolem: %a" Structs.Expr.print f) l
       end
    *)

    let atoms_from_sat_branch f =
      if get_verbose () && get_debug_sat () then
        print_dbg ~module_name:"Satml_frontend"
          ~function_name:"atoms_from_sat_branch"
          "[extract_and_add_terms from] %a" FF.print f

    let add_terms_of src terms =
      if get_verbose () && get_debug_sat () then (
        print_dbg ~flushed:false ~module_name:"Satml_frontend"
          ~function_name:"add_terms_of" "@[<v 2>[%s] add_terms_of:@," src;
        Structs.Expr.Set.iter
          (fun e ->
            print_dbg ~flushed:false ~header:false ">> %a@," Structs.Expr.print
              e)
          terms;
        print_dbg ~header:false "@]")

    (* unused --
       let axiom_def f =
       if get_debug_sat () then
       print_dbg
       (asprintf "[sat] I assume an axiom: %a" Structs.Expr.print f)
    *)

    let internal_axiom_def f a at =
      if get_debug_sat () then
        print_dbg ~module_name:"Satml_frontend"
          ~function_name:"internal_axiom_def"
          "I assume an internal axiom: %a <-> %a@,at of a is %a"
          Structs.Expr.print a Structs.Expr.print f Atom.pr_atom at

    (* unused --
       let in_mk_theories_instances () =
       if Util.Options.get_debug_fpa() > 0 || get_debug_sat() then
       print_dbg
       "[sat] entering mk_theories_instances:"
    *)

    (* unused --
       let out_mk_theories_instances normal_exit =
       if Util.Options.get_debug_fpa() > 0 || get_debug_sat() then
        if normal_exit then
        print_dbg "[sat] normal exit of mk_theories_instances."
        else
        print_dbg "exit mk_theories_instances with Inconsistency."
    *)

    let print_f_conj fmt hyp =
      match hyp with
      | [] -> fprintf fmt "True"
      | e :: l ->
          fprintf fmt "%a" Structs.Expr.print e;
          List.iter (fun f -> fprintf fmt " /\\  %a" Structs.Expr.print f) l

    let print_theory_instance hyp gf =
      if Util.Options.get_debug_fpa () > 1 || Util.Options.get_debug_sat () then
        print_dbg ~module_name:"Satml_frontend" ~function_name:"theory_instance"
          "@[<v 2>%s >@,hypotheses: %a@,conclusion: %a@]"
          (Structs.Expr.name_of_lemma_opt gf.Structs.Expr.lem)
          print_f_conj hyp Structs.Expr.print gf.Structs.Expr.ff
  end
  (*BISECT-IGNORE-END*)

  let print_propositional_model env fmt =
    let model = SAT.boolean_model env.satml in
    fprintf fmt "Propositional:";
    List.iter
      (fun at -> (fprintf fmt "\n %a" Structs.Expr.print) (Atom.literal at))
      model;
    fprintf fmt "\n@."

  let print_model ~header fmt env =
    Format.print_flush ();
    if header then fprintf fmt "\nModel\n@.";
    print_propositional_model env fmt;
    Th.print_model fmt (SAT.current_tbox env.satml)

  let make_explanation _ = Structs.Ex.empty
  (*
    if get_debug_sat () then
    fprintf fmt "make_explanation of %d clauses@." (List.length lc);
    List.fold_left
    (fun ex ({ST.form = f} as c) ->
    if get_debug_sat () then
    fprintf fmt "unsat_core: %a@." Atom.pr_clause c;
    Structs.Ex.union (Structs.Ex.singleton (Structs.Ex.Dep f)) ex
  )Structs.Ex.empty lc*)

  let selector env f orig =
    (Util.Options.get_cdcl_tableaux () || not (Structs.Expr.Map.mem f env.gamma))
    &&
    match Structs.Expr.form_view orig with
    | Structs.Expr.Lemma _ -> env.add_inst orig
    | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
    | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
    | Structs.Expr.Xor _ ->
        true
    | Structs.Expr.Not_a_form -> assert false

  (* <begin> copied from sat_solvers.ml *)

  let reduce_filters acc (hyp, gf, dep) =
    Debug.print_theory_instance hyp gf;
    let clause =
      List.fold_left
        (fun tmp f ->
          (* we cannot reduce like in DfsSAT *)
          Structs.Expr.mk_or (Structs.Expr.neg f) tmp false 0)
        gf.Structs.Expr.ff hyp
    in
    ({ gf with Structs.Expr.ff = clause }, dep) :: acc

  let mk_theories_instances do_syntactic_matching _remove_clauses env acc =
    let t_match = Inst.matching_terms_info env.inst in
    let tbox = SAT.current_tbox env.satml in
    let _tbox, l =
      (Th.theories_instances ~do_syntactic_matching t_match tbox (selector env)
         env.nb_mrounds 0
       [@ocaml.ppwarning "TODO: modifications made in tbox are lost! improve?"])
    in
    (List.fold_left reduce_filters acc l, match l with [] -> false | _ -> true)

  let syntactic_th_inst remove_clauses env acc =
    mk_theories_instances true remove_clauses env acc

  let semantic_th_inst_rec =
    let rec aux_rec remove_clauses env rnd acc =
      let acc, inst_made = mk_theories_instances false remove_clauses env acc in
      if (not inst_made) || rnd <= 1 then acc
      else aux_rec remove_clauses env (rnd - 1) acc
    in
    fun remove_clauses env rnd acc -> aux_rec remove_clauses env rnd acc

  let mk_theories_inst_rec env rnd =
    let acc, _ = syntactic_th_inst false env [] in
    semantic_th_inst_rec false env rnd acc

  (* <end> copied from sat_solvers.ml *)

  let literals_of_ex ex =
    Structs.Ex.fold_atoms
      (fun e acc ->
        match e with
        | Structs.Ex.Literal a -> a :: acc
        | Structs.Ex.Dep _ | Structs.Ex.RootDep _ -> acc
        (* for debug/profiling/proofs, ignore them *)
        | Structs.Ex.Bj _ | Structs.Ex.Fresh _ -> assert false)
      ex []

  let mround menv env acc =
    let tbox = SAT.current_tbox env.satml in
    let gd2, ngd2 =
      Inst.m_predicates menv env.inst tbox (selector env) env.nb_mrounds
    in
    let l2 = List.rev_append (List.rev gd2) ngd2 in
    if Util.Options.get_profiling () then Structs.Profiling.instances l2;
    (*let env = assume env l2 in*)
    let gd1, ngd1 =
      Inst.m_lemmas menv env.inst tbox (selector env) env.nb_mrounds
    in
    let l1 = List.rev_append (List.rev gd1) ngd1 in
    if Util.Options.get_profiling () then Structs.Profiling.instances l1;
    let l =
      (List.rev_append l2 l1 : (Structs.Expr.gformula * Structs.Ex.t) list)
    in

    let th_insts = mk_theories_inst_rec env 10 in
    let l = List.rev_append th_insts l in
    List.fold_left
      (fun acc (gf, dep) ->
        match literals_of_ex dep with
        | [] -> gf :: acc
        | [ { Atom.lit; _ } ] ->
            {
              gf with
              Structs.Expr.ff =
                Structs.Expr.mk_or gf.Structs.Expr.ff (Structs.Expr.neg lit)
                  false 0;
            }
            :: acc
        | _ -> assert false)
      acc l

  let pred_def env f name dep _loc =
    (* dep currently not used. No unsat-cores in satML yet *)
    Debug.pred_def f;
    let guard = env.guards.current_guard in
    { env with inst = Inst.add_predicate env.inst ~guard ~name (mk_gf f) dep }

  let axiom_def env gf ex = { env with inst = Inst.add_lemma env.inst gf ex }

  let internal_axiom_def ax a at inst =
    Debug.internal_axiom_def ax a at;
    let gax = mk_gf ax in
    let ex = Structs.Ex.singleton (Structs.Ex.Literal at) in
    Inst.add_lemma inst gax ex

  let register_abstraction (env, new_abstr_vars) (f, (af, at)) =
    if get_debug_sat () && get_verbose () then
      Util.Printer.print_dbg ~module_name:"Satml_frontend"
        ~function_name:"register_abstraction" "abstraction of %a is %a"
        Structs.Expr.print f FF.print af;
    let lat = Atom.literal at in
    let new_abstr_vars =
      if not (Atom.is_true at) then at :: new_abstr_vars else new_abstr_vars
    in
    assert (not (Structs.Expr.Map.mem f env.abstr_of_axs));
    assert (not (Structs.Expr.Map.mem lat env.axs_of_abstr));
    let env =
      if Atom.eq_atom at Atom.vrai_atom || Atom.eq_atom at Atom.faux_atom then
        env
      else
        {
          env with
          abstr_of_axs = Structs.Expr.Map.add f (af, at) env.abstr_of_axs;
          axs_of_abstr = Structs.Expr.Map.add lat (f, at) env.axs_of_abstr;
        }
    in
    if Atom.level at = 0 then
      (* at is necessarily assigned if lvl = 0 *)
      if Atom.is_true at then
        (axiom_def env (mk_gf f) Structs.Ex.empty, new_abstr_vars)
      else (
        assert (Atom.is_true (Atom.neg at));
        assert false (* FF.simplify invariant: should not happen *))
    else (
      (* FF.simplify invariant: should not happen *)
      assert (Atom.level at < 0);
      let ded =
        match Structs.Expr.neg f |> Structs.Expr.form_view with
        | Structs.Expr.Skolem q -> Structs.Expr.skolemize q
        | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
        | Structs.Expr.Lemma _ | Structs.Expr.Let _ | Structs.Expr.Iff _
        | Structs.Expr.Xor _ | Structs.Expr.Not_a_form ->
            assert false
      in
      (*XXX TODO: internal skolems*)
      let f = Structs.Expr.mk_or lat ded false 0 in
      let nlat = Structs.Expr.neg lat in
      (* semantics: nlat ==> f *)
      ( { env with skolems = Structs.Expr.Map.add nlat (mk_gf f) env.skolems },
        new_abstr_vars ))

  let expand_skolems env acc sa inst_quantif =
    List.fold_left
      (fun acc a ->
        if get_debug_sat () && get_verbose () then
          Util.Printer.print_dbg ~module_name:"Satml_frontend"
            ~function_name:"expand_skolems" "expand skolem of %a"
            Structs.Expr.print a;
        try
          if inst_quantif a then
            let ({ Structs.Expr.ff = f; _ } as gf) =
              Structs.Expr.Map.find a env.skolems
            in
            if
              (not (Util.Options.get_cdcl_tableaux ()))
              && Structs.Expr.Map.mem f env.gamma
            then acc
            else gf :: acc
          else acc
        with Not_found -> acc)
      acc sa

  let inst_env_from_atoms env acc sa inst_quantif =
    List.fold_left
      (fun (inst, acc) a ->
        let gf = mk_gf Structs.Expr.vrai in
        if get_debug_sat () && get_verbose () then
          Util.Printer.print_dbg ~module_name:"Satml_frontend"
            ~function_name:"inst_env_from_atoms" "terms_of_atom %a"
            Structs.Expr.print a;
        let inst =
          Inst.add_terms inst (Structs.Expr.max_ground_terms_of_lit a) gf
        in
        (* ax <-> a, if ax exists in axs_of_abstr *)
        try
          let ax, at = Structs.Expr.Map.find a env.axs_of_abstr in
          if inst_quantif a then (internal_axiom_def ax a at inst, acc)
          else (inst, acc)
        with Not_found -> (inst, acc))
      (env.inst, acc) sa

  let measure at = (Atom.level at, Atom.weight at, Atom.index at)

  (* smaller is more important *)
  let cmp_tuples (l1, w1, i1) (l2, w2, i2) =
    (* lower decision level is better *)
    let res = compare l1 l2 in
    if res <> 0 then res
    else
      (* higher weight is better hence compare w2 w1 *)
      let res = Stdlib.compare w2 w1 in
      if res <> 0 then res else (* lower index is better *)
                             compare i1 i2

  let max a b = if cmp_tuples a b > 0 then a else b

  (* unused --
     let take_max aux l =
     let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,_) as acc) f ->
          match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz > 0 then (m, l) else acc
        )((-1, -.1., -1), []) l
     in
     if lvl = -1 && ind = -1 then None
     else Some acc
  *)

  (* unused --
     let take_min aux l =
     let ((lvl, _, ind) ,_) as acc =
      List.fold_left (fun ((mz,_) as acc) f ->
          match aux f with
          | None -> acc
          | Some (m, l) ->
            if cmp_tuples m mz < 0 then (m, l) else acc
        )((max_int, -.1., max_int), []) l
     in
     if lvl = max_int && ind = max_int then None
     else Some acc
  *)

  let rec take_normal aux l =
    match l with
    | [] -> None
    | a :: l -> (
        match aux a with None -> take_normal aux l | Some _ as v -> v)

  let atoms_from_sat_branches =
    let rec atoms_from_sat_branch f =
      match FF.view f with
      | FF.UNIT at ->
          if not (Atom.is_true at) then None
          else Some (measure at, [ Atom.literal at ])
      | FF.AND l -> (
          try
            let acc =
              List.fold_left
                (fun (mz, lz) f ->
                  match atoms_from_sat_branch f with
                  | None -> raise Exit
                  | Some (m, l) -> (max m mz, List.rev_append l lz))
                ((-1, -1., -1), [])
                l
            in
            Some acc
          with Exit -> None)
      | FF.OR l -> take_normal atoms_from_sat_branch l
    in
    fun env ->
      FF.Map.fold
        (fun f _ sa ->
          Debug.atoms_from_sat_branch f;
          match atoms_from_sat_branch f with
          | None -> assert false
          | Some (_, l) ->
              List.fold_left (fun sa a -> Structs.Expr.Set.add a sa) sa l)
        env.conj Structs.Expr.Set.empty

  module SA = Structs.Satml_types.Atom.Set

  let atoms_from_lazy_sat =
    let rec add_reasons_graph _todo _done =
      match _todo with
      | [] -> _done
      | a :: _todo ->
          if SA.mem a _done then add_reasons_graph _todo _done
          else
            let _todo =
              List.fold_left
                (fun _todo a -> Atom.neg a :: _todo)
                _todo (Atom.reason_atoms a)
            in
            add_reasons_graph _todo (SA.add a _done)
    in
    fun ~frugal env ->
      let sa = SAT.instantiation_context env.satml env.ff_hcons_env in
      let sa =
        if frugal then sa else add_reasons_graph (SA.elements sa) SA.empty
      in
      SA.fold
        (fun a s -> Structs.Expr.Set.add (Atom.literal a) s)
        sa Structs.Expr.Set.empty

  let atoms_from_lazy_greedy env =
    let aux accu ff =
      let sf =
        try FF.Map.find ff env.conj |> snd
        with Not_found ->
          if FF.equal ff FF.vrai then Structs.Expr.Set.empty
          else (
            Util.Printer.print_err "%a not found in env.conj" FF.print ff;
            assert false)
      in
      Structs.Expr.Set.fold
        (Structs.Expr.atoms_rec_of_form ~only_ground:false)
        sf accu
    in
    let accu =
      FF.Map.fold
        (fun ff _ accu -> aux accu ff)
        (SAT.known_lazy_formulas env.satml)
        Structs.Expr.Set.empty
    in
    (Structs.Expr.Set.union
       (atoms_from_lazy_sat ~frugal:true env)
       (*otherwise, we loose atoms that abstract internal axioms *)
       (aux accu FF.vrai)
     [@ocaml.ppwarning
       "improve terms / atoms extraction in lazy/non-lazy and \
        greedy/non-greedy mode. Separate atoms from terms !"])

  let atoms_from_bmodel env =
    Structs.Expr.Map.fold
      (fun f _ sa -> (Structs.Expr.atoms_rec_of_form ~only_ground:false) f sa)
      env.gamma Structs.Expr.Set.empty

  let instantiation_context env ~greedy_round ~frugal =
    let sa =
      match (greedy_round, get_cdcl_tableaux_inst ()) with
      | false, false -> atoms_from_sat_branches env
      | false, true -> atoms_from_lazy_sat ~frugal env
      | true, false -> atoms_from_bmodel env
      | true, true -> atoms_from_lazy_greedy env
    in
    let inst_quantif =
      if get_cdcl_tableaux_inst () then
        let frugal = atoms_from_lazy_sat ~frugal:true env in
        fun a -> Structs.Expr.Set.mem a frugal
      else fun _ -> true
    in
    ( Structs.Expr.Set.elements sa,
      (inst_quantif
      [@ocaml.ppwarning "Issue for greedy: terms inside lemmas not extracted"])
    )

  let terms_from_dec_proc env =
    let terms = Th.extract_ground_terms (SAT.current_tbox env.satml) in
    Debug.add_terms_of "terms_from_dec_proc" terms;
    let gf = mk_gf Structs.Expr.vrai in
    Inst.add_terms env.inst terms gf

  let instantiate_ground_preds env acc sa =
    (List.fold_left
       (fun acc a ->
         match Inst.ground_pred_defn a env.inst with
         | Some (guard, res, _dep) ->
             (* To be correct in incremental mode, we'll generate the
                formula "guard -> (a -> res)" *)
             let tmp = Structs.Expr.mk_imp a res 0 in
             let tmp = Structs.Expr.mk_imp guard tmp 0 in
             mk_gf tmp :: acc
         | None -> acc)
       acc sa
     [@ocaml.ppwarning
       "!!! Possibles issues du to replacement of atoms that are facts with \
        TRUE by mk_lit (and simplify)"])

  let new_instances use_cs env sa inst_quantif acc =
    let inst, acc = inst_env_from_atoms env acc sa inst_quantif in
    let inst = terms_from_dec_proc { env with inst } in
    mround use_cs { env with inst } acc

  type pending = {
    seen_f : Structs.Expr.Set.t;
    activate : Atom.atom option FF.Map.t;
    new_vars : Atom.var list;
    unit : Atom.atom list list;
    nunit : Atom.atom list list;
    new_abstr_vars : Atom.atom list;
    updated : bool;
  }

  let pre_assume (env, acc) gf =
    let { Structs.Expr.ff = f; _ } = gf in
    if get_debug_sat () && get_verbose () then
      Util.Printer.print_dbg ~module_name:"Satml_frontend"
        ~function_name:"pre_assume" "Entry of pre_assume: Given %a"
        Structs.Expr.print f;
    if Structs.Expr.Set.mem f acc.seen_f then (env, acc)
    else
      let acc = { acc with seen_f = Structs.Expr.Set.add f acc.seen_f } in
      try
        let _, ff = Structs.Expr.Map.find f env.gamma in
        match ff with
        | None ->
            (env, (acc [@ocaml.ppwarning "TODO: should be assert failure?"]))
        | Some ff ->
            if SAT.exists_in_lazy_cnf env.satml ff then (env, acc)
            else
              ( env,
                {
                  acc with
                  activate = FF.Map.add ff None acc.activate;
                  updated = true;
                } )
      with Not_found -> (
        Debug.assume gf;
        match Structs.Expr.form_view f with
        | Structs.Expr.Lemma _ ->
            let ff = FF.vrai in
            let _, old_sf =
              try FF.Map.find ff env.conj
              with Not_found -> (0, Structs.Expr.Set.empty)
            in
            let env =
              {
                env with
                gamma = Structs.Expr.Map.add f (env.nb_mrounds, None) env.gamma;
                conj =
                  FF.Map.add ff
                    (env.nb_mrounds, Structs.Expr.Set.add f old_sf)
                    env.conj;
              }
            in
            (* This assert is not true assert (dec_lvl = 0); *)
            (axiom_def env gf Structs.Ex.empty, { acc with updated = true })
        | Structs.Expr.Not_a_form -> assert false
        | Structs.Expr.Unit _ | Structs.Expr.Clause _ | Structs.Expr.Literal _
        | Structs.Expr.Skolem _ | Structs.Expr.Let _ | Structs.Expr.Iff _
        | Structs.Expr.Xor _ ->
            let ff, axs, new_vars =
              FF.simplify env.ff_hcons_env f
                (fun f -> Structs.Expr.Map.find f env.abstr_of_axs)
                acc.new_vars
            in
            let acc = { acc with new_vars } in
            let cnf_is_in_cdcl = FF.Map.mem ff env.conj in
            let _, old_sf =
              try FF.Map.find ff env.conj
              with Not_found -> (0, Structs.Expr.Set.empty)
            in
            let env =
              {
                env with
                gamma =
                  Structs.Expr.Map.add f (env.nb_mrounds, Some ff) env.gamma;
                conj =
                  FF.Map.add ff
                    (env.nb_mrounds, Structs.Expr.Set.add f old_sf)
                    env.conj;
              }
            in
            Debug.simplified_form f ff;
            let env, new_abstr_vars =
              List.fold_left register_abstraction (env, acc.new_abstr_vars) axs
            in
            let acc = { acc with new_abstr_vars } in

            if FF.equal ff FF.vrai then (env, acc)
            else if cnf_is_in_cdcl then
              (* this means that there exists another E.t that is
                 equivalent to f. These two formulas have the same ff *)
              if SAT.exists_in_lazy_cnf env.satml ff then (env, acc)
              else
                ( env,
                  {
                    acc with
                    activate = FF.Map.add ff None acc.activate;
                    updated = true;
                  } )
            else
              let ff_abstr, new_proxies, proxies_mp, new_vars =
                FF.cnf_abstr env.ff_hcons_env ff env.proxies acc.new_vars
              in
              let env = { env with proxies = proxies_mp } in
              let nunit =
                List.fold_left FF.expand_proxy_defn acc.nunit new_proxies
              in
              let acc =
                {
                  acc with
                  new_vars;
                  nunit;
                  unit = [ ff_abstr ] :: acc.unit;
                  activate = FF.Map.add ff None acc.activate;
                  updated = true;
                }
              in
              (env, acc))

  let cdcl_assume env pending ~dec_lvl =
    let { seen_f; activate; new_vars; unit; nunit; updated; _ } = pending in
    (*
    fprintf fmt "pending : %d distinct forms@." (SE.cardinal seen_f);
    fprintf fmt "pending : %d to activate@." (SFF.cardinal activate);
    fprintf fmt "pending : %d new vars@." (List.length new_vars);
    fprintf fmt "pending : %d unit cnf@." (List.length unit);
    fprintf fmt "pending : %d non-unit cnf@." (List.length nunit);
    fprintf fmt "pending : updated = %b@." updated;
  *)
    if Structs.Expr.Set.is_empty seen_f then (
      assert (FF.Map.is_empty activate);
      assert (new_vars == []);
      assert (unit == []);
      assert (nunit == []);
      assert (not updated))
    else
      try
        let f =
          (Structs.Expr.vrai
          [@ocaml.ppwarning "TODO: should fix for unsat cores generation"])
        in
        SAT.set_new_proxies env.satml env.proxies;
        let nbv = FF.nb_made_vars env.ff_hcons_env in
        let unit, nunit = SAT.new_vars env.satml ~nbv new_vars unit nunit in
        (*update_lazy_cnf done inside assume at the right place *)
        (*SAT.update_lazy_cnf activate ~dec_lvl;*)
        SAT.assume env.satml unit nunit f ~cnumber:0 activate ~dec_lvl
      with
      | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
      | Satml.Sat -> assert false

  let assume_aux_bis ~dec_lvl env l =
    let pending =
      {
        seen_f = Structs.Expr.Set.empty;
        activate = FF.Map.empty;
        new_vars = [];
        unit = [];
        nunit = [];
        updated = false;
        new_abstr_vars = [];
      }
    in
    (*fprintf fmt "@.assume aux: %d@." (List.length l);*)
    let env, pending = List.fold_left pre_assume (env, pending) l in
    cdcl_assume env pending ~dec_lvl;
    (env, pending.updated, pending.new_abstr_vars)

  let rec assume_aux ~dec_lvl env l =
    let env, updated, new_abstr_vars = assume_aux_bis ~dec_lvl env l in
    let bot_abstr_vars =
      (* try to immediately expand newly added skolems *)
      List.fold_left
        (fun acc at ->
          let neg_at = Atom.neg at in
          if Atom.is_true neg_at then Atom.literal neg_at :: acc else acc)
        [] new_abstr_vars
    in
    match bot_abstr_vars with
    | [] -> (env, updated)
    | _ ->
        let res = expand_skolems env [] bot_abstr_vars (fun _ -> true) in
        if res == [] then (env, updated)
        else
          let env, updated' = assume_aux ~dec_lvl env res in
          (env, updated || updated')

  let frugal_mconf () =
    {
      Util.Util.nb_triggers = get_nb_triggers ();
      no_ematching = get_no_ematching ();
      triggers_var = get_triggers_var ();
      use_cs = false;
      backward = Util.Util.Normal;
      greedy = false;
    }

  let normal_mconf () =
    {
      Util.Util.nb_triggers = Stdlib.max 2 (get_nb_triggers () * 2);
      no_ematching = get_no_ematching ();
      triggers_var = get_triggers_var ();
      use_cs = false;
      backward = Util.Util.Normal;
      greedy = false;
    }

  let greedy_mconf () =
    {
      Util.Util.nb_triggers = Stdlib.max 10 (get_nb_triggers () * 10);
      no_ematching = false;
      triggers_var = get_triggers_var ();
      use_cs = true;
      backward = Util.Util.Normal;
      greedy = true;
    }

  let greedier_mconf () =
    {
      Util.Util.nb_triggers = Stdlib.max 10 (get_nb_triggers () * 10);
      no_ematching = false;
      triggers_var = true;
      use_cs = true;
      backward = Util.Util.Normal;
      greedy = true;
    }

  let do_instantiation env sa inst_quantif mconf msg ~dec_lvl =
    Debug.new_instances msg env;
    let l = instantiate_ground_preds env [] sa in
    let l = expand_skolems env l sa inst_quantif in
    let l = new_instances mconf env sa inst_quantif l in
    let env, updated = assume_aux ~dec_lvl env l in
    (env, updated)

  type instantiation_strat = Auto | Force_normal | Force_greedy

  let instantiation env inst_strat dec_lvl =
    let nb_mrounds = env.nb_mrounds in
    match inst_strat with
    | Force_normal ->
        let mconf = frugal_mconf () in
        (* take frugal_mconf if normal is forced *)
        let env = { env with last_forced_normal = nb_mrounds } in
        let sa, inst_quantif =
          instantiation_context env ~greedy_round:false ~frugal:false
        in
        do_instantiation env sa inst_quantif mconf "normal-inst (forced)"
          ~dec_lvl
    | Force_greedy ->
        let mconf = normal_mconf () in
        (*take normal_mconf if greedy is forced*)
        let env = { env with last_forced_greedy = nb_mrounds } in
        let sa, inst_quantif =
          instantiation_context env ~greedy_round:true ~frugal:true
        in
        do_instantiation env sa inst_quantif mconf "greedy-inst (forced)"
          ~dec_lvl
    | Auto ->
        List.fold_left
          (fun ((env, updated) as acc) (mconf, debug, greedy_round, frugal) ->
            if updated then acc
            else
              let sa, inst_quantif =
                instantiation_context env ~greedy_round ~frugal
              in
              do_instantiation env sa inst_quantif mconf debug ~dec_lvl)
          (env, false)
          (match get_instantiation_heuristic () with
          | INormal ->
              [
                (frugal_mconf (), "frugal-inst", false, true);
                (normal_mconf (), "normal-inst", false, false);
              ]
          | IAuto ->
              [
                (frugal_mconf (), "frugal-inst", false, true);
                (normal_mconf (), "normal-inst", false, false);
                (greedier_mconf (), "greedier-inst", true, false);
              ]
          | IGreedy ->
              [
                (greedy_mconf (), "greedy-inst", true, false);
                (greedier_mconf (), "greedier-inst", true, false);
              ])

  let rec unsat_rec env ~first_call:_ : unit =
    try
      SAT.solve env.satml;
      assert false
    with
    | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
    | Satml.Sat -> (
        try
          (*if first_call then SAT.cancel_until 0;*)
          let env =
            { env with nb_mrounds = env.nb_mrounds + 1 }
            [@ocaml.ppwarning
              "TODO: first intantiation a la DfsSAT before searching ..."]
          in
          if Util.Options.get_profiling () then
            Structs.Profiling.instantiation env.nb_mrounds;
          let strat =
            if env.nb_mrounds - env.last_forced_greedy > 1000 then Force_greedy
            else if env.nb_mrounds - env.last_forced_normal > 50 then
              Force_normal
            else Auto
          in
          (*let strat = Auto in*)
          let dec_lvl = SAT.decision_level env.satml in
          let env, updated = instantiation env strat dec_lvl in
          let env, updated =
            if (not updated) && strat != Auto then
              instantiation env Auto dec_lvl
            else (env, updated)
          in
          let dec_lvl' = SAT.decision_level env.satml in
          let env =
            if strat == Auto && dec_lvl' = dec_lvl then
              (* increase chances of forcing Normal each time Auto
                 instantiation doesn't allow to backjump *)
              { env with last_forced_normal = env.last_forced_normal - 1 }
            else env
          in
          if not updated then raise (I_dont_know env);
          unsat_rec env ~first_call:false
        with Structs.Ex.Inconsistent (expl, _cls) -> (
          (*may be raised during matching*)
          try
            SAT.conflict_analyze_and_fix env.satml (Satml.C_theory expl);
            unsat_rec env ~first_call:false
          with
          | Satml.Unsat lc -> raise (IUnsat (env, make_explanation lc))
          | _ -> assert false))

  (* copied from sat_solvers.ml *)
  let max_term_depth_in_sat env =
    let aux mx f = Stdlib.max mx (Structs.Expr.depth f) in
    Structs.Expr.Map.fold (fun f _ mx -> aux mx f) env.gamma 0

  let checks_implemented_features () =
    let fails msg =
      let msg =
        Format.sprintf
          "%S is not implemented in CDCL solver ! Please use the old \
           Tableaux-like SAT solver instead."
          msg
      in
      Structs.Errors.run_error (Structs.Errors.Unsupported_feature msg)
    in
    let open Util.Options in
    if get_interpretation () <> 0 then fails "interpretation";
    if get_save_used_context () then fails "save_used_context";
    if get_unsat_core () then fails "unsat_core";
    if get_all_models () then fails "all_models";
    if get_model () then fails "model"

  let create_guard env =
    let expr_guard = Structs.Expr.fresh_name Structs.Ty.Tbool in
    let ff, axs, new_vars =
      FF.simplify env.ff_hcons_env expr_guard
        (fun f -> Structs.Expr.Map.find f env.abstr_of_axs)
        []
    in
    assert (axs == []);
    match (FF.view ff, new_vars) with
    | FF.UNIT atom_guard, [ v ] ->
        assert (Atom.eq_atom atom_guard v.pa);
        let nbv = FF.nb_made_vars env.ff_hcons_env in
        (* Need to use new_vars function to add the new_var corresponding to
           the atom atom_guard in the satml env *)
        let u, nu = SAT.new_vars env.satml ~nbv new_vars [] [] in
        assert (u == [] && nu == []);
        (expr_guard, atom_guard)
    | _ -> assert false

  let push env to_push =
    Util.Util.loop
      ~f:(fun _n () acc ->
        let expr_guard, atom_guard = create_guard acc in
        SAT.push acc.satml atom_guard;
        Stack.push expr_guard acc.guards.stack_guard;
        Util.Steps.push_steps ();
        { acc with guards = { acc.guards with current_guard = expr_guard } })
      ~max:to_push ~elt:() ~init:env

  let pop env to_pop =
    Util.Util.loop
      ~f:(fun _n () acc ->
        SAT.pop acc.satml;
        let guard_to_neg = Stack.pop acc.guards.stack_guard in
        let inst = Inst.pop ~guard:guard_to_neg env.inst in
        assert (not (Stack.is_empty acc.guards.stack_guard));
        let b = Stack.top acc.guards.stack_guard in
        Util.Steps.pop_steps ();
        { acc with inst; guards = { acc.guards with current_guard = b } })
      ~max:to_pop ~elt:() ~init:env

  let add_guard env gf =
    let current_guard = env.guards.current_guard in
    {
      gf with
      Structs.Expr.ff = Structs.Expr.mk_imp current_guard gf.Structs.Expr.ff 1;
    }

  let unsat env gf =
    checks_implemented_features ();
    let gf = add_guard env gf in
    Debug.unsat gf;
    (*fprintf fmt "FF.unsat@.";*)
    (* In dfs_sat goals' terms are added to env.inst *)
    let env =
      {
        env with
        inst =
          Inst.add_terms env.inst
            (Structs.Expr.max_ground_terms_rec_of_form gf.Structs.Expr.ff)
            gf;
      }
    in
    try
      assert (SAT.decision_level env.satml == 0);
      let env, _updated = assume_aux ~dec_lvl:0 env [ gf ] in
      let max_t = max_term_depth_in_sat env in
      let env =
        { env with inst = Inst.register_max_term_depth env.inst max_t }
      in
      unsat_rec env ~first_call:true;
      assert false
    with IUnsat (_env, dep) ->
      assert (
        Structs.Ex.fold_atoms
          (fun e b ->
            match e with
            | Structs.Ex.Bj _ -> false (* only used in fun_sat *)
            | Structs.Ex.Literal _ | Structs.Ex.Fresh _ ->
                false (* bug if this happens *)
            | Structs.Ex.RootDep _ | Structs.Ex.Dep _ -> b)
          dep true);
      dep

  let assume env gf _dep =
    (* dep currently not used. No unsat-cores in satML yet *)
    assert (SAT.decision_level env.satml == 0);
    try fst (assume_aux ~dec_lvl:0 env [ add_guard env gf ])
    with IUnsat (_env, dep) -> raise (Unsat dep)

  (* instrumentation of relevant exported functions for profiling *)
  let assume t ff dep =
    if not (Util.Options.get_timers ()) then assume t ff dep
    else
      try
        Util.Timers.exec_timer_start Util.Timers.M_Sat Util.Timers.F_assume;
        let t = assume t ff dep in
        Util.Timers.exec_timer_pause Util.Timers.M_Sat Util.Timers.F_assume;
        t
      with exn ->
        Util.Timers.exec_timer_pause Util.Timers.M_Sat Util.Timers.F_assume;
        raise exn

  let unsat t ff =
    if not (Util.Options.get_timers ()) then unsat t ff
    else
      try
        Util.Timers.exec_timer_start Util.Timers.M_Sat Util.Timers.F_unsat;
        let t = unsat t ff in
        Util.Timers.exec_timer_pause Util.Timers.M_Sat Util.Timers.F_unsat;
        t
      with exn ->
        Util.Timers.exec_timer_pause Util.Timers.M_Sat Util.Timers.F_unsat;
        raise exn

  let assume_th_elt env th_elt dep =
    SAT.assume_th_elt env.satml th_elt dep;
    env
end

(*
(*+ no dynamic loading of SAT solvers anymore +*)
let () = Sat_solver.set_current (module Main : Sat_solver_sig.S)
*)
