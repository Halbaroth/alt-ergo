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

open Format
open Options
open Matching_types

module T = Term
module F = Formula
module MF = F.Map
module MT = T.Map
module SubstT = Term.Subst

module type S = sig
  type t
  type theory

  val empty : t

  type pats
  val make:
    max_t_depth:int ->
    Matching_types.info Term.Map.t ->
    Term.t list Term.Map.t Term.Subst.t ->
    pats list ->
    t

  val add_term : term_info -> Term.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers :
    backward:Util.inst_kind -> t -> (int * Explanation.t) Formula.Map.t ->
    grd:bool ->
    t
  val terms_info : t -> info Term.Map.t * T.t list MT.t SubstT.t
  val query : t -> theory -> (trigger_info * gsubst list) list
  val match_one_term : t -> theory -> Term.t -> Term.t -> gsubst list

end

module type Arg = sig
  type t
  val term_repr : t -> Term.t -> init_term:bool -> Term.t
  val are_equal : t -> Term.t -> Term.t -> init_terms:bool -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
end

module Make (X : Arg) : S with type theory = X.t = struct

  type theory = X.t

  type pats =
    F.trigger list *
    int * (* age *)
    F.t * (* lem *)
    F.t * (* lem's form *)
    Explanation.t * (* dep *)
    bool (* grd *)

  type t = {
    fils : T.t list MT.t SubstT.t ;
    info : info MT.t ;
    max_t_depth : int;
    pats : pats list
  }

  exception Echec

  let empty = {
    fils = SubstT.empty ;
    info = MT.empty ;
    pats = [ ];
    max_t_depth = 0;
  }

  let make ~max_t_depth info fils pats = { fils; info; pats; max_t_depth }

  let age_limite = Options.age_bound
  (* l'age limite des termes, au dela ils ne sont pas consideres par le
     matching *)

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let add_term t =
      if debug_matching() >= 3 then
        fprintf fmt "[matching] add_term:  %a@." T.print t

    let matching tr =
      if debug_matching() >= 3 then begin
        fprintf fmt "@.[matching] (multi-)trigger: %a@."
          T.print_list tr.F.content;
        fprintf fmt "========================================================@."
      end

    let match_pats_modulo pat lsubsts =
      if debug_matching() >= 3 then begin
        fprintf fmt "@.match_pat_modulo: %a  with accumulated substs@."
          T.print pat;
        List.iter (fun {sbs=sbs; sty=sty} ->
            fprintf fmt ">>> sbs= %a | sty= %a@."
              (SubstT.print Term.print) sbs Ty.print_subst sty
          )lsubsts
      end

    let match_one_pat {sbs=sbs; sty=sty} pat0 =
      if debug_matching() >= 3 then
        fprintf fmt "@.match_pat: %a  with subst:  sbs= %a | sty= %a @."
          T.print pat0 (SubstT.print Term.print) sbs Ty.print_subst sty


    let match_one_pat_against {sbs=sbs; sty=sty} pat0 t =
      if debug_matching() >= 3 then
        fprintf fmt
          "@.match_pat: %a  against term %a@.with subst:  sbs= %a | sty= %a @."
          T.print pat0
          T.print t
          (SubstT.print Term.print) sbs
          Ty.print_subst sty

    let match_term {sbs=sbs; sty=sty} t pat =
      if debug_matching() >= 3 then
        fprintf fmt
          "[match_term] I match %a against %a with subst: sbs=%a | sty= %a@."
          T.print pat T.print t (SubstT.print Term.print) sbs Ty.print_subst sty

    let match_list {sbs=sbs; sty=sty} pats xs =
      if debug_matching() >= 3 then
        fprintf fmt
          "@.[match_list] I match %a against %a with subst: sbs=%a | sty= %a@."
          T.print_list pats
          T.print_list xs
          (SubstT.print Term.print) sbs
          Ty.print_subst sty

    let match_class_of t cl =
      if debug_matching() >= 3 then
        fprintf fmt "class_of (%a)  = { %a }@."
          T.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " T.print)) cl

    let candidate_substitutions pat_info res =
      if debug_matching() >= 1 then begin
        fprintf fmt "[Matching.matching]@.";
        fprintf fmt "%3d candidate substitutions for Axiom %a with trigger %a@."
          (List.length res)
          F.print pat_info.trigger_orig
          T.print_list pat_info.trigger.F.content;
        if debug_matching() >= 2 then
          List.iter
            (fun gsbt ->
               fprintf fmt " >>> sbs = %a  and  sbty = %a@."
                 (SubstT.print T.print) gsbt.sbs Ty.print_subst gsbt.sty
            )res

      end
  end
  (*BISECT-IGNORE-END*)

  let infos op_gen op_but t g b env =
    try
      let i = MT.find t env.info in
      op_gen i.age g , op_but i.but b
    with Not_found -> g , b

  let add_term info t env =
    Debug.add_term t;
    let rec add_rec env t =
      if MT.mem t env.info then env
      else
        let {T.f=f; xs=xs} = T.view t in
        let env =
          let map_f = try SubstT.find f env.fils with Not_found -> MT.empty in

          (* - l'age d'un terme est le min entre l'age passe en argument
             	     et l'age dans la map
             	     - un terme est en lien avec le but de la PO seulement s'il
             	     ne peut etre produit autrement (d'ou le &&)
             	     - le lemme de provenance est le dernier lemme
             	  *)
          let g, b = infos min (&&) t info.term_age info.term_from_goal env in
          let from_lems =
            List.fold_left
              (fun acc t ->
                 try (MT.find t env.info).lem_orig @ acc
                 with Not_found -> acc)
              (match info.term_from_formula with None -> [] | Some a -> [a])
              info.term_from_terms
          in
          { env with
            fils = SubstT.add f (MT.add t xs map_f) env.fils;
            info =
              MT.add t
                { age=g; lem_orig = from_lems; but=b;
                  t_orig = info.term_from_terms }
                env.info
          }
        in
        List.fold_left add_rec env xs
    in
    if info.term_age > age_limite () then env else add_rec env t

  let add_trigger p env =
    { env with pats = p :: env.pats }

  let all_terms
      f ty env tbox
      {sbs=s_t; sty=s_ty; gen=g; goal=b;
       s_term_orig=s_torig;
       s_lem_orig = s_lorig} lsbt_acc =
    SubstT.fold
      (fun k s l ->
         MT.fold
           (fun t _ l ->
              try
                let s_ty = Ty.matching s_ty ty (T.view t).T.ty in
                let ng , but =
                  try
                    let {age=ng;lem_orig=lem'; but=bt} = MT.find t env.info in
                    max ng g , bt || b
                  with Not_found -> g , b
                in
                (* with triggers that are variables, always normalize substs *)
                let t = X.term_repr tbox t ~init_term:true in
                { sbs = SubstT.add f t s_t;
                  sty = s_ty;
                  gen = ng;
                  goal = but;
                  s_term_orig = t :: s_torig;
                  s_lem_orig = s_lorig;
                }::l
              with Ty.TypeClash _ -> l
           ) s l
      ) env.fils lsbt_acc


  module T2 = struct
    type t = T.t * T.t
    let compare (a, b) (x, y) =
      let c = T.compare a x in if c <> 0 then c else T.compare b y
  end

  module MT2 = Map.Make(T2)

  let wrap_are_equal_generic tbox t s add_terms cache_are_eq_gen =
    try MT2.find (t, s) !cache_are_eq_gen
    with Not_found ->
      let res = X.are_equal tbox t s ~init_terms:add_terms in
      cache_are_eq_gen :=
        MT2.add (t, s) res (MT2.add (s, t) res !cache_are_eq_gen);
      res

  (* These references are reset before and after each call to query.
     If some intermediate functions are exported in the future, the code
     should be adapted. *)
  let cache_are_equal_light = ref MT2.empty
  let cache_are_equal_full  = ref MT2.empty

  let are_equal_light tbox t s =
    wrap_are_equal_generic tbox t s false cache_are_equal_light

  let are_equal_full tbox t s =
    wrap_are_equal_generic tbox t s true cache_are_equal_full

  let add_msymb tbox f t ({sbs=s_t} as sg) max_t_depth =
    if SubstT.mem f s_t then
      let s = SubstT.find f s_t in
      if are_equal_full tbox t s == Sig.No then raise Echec;
      sg
    else
      let t =
        if (T.view t).T.depth > max_t_depth || normalize_instances () then
          X.term_repr tbox t ~init_term:true
        else t
      in
      {sg with sbs=SubstT.add f t s_t}

  let (-@) l1 l2 =
    match l1, l2 with
    | [], _  -> l2
    | _ , [] -> l1
    | _ -> List.fold_left (fun acc e -> e :: acc) l2 (List.rev l1)

  let xs_modulo_records t { Ty.lbs = lbs } =
    List.rev
      (List.rev_map
         (fun (hs, ty) -> T.make (Symbols.Op (Symbols.Access hs)) [t] ty) lbs)

  module SLT = (* sets of lists of terms *)
    Set.Make(struct
      type t = T.t list
      let compare l1 l2 =
        try
          List.iter2
            (fun t1 t2 ->
               let c = T.compare t1 t2 in
               if c <> 0 then raise (Exception.Compared c)
            ) l1 l2;
          0
        with Invalid_argument _ ->
          List.length l1 - List.length l2
           | Exception.Compared n -> n
    end)

  let filter_classes cl tbox =
    if no_Ematching () then cl
    else
      let mtl =
        List.fold_left
          (fun acc xs ->
             let xs =
               List.rev
                 (List.rev_map
                    (fun t -> X.term_repr tbox t ~init_term:false) xs)
             in
             SLT.add xs acc
          ) SLT.empty cl
      in
      SLT.elements mtl

  let plus_of_minus t d ty =
    [T.make (Symbols.Op Symbols.Minus) [t; d] ty ; d]

  let minus_of_plus t d ty =
    [T.make (Symbols.Op Symbols.Plus)  [t; d] ty ; d]

  let linear_arithmetic_matching f_pat pats ty_pat t =
    let {T.f=f ; xs; ty} = T.view t in
    if not (Options.arith_matching ()) ||
       ty != Ty.Tint && ty != Ty.Treal then []
    else
      match f_pat, pats with
      | Symbols.Op Symbols.Plus, [p1; p2] ->
        if T.is_ground p2 then [plus_of_minus t p2 ty]
        else if T.is_ground p1 then [plus_of_minus t p1 ty] else []

      | Symbols.Op Symbols.Minus, [p1; p2] ->
        if T.is_ground p2 then [minus_of_plus t p2 ty]
        else if T.is_ground p1 then [minus_of_plus t p1 ty] else []
      | _ -> []

  let rec match_term env tbox ({sty=s_ty;gen=g;goal=b} as sg) pat t =
    Options.exec_thread_yield ();
    Debug.match_term sg t pat;

    let {T.f=f_pat;xs=pats;ty=ty_pat} = T.view pat in
    let {T.f=f_t} = T.view t in
    match f_pat, f_t with
    |	Symbols.Var hs, _ when String.equal "_" (Hstring.view hs) -> [sg]
    |	Symbols.Var _, _ ->
      let sb =
        (try
           let s_ty = Ty.matching s_ty ty_pat (T.view t).T.ty in
           let g',b' = infos max (||) t g b env in
           add_msymb tbox f_pat t
             { sg with sty=s_ty; gen=g'; goal=b' }
             env.max_t_depth
         with Ty.TypeClash _ -> raise Echec)
      in
      [sb]
    (*| _, Symbols.Var _ ->
      match_term env tbox sg t pat*)
    | _ ->
      try
        let s_ty = Ty.matching s_ty ty_pat (T.view t).T.ty in
        let gsb = { sg with sty = s_ty } in
        if T.is_ground pat &&
           are_equal_light tbox pat t != Sig.No then
          [gsb]
        else
          let cl = if no_Ematching () then [t] else X.class_of tbox t in
          Debug.match_class_of t cl;
          let cl =
            List.fold_left
              (fun l t ->
                 let {T.f=f; xs=xs; ty=ty} = T.view t in
                 if Symbols.compare f_pat f = 0 then xs::l
                 else
                   begin
                     match f_pat, ty with
                     | Symbols.Op (Symbols.Record), Ty.Trecord record ->
                       (xs_modulo_records t record) :: l
                     | _ -> l
                   end
              )[] cl
          in
          let cl = filter_classes cl tbox in
          let cl =
            if cl != [] then cl
            else linear_arithmetic_matching f_pat pats ty_pat t
          in
          List.fold_left
            (fun acc xs ->
               try (match_list env tbox gsb pats xs) -@ acc
               with Echec -> acc
            ) [] cl
      with Ty.TypeClash _ -> raise Echec

  and match_list env tbox sg pats xs =
    Debug.match_list sg pats xs;
    try
      List.fold_left2
        (fun sb_l pat arg ->
           List.fold_left
             (fun acc sg ->
                let aux = match_term env tbox sg pat arg in
                (*match aux with [] -> raise Echec | _  -> BUG !! *)
                List.rev_append aux acc
             ) [] sb_l
        ) [sg] pats xs
    with Invalid_argument _ -> raise Echec

  (* exported *)
  let match_one_term env tbox pat t =
    let sg = {
      Matching_types.sbs = Term.Subst.empty;
      sty = Ty.esubst;
      gen = 0;
      goal = true;
      s_term_orig = [];
      s_lem_orig = F.vrai;
    }
    in
    let {T.f=f; xs=pats; ty=ty} = T.view pat in
    let {T.f=t_f; xs=t_xs; ty=t_ty} = T.view t in
    try
      Debug.match_one_pat_against sg pat t;
      let s_ty = Ty.matching sg.sty ty (T.view t).T.ty in
      let sg =
        { sg with
          sty = s_ty; gen = -1; goal = false;
          s_term_orig = t::sg.s_term_orig }
      in
      match_list env tbox sg pats t_xs
    with Echec | Ty.TypeClash _ -> []


  let match_one_pat env tbox pat0 lsbt_acc sg =
    Debug.match_one_pat sg pat0;
    let pat = T.apply_subst (sg.sbs, sg.sty) pat0 in
    let {T.f=f; xs=pats; ty=ty} = T.view pat in
    match f with
    | Symbols.Var _ -> all_terms f ty env tbox sg lsbt_acc
    | _ ->
      let {sty=sty; gen=g; goal=b} = sg in
      let f_aux t xs lsbt =
        (* maybe put 3 as a rational parameter in the future *)
        let too_big = (T.view t).T.depth > 3 * env.max_t_depth in
        if too_big then lsbt
        else
          try
            Debug.match_one_pat_against sg pat0 t;
            let s_ty = Ty.matching sty ty (T.view t).T.ty in
            let gen, but = infos max (||) t g b env in
            let sg =
              { sg with
                sty = s_ty; gen = gen; goal = but;
                s_term_orig = t::sg.s_term_orig }
            in
            let aux = match_list env tbox sg pats xs in
            List.rev_append aux lsbt
          with Echec | Ty.TypeClash _ -> lsbt
      in
      try MT.fold f_aux (SubstT.find f env.fils) lsbt_acc
      with Not_found -> lsbt_acc

  let match_pats_modulo env tbox lsubsts pat =
    Debug.match_pats_modulo pat lsubsts;
    List.fold_left (match_one_pat env tbox pat) [] lsubsts

  let trig_weight s t =
    match T.view s, T.view t with
    | {T.f=Symbols.Name _}, {T.f=Symbols.Op _}   -> -1
    | {T.f=Symbols.Op _}  , {T.f=Symbols.Name _} -> 1
    | _ -> (T.view t).T.depth - (T.view s).T.depth


  let matching env tbox pat_info =
    let pats = pat_info.trigger in
    let pats_list = List.stable_sort trig_weight pats.F.content in
    Debug.matching pats;
    if List.length pats_list > Options.max_multi_triggers_size () then
      pat_info, []
    else
      let egs =
        { sbs = SubstT.empty;
          sty = Ty.esubst;
          gen = 0;
          goal = false;
          s_term_orig = [];
          s_lem_orig = pat_info.trigger_orig;
        }
      in
      match pats_list with
      | []  -> pat_info, []
      | [_] ->
        let res = List.fold_left (match_pats_modulo env tbox) [egs] pats_list in
        Debug.candidate_substitutions pat_info res;
        pat_info, res
      | _ ->
        let cpt = ref 1 in
        try
          List.iter
            (fun pat ->
               cpt := !cpt * List.length (match_pats_modulo env tbox [egs] pat);
               (* TODO: put an adaptive limit *)
               if !cpt = 0 || !cpt > 10_000 then raise Exit
            ) (List.rev pats_list);
          let res =
            List.fold_left (match_pats_modulo env tbox) [egs] pats_list
          in
          Debug.candidate_substitutions pat_info res;
          pat_info, res
        with Exit ->
          if verbose() then
            fprintf fmt "@.skip matching for %a : cpt = %d@."
              F.print pat_info.trigger_orig !cpt;
          pat_info, []

  let reset_cache_refs () =
    cache_are_equal_light := MT2.empty;
    cache_are_equal_full  := MT2.empty





  let matching_one env tbox age lem f dep tr =
    let pat_info =
      { trigger = tr;
        trigger_age = age ;
        trigger_orig = lem ;
        trigger_formula = f ;
        trigger_dep = dep}
    in
    matching env tbox pat_info

  let matching_all env tbox acc (tgs, age, lem, f, dep, grd) =
    if grd then
      List.fold_left
        (fun acc tr ->
           (matching_one env tbox age lem f dep tr) :: acc) acc tgs
    else
      let default, others = List.partition (fun t -> t.F.default) tgs in
      let ok = ref false in
      let acc =
        List.fold_left
          (fun acc tr ->
             match matching_one env tbox age lem f dep tr with
             | (_, []) -> acc
             | res -> ok := true; res :: acc
          ) acc default
      in
      let acc = ref acc in
      let others =
        List.stable_sort
          (fun t1 t2 -> !(t1.F.nb_success) - !(t2.F.nb_success))
          others
      in
      let others = ref others in
      try
        while greedy () || not !ok do
          match !others with
            [] -> raise Exit
          | tr :: l ->
            others := l;
            match matching_one env tbox age lem f dep tr with
            | (_, []) -> ()
            | res ->
              ok := true;
              incr tr.F.nb_success;
              acc := res :: !acc
        done;
        !acc
      with Exit -> !acc




  let query env tbox =
    reset_cache_refs ();
    try
      let res = List.fold_left (matching_all env tbox) [] env.pats in
      reset_cache_refs ();
      res
    with e ->
      reset_cache_refs ();
      raise e

  let query env tbox =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Match Timers.F_query;
        let res = query env tbox in
        Timers.exec_timer_pause Timers.M_Match Timers.F_query;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Match Timers.F_query;
        raise e
    else query env tbox

  let max_term_depth env mx = {env with max_t_depth = max env.max_t_depth mx}

  let add_triggers ~backward env formulas ~grd =
    MF.fold
      (fun lem (age, dep) env ->
         match F.view lem with
         | F.Lemma {F.triggers = tgs0; main = f;
                    backward_triggers=tgs1; forward_triggers=tgs2} ->
           let tgs =
             match backward with
             | Util.Normal -> tgs0
             | Util.Backward -> Lazy.force tgs1
             | Util.Forward -> Lazy.force tgs2
           in
           add_trigger (tgs, age, lem, f, dep, grd) env
         | _ -> assert false
      ) formulas env

  let terms_info env = env.info, env.fils

end
