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
            
open Util.Options
open Format
module Sh = Shostak.Adt
open Sh

module MX = Shostak.MXH
module LR = Uf.LX
module SLR = Set.Make (LR)

type t = {
  classes : Ast.Expr.Set.t list;
  domains : (Util.Hstring.Set.t * Ast.Ex.t) MX.t;
  seen_destr : Ast.Expr.Set.t;
  seen_access : Ast.Expr.Set.t;
  seen_testers : Util.Hstring.Set.t MX.t;
  [@ocaml.ppwarning
    "selectors should be improved. only representatives in it. No true or \
     false _is"]
  selectors : (Ast.Expr.t * Ast.Ex.t) list Util.Hstring.Map.t MX.t;
  size_splits : Util.Numbers.Q.t;
  new_terms : Ast.Expr.Set.t;
  pending_deds : (r Intf.Relation.literal * Ast.Ex.t * Ast.Th_util.lit_origin) list;
  }
       type r = Shostak.Combine.r
       type uf = Uf.t

let empty classes =
  {
    classes;
    domains = MX.empty;
    seen_destr = Ast.Expr.Set.empty;
    seen_access = Ast.Expr.Set.empty;
    seen_testers = MX.empty;
    selectors = MX.empty;
    size_splits = Util.Numbers.Q.one;
    new_terms = Ast.Expr.Set.empty;
    pending_deds = [];
  }

(* ################################################################ *)
(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Util.Printer

  let assume a =
    if get_debug_adt () then
      print_dbg ~module_name:"Adt_rel" ~function_name:"assume" " we assume %a"
        LR.print (LR.make a)

  let print_env loc env =
    if get_debug_adt () then (
      print_dbg ~flushed:false ~module_name:"Adt_rel" ~function_name:"print_env"
        "@ @[<v 2>--ADT env %s ---------------------------------@ " loc;
      MX.iter
        (fun r (hss, ex) ->
           print_dbg ~flushed:false ~header:false "%a 's domain is " Shostak.Combine.print r;
           (match Util.Hstring.Set.elements hss with
            | [] -> ()
            | hs :: l ->
              print_dbg ~flushed:false ~header:false "{ %s"
                (Util.Hstring.view hs);
              List.iter
                (fun hs ->
                   print_dbg ~flushed:false ~header:false " | %s"
                     (Util.Hstring.view hs))
                l);
           print_dbg ~flushed:false ~header:false " } %a@ " Ast.Ex.print ex)
        env.domains;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- seen testers ---------------------------@ ";
      MX.iter
        (fun r hss ->
           Util.Hstring.Set.iter
             (fun hs ->
                print_dbg ~flushed:false ~header:false "(%a is %a)@ " Shostak.Combine.print r
                  Util.Hstring.print hs)
             hss)
        env.seen_testers;
      print_dbg ~flushed:false ~header:false
        "@]@ @[<v 2>-- selectors ------------------------------@ ";
      MX.iter
        (fun r mhs ->
           Util.Hstring.Map.iter
             (fun hs l ->
                List.iter
                  (fun (a, _) ->
                     print_dbg ~flushed:false ~header:false "(%a is %a) ==> %a@ "
                       Shostak.Combine.print r Util.Hstring.print hs Ast.Expr.print a)
                  l)
             mhs)
        env.selectors;
      print_dbg ~header:false "@]@ -------------------------------------------")

  (* unused --
     let case_split r r' =
     if get_debug_adt () then
       Util.Printer.print_dbg
          "[ADT.case-split] %a = %a" Shostak.Combine.print r Shostak.Combine.print r'
  *)

  let no_case_split () =
    if get_debug_adt () then
      print_dbg ~module_name:"Adt_rel" ~function_name:"case-split" "nothing"

  let add r =
    if get_debug_adt () then
      print_dbg ~module_name:"Adt_rel" ~function_name:"add" "%a" Shostak.Combine.print r
end
(*BISECT-IGNORE-END*)
(* ################################################################ *)

let print_model _ _ _ = ()
let new_terms env = env.new_terms
let instantiate ~do_syntactic_matching:_ _ env _ _ = (env, [])

let assume_th_elt t th_elt _ =
  match th_elt.Ast.Expr.extends with
  | Util.Util.Adt -> failwith "This Theory does not support theories extension"
  | _ -> t

let seen_tester r hs env =
  try Util.Hstring.Set.mem hs (MX.find r env.seen_testers)
  with Not_found -> false

let deduce_is_constr uf r h eqs env ex =
  let r, ex' = try Uf.find_r uf r with Not_found -> assert false in
  let ex = Ast.Ex.union ex ex' in
  match embed r with
  | Adt.Alien r -> (
      match Shostak.Combine.term_extract r with
      | Some t, _ -> (
          let eqs =
            if seen_tester r h env then eqs
            else
              let is_c =
                Ast.Expr.mk_builtin ~is_pos:true (Ast.Sy.IsConstr h)
                  [ t ]
              in
              if get_debug_adt () then
                Util.Printer.print_dbg ~module_name:"Adt_rel"
                  ~function_name:"deduce_is_constr" "%a" Ast.Expr.print is_c;
              (Intf.Relation.LTerm is_c, ex, Ast.Th_util.Other) :: eqs
          in
          match Ast.Expr.term_view t with
          | Ast.Expr.Not_a_term _ -> assert false
          | Ast.Expr.Term
              { Ast.Expr.ty = Ast.Ty.Tadt (name, params) as ty; _ } ->
            (* Only do this deduction for finite types ??
                 may not terminate in some cases otherwise.
                 eg. type t = A of t
                 goal g: forall e,e' :t. e = C(e') -> false
                 + should not be guareded by "seen_tester"
            *)
            let cases =
              match Ast.Ty.type_body name params with
              | Ast.Ty.Adt cases -> cases
            in
            let { Ast.Ty.destrs; _ } =
              try
                List.find
                  (fun { Ast.Ty.constr = c; _ } -> Util.Hstring.equal h c)
                  cases
              with Not_found -> assert false
            in
            let xs =
              List.map (fun (_, ty) -> Ast.Expr.fresh_name ty) destrs
            in
            let cons =
              Ast.Expr.mk_term
                (Ast.Sy.constr (Util.Hstring.view h))
                xs ty
            in
            let env =
              { env with new_terms = Ast.Expr.Set.add cons env.new_terms }
            in
            let eq = Ast.Expr.mk_eq t cons ~iff:false in
            if get_debug_adt () then
              Util.Printer.print_dbg ~module_name:"Adt_rel"
                ~function_name:"deduce equal to constr" "%a"
                Ast.Expr.print eq;
            let eqs = (Intf.Relation.LTerm eq, ex, Ast.Th_util.Other) :: eqs in
            (env, eqs)
          | _ -> (env, eqs))
      | _ ->
        Util.Printer.print_err "%a" Shostak.Combine.print r;
        assert false)
  | _ -> (env, eqs)

let values_of ty =
  match ty with
  | Ast.Ty.Tadt (name, params) ->
    let l =
      match Ast.Ty.type_body name params with
      | Ast.Ty.Adt cases -> cases
    in
    Some
      (List.fold_left
         (fun st { Ast.Ty.constr; _ } -> Util.Hstring.Set.add constr st)
         Util.Hstring.Set.empty l)
  | _ -> None

let add_adt env uf t r sy ty =
  if MX.mem r env.domains then env
  else
    match (sy, ty) with
    | Ast.Sy.Op (Ast.Sy.Constr hs), Ast.Ty.Tadt _ ->
      if get_debug_adt () then
        Util.Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"add_adt"
          "new ADT expr(C): %a" Ast.Expr.print t;
      {
        env with
        domains =
          MX.add r
            (Util.Hstring.Set.singleton hs, Ast.Ex.empty)
            env.domains;
      }
    | _, Ast.Ty.Tadt _ ->
      if get_debug_adt () then
        Util.Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"add_adt"
          "new ADT expr: %a" Ast.Expr.print t;
      let constrs =
        match values_of ty with None -> assert false | Some s -> s
      in
      let env =
        {
          env with
          domains = MX.add r (constrs, Ast.Ex.empty) env.domains;
        }
      in
      if Util.Hstring.Set.cardinal constrs = 1 then
        let h' = Util.Hstring.Set.choose constrs in
        let env, pending_deds =
          deduce_is_constr uf r h' env.pending_deds env Ast.Ex.empty
        in
        { env with pending_deds }
      else env
    | _ -> env

let update_tester r hs env =
  let old =
    try MX.find r env.seen_testers with Not_found -> Util.Hstring.Set.empty
  in
  {
    env with
    seen_testers = MX.add r (Util.Hstring.Set.add hs old) env.seen_testers;
  }

let trivial_tester r hs =
  match embed r with
  (* can filter further/better *)
  | Adt.Constr { c_name; _ } -> Util.Hstring.equal c_name hs
  | _ -> false

let constr_of_destr ty dest =
  if get_debug_adt () then
    Util.Printer.print_dbg ~module_name:"Adt_rel"
      ~function_name:"constr_of_destr" "ty = %a" Ast.Ty.print ty;
  match ty with
  | Ast.Ty.Tadt (name, params) -> (
      let cases =
        match Ast.Ty.type_body name params with
        | Ast.Ty.Adt cases -> cases
      in
      try
        List.find
          (fun { Ast.Ty.destrs; _ } ->
             List.exists (fun (d, _) -> Util.Hstring.equal dest d) destrs)
          cases
      with Not_found -> assert false (* invariant *))
  | _ -> assert false
[@@ocaml.ppwarning
  "XXX improve. For each selector, store its corresponding constructor when \
   typechecking ?"]

let add_guarded_destr env uf t hs e t_ty =
  if get_debug_adt () then
    Util.Printer.print_dbg ~flushed:false ~module_name:"Adt_rel"
      ~function_name:"add_guarded_destr" "new (guarded) Destr: %a@ "
      Ast.Expr.print t;
  let env = { env with seen_destr = Ast.Expr.Set.add t env.seen_destr } in
  let { Ast.Ty.constr = c; _ } =
    constr_of_destr (Ast.Expr.type_info e) hs
  in
  let access =
    Ast.Expr.mk_term
      (Ast.Sy.destruct (Util.Hstring.view hs) ~guarded:false)
      [ e ] t_ty
  in
  (* XXX : Never add non-guarded access to list of new terms !
     This may/will introduce bugs when instantiating
     let env = {env with new_terms = Ast.Expr.Set.add access env.new_terms} in
  *)
  let is_c =
    Ast.Expr.mk_builtin ~is_pos:true (Ast.Sy.IsConstr c) [ e ]
  in
  let eq = Ast.Expr.mk_eq access t ~iff:false in
  if get_debug_adt () then
    Util.Printer.print_dbg ~header:false "associated with constr %a@,%a => %a"
      Util.Hstring.print c Ast.Expr.print is_c Ast.Expr.print eq;
  let r_e, ex_e = try Uf.find uf e with Not_found -> assert false in
  if trivial_tester r_e c then
    {
      env with
      pending_deds = (Intf.Relation.LTerm eq, ex_e, Ast.Th_util.Other) :: env.pending_deds;
    }
  else if seen_tester r_e c env then
    {
      env with
      pending_deds = (Intf.Relation.LTerm eq, ex_e, Ast.Th_util.Other) :: env.pending_deds;
    }
  else
    let m_e =
      try MX.find r_e env.selectors with Not_found -> Util.Hstring.Map.empty
    in
    let old = try Util.Hstring.Map.find c m_e with Not_found -> [] in
    {
      env with
      selectors =
        MX.add r_e
          (Util.Hstring.Map.add c ((eq, ex_e) :: old) m_e)
          env.selectors;
    }
[@@ocaml.ppwarning "working with Shostak.Combine.term_extract r would be sufficient ?"]

let add_aux env (uf : uf) (r : r) t =
  if get_disable_adts () then env
  else
    let { Ast.Expr.f = sy; xs; ty; _ } =
      match Ast.Expr.term_view t with
      | Ast.Expr.Term t -> t
      | Ast.Expr.Not_a_term _ -> assert false
    in
    let env = add_adt env uf t r sy ty in
    match (sy, xs) with
    | Ast.Sy.Op (Ast.Sy.Destruct (hs, true)), [ e ] ->
      (* guarded *)
      if get_debug_adt () then
        Util.Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"add_aux"
          "add guarded destruct: %a" Ast.Expr.print t;
      if Ast.Expr.Set.mem t env.seen_destr then env
      else add_guarded_destr env uf t hs e ty
    | Ast.Sy.Op (Ast.Sy.Destruct (_, false)), [ _ ] ->
      (* not guarded *)
      if get_debug_adt () then
        Util.Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"add_aux"
          "[ADTs] add unguarded destruct: %a" Ast.Expr.print t;
      { env with seen_access = Ast.Expr.Set.add t env.seen_access }
    | Ast.Sy.Op (Ast.Sy.Destruct _), _ ->
      assert false (* not possible *)
    (*| Ast.Sy.Op Ast.Sy.IsConstr _, _ ->
      if get_debug_adt () then
      Util.Printer.print_dbg
      "new Tester: %a" E.print t;
       { env with seen_testers = Ast.Expr.Set.add t env.seen_testers }
    *)
    | _ -> env

let add env (uf : uf) (r : r) t = (add_aux env (uf : uf) (r : r) t, [])

let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_, _, _, i) ->
         match i with
         | Ast.Th_util.CS (Ast.Th_util.Th_sum, n) -> Util.Numbers.Q.mult nb n
         | _ -> nb)
      env.size_splits la
  in
  { env with size_splits = nb }

let add_diseq uf hss sm1 sm2 dep env eqs =
  match (sm1, sm2) with
  | Adt.Alien r, Adt.Constr { c_name = h; c_args = []; _ }
  | Adt.Constr { c_name = h; c_args = []; _ }, Adt.Alien r ->
    (* not correct with args *)
    let enum, ex =
      try MX.find r env.domains with Not_found -> (hss, Ast.Ex.empty)
    in
    let enum = Util.Hstring.Set.remove h enum in
    let ex = Ast.Ex.union ex dep in
    if Util.Hstring.Set.is_empty enum then
      raise (Ast.Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with domains = MX.add r (enum, ex) env.domains } in
      if Util.Hstring.Set.cardinal enum = 1 then
        let h' = Util.Hstring.Set.choose enum in
        let env, eqs = deduce_is_constr uf r h' eqs env ex in
        (env, eqs)
      else (env, eqs)
  | Adt.Alien _, Adt.Constr _ | Adt.Constr _, Adt.Alien _ -> (env, eqs)
  | Adt.Alien r1, Adt.Alien r2 ->
    let enum1, ex1 =
      try MX.find r1 env.domains with Not_found -> (hss, Ast.Ex.empty)
    in
    let enum2, ex2 =
      try MX.find r2 env.domains with Not_found -> (hss, Ast.Ex.empty)
    in

    let env, eqs =
      if Util.Hstring.Set.cardinal enum1 = 1 then
        let ex = Ast.Ex.union dep ex1 in
        let h' = Util.Hstring.Set.choose enum1 in
        deduce_is_constr uf r1 h' eqs env ex
      else (env, eqs)
    in
    let env, eqs =
      if Util.Hstring.Set.cardinal enum2 = 1 then
        let ex = Ast.Ex.union dep ex2 in
        let h' = Util.Hstring.Set.choose enum2 in
        deduce_is_constr uf r2 h' eqs env ex
      else (env, eqs)
    in
    (env, eqs)
  | _ -> (env, eqs)

let assoc_and_remove_selector hs r env =
  try
    let mhs = MX.find r env.selectors in
    let deds = Util.Hstring.Map.find hs mhs in
    let mhs = Util.Hstring.Map.remove hs mhs in
    ( deds,
      if Util.Hstring.Map.is_empty mhs then
        { env with selectors = MX.remove r env.selectors }
      else { env with selectors = MX.add r mhs env.selectors } )
  with Not_found -> ([], env)

let assume_is_constr uf hs r dep env eqs =
  match embed r with
  | Adt.Constr { c_name; _ } when not (Util.Hstring.equal c_name hs) ->
    raise (Ast.Ex.Inconsistent (dep, env.classes))
  | _ ->
    if get_debug_adt () then
      Util.Printer.print_dbg ~module_name:"Adt_rel"
        ~function_name:"assume_is_constr" "assume is constr %a %a" Shostak.Combine.print r
        Util.Hstring.print hs;
    if seen_tester r hs env then (env, eqs)
    else
      let deds, env = assoc_and_remove_selector hs r env in
      let eqs =
        List.fold_left
          (fun eqs (ded, dep') ->
             (Intf.Relation.LTerm ded, Ast.Ex.union dep dep', Ast.Th_util.Other)
             :: eqs)
          eqs deds
      in
      let env = update_tester r hs env in

      let enum, ex =
        try MX.find r env.domains
        with Not_found -> (
            (*Cannot just put assert false !
              some terms are not well inited *)
            match values_of (Shostak.Combine.type_info r) with
            | None -> assert false
            | Some s -> (s, Ast.Ex.empty))
      in
      let ex = Ast.Ex.union ex dep in
      if not (Util.Hstring.Set.mem hs enum) then
        raise (Ast.Ex.Inconsistent (ex, env.classes));
      let env, eqs = deduce_is_constr uf r hs eqs env ex in
      ( {
        env with
        domains = MX.add r (Util.Hstring.Set.singleton hs, ex) env.domains;
      },
        eqs )

let assume_not_is_constr uf hs r dep env eqs =
  match embed r with
  | Adt.Constr { c_name; _ } when Util.Hstring.equal c_name hs ->
    raise (Ast.Ex.Inconsistent (dep, env.classes))
  | _ ->
    let _, env = assoc_and_remove_selector hs r env in
    let enum, ex =
      try MX.find r env.domains
      with Not_found -> (
          (* semantic values may be not inited with function add *)
          match values_of (Shostak.Combine.type_info r) with
          | Some s -> (s, Ast.Ex.empty)
          | None -> assert false)
    in
    if not (Util.Hstring.Set.mem hs enum) then (env, eqs)
    else
      let enum = Util.Hstring.Set.remove hs enum in
      let ex = Ast.Ex.union ex dep in
      if Util.Hstring.Set.is_empty enum then
        raise (Ast.Ex.Inconsistent (ex, env.classes))
      else
        let env = { env with domains = MX.add r (enum, ex) env.domains } in
        if Util.Hstring.Set.cardinal enum = 1 then
          let h' = Util.Hstring.Set.choose enum in
          let env, eqs = deduce_is_constr uf r h' eqs env ex in
          (env, eqs)
        else (env, eqs)

(* dot it modulo equivalence class ? or is it sufficient ? *)
let add_eq uf hss sm1 sm2 dep env eqs =
  match (sm1, sm2) with
  | Adt.Alien r, Adt.Constr { c_name = h; _ }
  | Adt.Constr { c_name = h; _ }, Adt.Alien r ->
    let enum, ex =
      try MX.find r env.domains with Not_found -> (hss, Ast.Ex.empty)
    in
    let ex = Ast.Ex.union ex dep in
    if not (Util.Hstring.Set.mem h enum) then
      raise (Ast.Ex.Inconsistent (ex, env.classes));
    let env, eqs = deduce_is_constr uf r h eqs env ex in
    ( {
      env with
      domains = MX.add r (Util.Hstring.Set.singleton h, ex) env.domains;
    },
      eqs )
  | Adt.Alien r1, Adt.Alien r2 ->
    let enum1, ex1 =
      try MX.find r1 env.domains with Not_found -> (hss, Ast.Ex.empty)
    in
    let enum2, ex2 =
      try MX.find r2 env.domains with Not_found -> (hss, Ast.Ex.empty)
    in
    let ex = Ast.Ex.union dep (Ast.Ex.union ex1 ex2) in
    let diff = Util.Hstring.Set.inter enum1 enum2 in
    if Util.Hstring.Set.is_empty diff then
      raise (Ast.Ex.Inconsistent (ex, env.classes));
    let domains = MX.add r1 (diff, ex) env.domains in
    let env = { env with domains = MX.add r2 (diff, ex) domains } in
    if Util.Hstring.Set.cardinal diff = 1 then
      let h' = Util.Hstring.Set.choose diff in
      let env, eqs = deduce_is_constr uf r1 h' eqs env ex in
      let env, eqs = deduce_is_constr uf r2 h' eqs env ex in
      (env, eqs)
    else (env, eqs)
  | _ -> (env, eqs)

let add_aux env r =
  Debug.add r;
  match embed r with
  | Adt.Alien r when not (MX.mem r env.domains) -> (
      match values_of (Shostak.Combine.type_info r) with
      | Some s ->
        { env with domains = MX.add r (s, Ast.Ex.empty) env.domains }
      | None -> env)
  | _ -> env

(* needed for models generation because fresh terms are not
   added with function add *)
let add_rec env r = List.fold_left add_aux env (Shostak.Combine.leaves r)

let update_cs_modulo_eq r1 r2 ex env eqs =
  (* PB Here: even if Subst, we are not sure that it was
     r1 |-> r2, because LR.mkv_eq may swap r1 and r2 *)
  try
    let old = MX.find r1 env.selectors in
    if get_debug_adt () then
      Util.Printer.print_dbg ~flushed:false ~module_name:"Adt_rel"
        ~function_name:"update_cs_modulo_eq"
        "update selectors modulo eq: %a |-> %a@ " Shostak.Combine.print r1 Shostak.Combine.print r2;
    let mhs =
      try MX.find r2 env.selectors with Not_found -> Util.Hstring.Map.empty
    in
    let eqs = ref eqs in
    let _new =
      Util.Hstring.Map.fold
        (fun hs l mhs ->
           if trivial_tester r2 hs then (
             if get_debug_adt () then
               Util.Printer.print_dbg ~flushed:false ~header:false
                 "make deduction because %a ? %a is trivial@ " Shostak.Combine.print r2
                 Util.Hstring.print hs;
             List.iter
               (fun (a, dep) ->
                  eqs := (Intf.Relation.LTerm a, dep, Ast.Th_util.Other) :: !eqs)
               l);
           let l =
             List.rev_map (fun (a, dep) -> (a, Ast.Ex.union ex dep)) l
           in
           Util.Hstring.Map.add hs l mhs)
        old mhs
    in
    if get_debug_adt () then Util.Printer.print_dbg ~header:false "";
    ({ env with selectors = MX.add r2 _new env.selectors }, !eqs)
  with Not_found -> (env, eqs)

let remove_redundancies la =
  let cache = ref SLR.empty in
  List.filter
    (fun (a, _, _, _) ->
       let a = LR.make a in
       if SLR.mem a !cache then false
       else (
         cache := SLR.add a !cache;
         true))
    la

let assume env uf la =
  if get_disable_adts () then (env, { Intf.Relation.assume = []; remove = [] })
  else
    let la = remove_redundancies la in
    (* should be done globally in CCX *)
    let env = count_splits env la in
    let classes = Uf.cl_extract uf in
    let env = { env with classes } in
    let aux bol r1 r2 dep env eqs = function
      | None -> (env, eqs)
      | Some hss ->
        if bol then add_eq uf hss (embed r1) (embed r2) dep env eqs
        else add_diseq uf hss (embed r1) (embed r2) dep env eqs
    in
    Debug.print_env "before assume" env;
    let env, eqs =
      List.fold_left
        (fun (env, eqs) (a, b, c, d) ->
           Debug.assume a;
           match (a, b, c, d) with
           | Ast.Xliteral.Eq (r1, r2), _, ex, orig ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             let env, eqs =
               if orig == Ast.Th_util.Subst then
                 update_cs_modulo_eq r1 r2 ex env eqs
               else (env, eqs)
             in
             aux true r1 r2 ex env eqs (values_of (Shostak.Combine.type_info r1))
           | Ast.Xliteral.Distinct (false, [ r1; r2 ]), _, ex, _ ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             aux false r1 r2 ex env eqs (values_of (Shostak.Combine.type_info r1))
           | ( Ast.Xliteral.Builtin (true, Ast.Sy.IsConstr hs, [ e ]),
               _,
               ex,
               _ ) ->
             assume_is_constr uf hs e ex env eqs
           | ( Ast.Xliteral.Builtin (false, Ast.Sy.IsConstr hs, [ e ]),
               _,
               ex,
               (_
                [@ocaml.ppwarning "XXX: assume not (. ? .): reasoning missing ?"])
             ) ->
             assume_not_is_constr uf hs e ex env eqs
           | _ -> (env, eqs))
        (env, []) la
    in
    let eqs = List.rev_append env.pending_deds eqs in
    let env = { env with pending_deds = [] } in
    Debug.print_env "after assume" env;
    let print fmt (a, _, _) =
      match a with
      | Intf.Relation.LTerm a -> fprintf fmt "%a" Ast.Expr.print a
      | _ -> assert false
    in
    if get_debug_adt () then
      Util.Printer.print_dbg ~module_name:"Adt_rel" ~function_name:"assume"
        "assume deduced %d equalities@ %a" (List.length eqs)
        (Util.Printer.pp_list_no_space print)
        eqs;
    (env, { Intf.Relation.assume = eqs; remove = [] })

(* ################################################################ *)

let two = Util.Numbers.Q.from_int 2

let case_split env _ ~for_model =
  if get_disable_adts () || not (get_enable_adts_cs ()) then []
  else (
    assert (not for_model);
    if get_debug_adt () then Debug.print_env "before cs" env;
    try
      let r, mhs = MX.choose env.selectors in
      if get_debug_adt () then
        Util.Printer.print_dbg ~flushed:false ~module_name:"Adt_rel"
          ~function_name:"case_split" "found r = %a@ " Shostak.Combine.print r;
      let hs, _ = Util.Hstring.Map.choose mhs in
      if get_debug_adt () then
        Util.Printer.print_dbg ~header:false "found hs = %a" Util.Hstring.print
          hs;
      (* cs on negative version would be better in general *)
      let cs = LR.mkv_builtin false (Ast.Sy.IsConstr hs) [ r ] in
      [ (cs, true, Ast.Th_util.CS (Ast.Th_util.Th_adt, two)) ]
    with Not_found ->
      Debug.no_case_split ();
      [])

let query env uf (ra, _, ex, _) =
  if get_disable_adts () then None
  else
    try
      match ra with
      | Ast.Xliteral.Builtin (true, Ast.Sy.IsConstr hs, [ e ]) ->
        ignore (assume_is_constr uf hs e ex env []);
        None
      | ((Ast.Xliteral.Builtin (false, Ast.Sy.IsConstr hs, [ e ]))
         [@ocaml.ppwarning "XXX: assume not (. ? .): reasoning missing ?"]) ->
        ignore (assume_not_is_constr uf hs e ex env []);
        None
      | _ -> None
    with Ast.Ex.Inconsistent (expl, classes) -> Some (expl, classes)

(* ################################################################ *)
