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
module Intf = Alt_ergo_lib_intf

open Format
open Util.Options
module X = Shostak.Combine
module Ac = Shostak.Ac

module LX = Ast.Xliteral.Make (struct
    type t = Shostak.Combine.r

    let compare = Shostak.Combine.hash_cmp

    include Shostak.Combine
  end)

module MapL = Util.Emap.Make (LX)

module MapX = struct
  include Shostak.MXH

  let find m x =
    Util.Steps.incr Util.Steps.Uf;
    find m x
end

module SetX = Shostak.SXH

module SetXX = Set.Make (struct
    type t = Shostak.Combine.r * Shostak.Combine.r

    let compare (r1, r1') (r2, r2') =
      let c = Shostak.Combine.hash_cmp r1 r2 in
      if c <> 0 then c else Shostak.Combine.hash_cmp r1' r2'
  end)

module SetAc = Set.Make (struct
    type t = Ac.t

    let compare = Ac.compare
  end)

module SetRL = Set.Make (struct
    type t = Ac.t * Shostak.Combine.r * Ast.Ex.t

    let compare (ac1, _, _) (ac2, _, _) = Ac.compare ac1 ac2
  end)

module RS = struct
  include Map.Make (struct
      type t = Ast.Sy.t

      let compare = Ast.Sy.compare
    end)

  let find k m = try find k m with Not_found -> SetRL.empty

  let add_rule (({ Intf.Solvable_theory.h; _ }, _, _) as rul) mp =
    add h (SetRL.add rul (find h mp)) mp

  let remove_rule (({ Intf.Solvable_theory.h; _ }, _, _) as rul) mp =
    add h (SetRL.remove rul (find h mp)) mp
end

type r = Shostak.Combine.r

type t = {
  (* term -> [t] *)
  make : r Ast.Expr.Map.t;
  (* representative table *)
  repr : (r * Ast.Ex.t) MapX.t;
  (* r -> class (of terms) *)
  classes : Ast.Expr.Set.t MapX.t;
  (*associates each value r with the set of semantical values whose
    representatives contains r *)
  gamma : SetX.t MapX.t;
  (* the disequations map *)
  neqs : Ast.Ex.t MapL.t MapX.t;
  (*AC rewrite system *)
  ac_rs : SetRL.t RS.t;
}

exception Found_term of Ast.Expr.t

(* hack: would need an inverse map from semantic values to terms *)
let terms_of_distinct env l =
  match LX.view l with
  | Ast.Xliteral.Distinct (false, rl) ->
    let lt =
      List.fold_left
        (fun acc r ->
           try
             let cl = MapX.find r env.classes in
             Ast.Expr.Set.iter
               (fun t ->
                  if Shostak.Combine.hash_equal (Ast.Expr.Map.find t env.make) r then
                    raise (Found_term t))
               cl;
             acc
           with
           | Found_term t -> t :: acc
           | Not_found -> acc)
        [] rl
    in
    let rec distrib = function
      | x :: r ->
        distrib r
        @ List.map
          (fun y -> Ast.Expr.Set.add x (Ast.Expr.Set.singleton y))
          r
      | [] -> []
    in
    distrib lt
  | _ -> assert false

let cl_extract env =
  if get_bottom_classes () then
    let classes = MapX.fold (fun _ cl acc -> cl :: acc) env.classes [] in
    MapX.fold
      (fun _ ml acc ->
         MapL.fold (fun l _ acc -> terms_of_distinct env l @ acc) ml acc)
      env.neqs classes
  else []

(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Util.Printer

  (* unused --
     let rs_print fmt = SetX.iter (fprintf fmt "\t%a@." Shostak.Combine.print)
  *)

  let lm_print fmt =
    MapL.iter (fun k dep -> fprintf fmt "%a %a" LX.print k Ast.Ex.print dep)

  let pmake fmt m =
    fprintf fmt "@[<v 2>map:@,";
    Ast.Expr.Map.iter
      (fun t r -> fprintf fmt "%a -> %a@," Ast.Expr.print t Shostak.Combine.print r)
      m;
    fprintf fmt "@]@,"

  let prepr fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Representatives map ----------------@,";
    MapX.iter
      (fun r (rr, dep) ->
         fprintf fmt "%a --> %a %a@," Shostak.Combine.print r Shostak.Combine.print rr Ast.Ex.print dep)
      m;
    fprintf fmt "@]@,"

  let prules fmt s =
    fprintf fmt
      "@[<v 2>------------- UF: AC rewrite rules ----------------------@,";
    RS.iter
      (fun _ srl ->
         SetRL.iter
           (fun (ac, d, dep) ->
              fprintf fmt "%a ~~> %a %a@," Shostak.Combine.print (Shostak.Combine.ac_embed ac) Shostak.Combine.print d
                Ast.Ex.print dep)
           srl)
      s;
    fprintf fmt "@]@,"

  let pclasses fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Class map --------------------------@,";
    MapX.iter
      (fun k s ->
         fprintf fmt "%a -> %a@," Shostak.Combine.print k Ast.Expr.print_list
           (Ast.Expr.Set.elements s))
      m;
    fprintf fmt "@]@,"

  (* unused --
     let pgamma fmt m =
     fprintf fmt "------------- UF: Gamma map --------------------------@.";
     MapX.iter (fun k s -> fprintf fmt "%a -> \n%a" Shostak.Combine.print k rs_print s) m
  *)

  let pneqs fmt m =
    fprintf fmt
      "@[<v 2>------------- UF: Disequations map--------------------@ ";
    MapX.iter (fun k s -> fprintf fmt "%a -> %a@ " Shostak.Combine.print k lm_print s) m;
    fprintf fmt "@]@ "

  let all env =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"all"
        "@[<v 0>-------------------------------------------------@ \
         %a%a%a%a%a-------------------------------------------------@]"
        pmake env.make prepr env.repr prules env.ac_rs pclasses env.classes
        pneqs env.neqs

  let lookup_not_found t env =
    print_err "Uf: %a Not_found in env" Ast.Expr.print t;
    all env

  let canon_of r rr =
    if get_rewriting () && get_verbose () then
      print_dbg "canon %a = %a" Shostak.Combine.print r Shostak.Combine.print rr

  let init_leaf p =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"init_leaf" "init leaf : %a"
        Shostak.Combine.print p

  let critical_pair rx ry =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"critical_pair"
        "critical pair : %a = %a@." Shostak.Combine.print rx Shostak.Combine.print ry

  let collapse_mult g2 d2 =
    if get_debug_ac () then
      print_dbg ~module_name:"Uf" ~function_name:"collapse_mult"
        "collapse *: %a = %a" Shostak.Combine.print g2 Shostak.Combine.print d2

  let collapse g2 d2 =
    if get_debug_ac () then
      print_dbg ~module_name:"Uf" ~function_name:"collapse" "collapse: %a = %a"
        Shostak.Combine.print g2 Shostak.Combine.print d2

  let compose p v g d =
    if get_debug_ac () then
      print_dbg ~module_name:"Uf" ~function_name:"compose"
        "compose : %a -> %a on %a and %a" Shostak.Combine.print p Shostak.Combine.print v Ac.print g Shostak.Combine.print
        d

  let x_solve rr1 rr2 dep =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"x_solve" "x-solve: %a = %a %a"
        Shostak.Combine.print rr1 Shostak.Combine.print rr2 Ast.Ex.print dep

  let ac_solve p v dep =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"ac_solve"
        "ac-solve: %a |-> %a %a" Shostak.Combine.print p Shostak.Combine.print v Ast.Ex.print dep

  let ac_x r1 r2 =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"ac_x"
        "ac(x): delta (%a) = delta (%a)" Shostak.Combine.print r1 Shostak.Combine.print r2

  let distinct d =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"distinct" "distinct %a"
        LX.print d

  let are_distinct t1 t2 =
    if get_debug_uf () then
      print_dbg ~module_name:"Uf" ~function_name:"are_distinct"
        "are_distinct %a %a" Ast.Expr.print t1 Ast.Expr.print t2

  let check_inv_repr_normalized =
    let trace orig =
      print_err
        "[uf.%s] invariant broken when calling check_inv_repr_normalized" orig
    in
    fun orig repr ->
      MapX.iter
        (fun _ (rr, _) ->
           List.iter
             (fun x ->
                try
                  if not (Shostak.Combine.hash_equal x (fst (MapX.find x repr))) then
                    let () = trace orig in
                    assert false
                with Not_found ->
                  (* all leaves that are in normal form should be in repr ?
                     not AC leaves, which can be created dynamically,
                     not for other, that can be introduced by make and solve*)
                  ())
             (Shostak.Combine.leaves rr))
        repr

  let check_invariants orig env =
    if Util.Options.get_enable_assertions () then
      check_inv_repr_normalized orig env.repr
end
(*BISECT-IGNORE-END*)

module Env = struct
  let mem env t = Ast.Expr.Map.mem t env.make

  let lookup_by_t t env =
    Util.Options.exec_thread_yield ();
    try MapX.find (Ast.Expr.Map.find t env.make) env.repr
    with Not_found ->
      Debug.lookup_not_found t env;
      assert false
  (*Shostak.Combine.make t, Ex.empty*)
  (* XXXX *)

  let lookup_by_t___without_failure t env =
    try MapX.find (Ast.Expr.Map.find t env.make) env.repr
    with Not_found -> (fst (Shostak.Combine.make t), Ast.Ex.empty)

  let lookup_by_r r env =
    Util.Options.exec_thread_yield ();
    try MapX.find r env.repr with Not_found -> (r, Ast.Ex.empty)

  let disjoint_union l_1 l_2 =
    let rec di_un (l1, c, l2) (l_1, l_2) =
      Util.Options.exec_thread_yield ();
      match (l_1, l_2) with
      | [], [] -> (l1, c, l2)
      | l, [] -> di_un (l @ l1, c, l2) ([], [])
      | [], l -> di_un (l1, c, l @ l2) ([], [])
      | (a, m) :: r, (b, n) :: s ->
        let cmp = Shostak.Combine.str_cmp a b in
        if cmp = 0 then
          if m = n then di_un (l1, (a, m) :: c, l2) (r, s)
          else if m > n then di_un ((a, m - n) :: l1, (a, n) :: c, l2) (r, s)
          else di_un (l1, (b, n) :: c, (b, n - m) :: l2) (r, s)
        else if cmp > 0 then di_un ((a, m) :: l1, c, l2) (r, (b, n) :: s)
        else di_un (l1, c, (b, n) :: l2) ((a, m) :: r, s)
    in
    di_un ([], [], []) (l_1, l_2)

  (* Debut : Code pour la mise en forme normale modulo env *)
  exception List_minus_exn

  let list_minus l_1 l_2 =
    let rec di_un l1 l_1 l_2 =
      match (l_1, l_2) with
      | [], [] -> l1
      | l, [] -> l @ l1
      | [], _ -> raise List_minus_exn
      | (a, m) :: r, (b, n) :: s ->
        let cmp = Shostak.Combine.str_cmp a b in
        if cmp = 0 then
          if m = n then di_un l1 r s
          else if m > n then di_un ((a, m - n) :: l1) r s
          else raise List_minus_exn
        else if cmp > 0 then di_un ((a, m) :: l1) r ((b, n) :: s)
        else raise List_minus_exn
    in
    di_un [] l_1 l_2

  let apply_rs r rls =
    let fp = ref true in
    let r = ref r in
    let ex = ref Ast.Ex.empty in
    let rec apply_rule ((p, v, dep) as rul) =
      let c = Ac.compare !r p in
      if c = 0 then (
        r := { !r with l = [ (v, 1) ] };
        ex := Ast.Ex.union !ex dep)
      else if c < 0 then raise Exit
      else
        try
          r := { !r with l = Ac.add !r.h (v, 1) (list_minus !r.l p.l) };
          ex := Ast.Ex.union !ex dep;
          fp := false;
          apply_rule rul
        with List_minus_exn -> ()
    in
    let rec fixpoint () =
      Util.Options.exec_thread_yield ();
      (try SetRL.iter apply_rule rls with Exit -> ());
      if !fp then (!r, !ex)
      else (
        fp := true;
        fixpoint ())
    in
    fixpoint ()

  let filter_leaves r =
    List.fold_left
      (fun (p, q) r ->
         match Shostak.Combine.ac_extract r with
         | None -> (SetX.add r p, q)
         | Some ac -> (p, SetAc.add ac q))
      (SetX.empty, SetAc.empty) (Shostak.Combine.leaves r)

  let canon_empty st env =
    SetX.fold
      (fun p ((z, ex) as acc) ->
         let q, ex_q = lookup_by_r p env in
         if Shostak.Combine.hash_equal p q then acc else ((p, q) :: z, Ast.Ex.union ex_q ex))
      st ([], Ast.Ex.empty)

  let canon_ac st env =
    SetAc.fold
      (fun ac (z, ex) ->
         let rac, ex_ac = apply_rs ac (RS.find ac.h env.ac_rs) in
         if Ac.compare ac rac = 0 then (z, ex)
         else ((Shostak.Combine.color ac, Shostak.Combine.color rac) :: z, Ast.Ex.union ex ex_ac))
      st ([], Ast.Ex.empty)

  let canon_aux rx = List.fold_left (fun r (p, v) -> Shostak.Combine.subst p v r) rx

  let rec canon env r ex_r =
    let se, sac = filter_leaves r in
    let subst, ex_subst = canon_empty se env in
    let subst_ac, ex_ac = canon_ac sac env in
    (* explications? *)
    let r2 = canon_aux (canon_aux r subst_ac) subst in
    let ex_r2 = Ast.Ex.union (Ast.Ex.union ex_r ex_subst) ex_ac in
    if Shostak.Combine.hash_equal r r2 then (r2, ex_r2) else canon env r2 ex_r2

  let normal_form env r =
    let rr, ex = canon env r Ast.Ex.empty in
    Debug.canon_of r rr;
    (rr, ex)

  (* Fin : Code pour la mise en forme normale modulo env *)

  let find_or_normal_form env r =
    Util.Options.exec_thread_yield ();
    try MapX.find r env.repr with Not_found -> normal_form env r

  let lookup_for_neqs env r =
    Util.Options.exec_thread_yield ();
    try MapX.find r env.neqs with Not_found -> MapL.empty

  let add_to_classes t r classes =
    MapX.add r
      (Ast.Expr.Set.add t
         (try MapX.find r classes with Not_found -> Ast.Expr.Set.empty))
      classes

  let update_classes c nc classes =
    let s1 =
      try MapX.find c classes with Not_found -> Ast.Expr.Set.empty
    in
    let s2 =
      try MapX.find nc classes with Not_found -> Ast.Expr.Set.empty
    in
    MapX.add nc (Ast.Expr.Set.union s1 s2) (MapX.remove c classes)

  let add_to_gamma r c gamma =
    Util.Options.exec_thread_yield ();
    List.fold_left
      (fun gamma x ->
         let s = try MapX.find x gamma with Not_found -> SetX.empty in
         MapX.add x (SetX.add r s) gamma)
      gamma (Shostak.Combine.leaves c)

  let explain_repr_of_distinct x repr_x dep lit env =
    match LX.view lit with
    | Ast.Xliteral.Distinct (false, ([ _; _ ] as args)) ->
      List.fold_left
        (fun dep r -> Ast.Ex.union dep (snd (find_or_normal_form env r)))
        dep args
    | Ast.Xliteral.Pred (r, _) ->
      Ast.Ex.union dep (snd (find_or_normal_form env r))
    | Ast.Xliteral.Distinct (false, l) ->
      List.fold_left
        (fun d r ->
           let z, ex = find_or_normal_form env r in
           if Shostak.Combine.hash_equal z x || Shostak.Combine.hash_equal z repr_x then Ast.Ex.union d ex else d)
        dep l
    | _ -> assert false

  (* r1 = r2 => neqs(r1) \uplus neqs(r2) *)
  let update_neqs x repr_x dep env =
    let merge_disjoint_maps l1 ex1 mapl =
      try
        let ex2 = MapL.find l1 mapl in
        Util.Options.tool_req 3 "TR-CCX-Congruence-Conflict";
        let ex = Ast.Ex.union (Ast.Ex.union ex1 ex2) dep in
        let ex = explain_repr_of_distinct x repr_x ex l1 env in
        raise (Ast.Ex.Inconsistent (ex, cl_extract env))
      with Not_found ->
        (* with the use of explain_repr_of_distinct above, I
           don't need to propagate dep to ex1 here *)
        MapL.add l1 ex1 mapl
    in
    let nq_r1 = lookup_for_neqs env x in
    let nq_r2 = lookup_for_neqs env repr_x in
    let small, big =
      if MapL.height nq_r1 < MapL.height nq_r2 then (nq_r1, nq_r2)
      else (nq_r2, nq_r1)
    in
    let mapl = MapL.fold merge_disjoint_maps small big in
    (* remove x from the map to avoid eventual bugs if call this
       function again with x == repr_x *)
    MapX.add repr_x mapl (MapX.remove x env.neqs)

  let init_leaf env p =
    Debug.init_leaf p;
    let in_repr = MapX.mem p env.repr in
    let rp, ex_rp =
      if in_repr then MapX.find p env.repr else normal_form env p
    in
    let mk_env = env.make in
    let make =
      match Shostak.Combine.term_extract p with
      | Some t, true when not (Ast.Expr.Map.mem t mk_env) ->
        Ast.Expr.Map.add t p mk_env
      | _ -> mk_env
    in
    let env =
      {
        env with
        make;
        repr = (if in_repr then env.repr else MapX.add p (rp, ex_rp) env.repr);
        classes =
          (if MapX.mem p env.classes then env.classes
           else update_classes p rp env.classes);
        gamma = (if in_repr then env.gamma else add_to_gamma p rp env.gamma);
        neqs =
          (if MapX.mem p env.neqs then env.neqs
           else update_neqs p rp Ast.Ex.empty env);
      }
    in
    Debug.check_invariants "init_leaf" env;
    env

  let init_leaves env v =
    let env = List.fold_left init_leaf env (Shostak.Combine.leaves v) in
    init_leaf env v

  let init_new_ac_leaves env mkr =
    List.fold_left
      (fun env x ->
         match X.ac_extract x with
         | None -> env
         | Some _ -> if MapX.mem x env.repr then env else init_leaves env x)
      env (Shostak.Combine.leaves mkr)

  let init_term env t =
    let mkr, ctx = Shostak.Combine.make t in
    let rp, ex = normal_form env mkr in
    let env =
      {
        env with
        make = Ast.Expr.Map.add t mkr env.make;
        repr = MapX.add mkr (rp, ex) env.repr;
        classes = add_to_classes t rp env.classes;
        gamma = add_to_gamma mkr rp env.gamma;
        neqs =
          (if MapX.mem rp env.neqs then env.neqs (* pourquoi ce test *)
           else MapX.add rp MapL.empty env.neqs);
      }
    in
    (init_new_ac_leaves env mkr, ctx)

  let head_cp eqs env pac ({ Intf.Solvable_theory.h; _ } as ac) v dep =
    try
      (*if RS.mem h env.ac_rs then*)
      SetRL.iter
        (fun (g, d, dep_rl) ->
           if Shostak.Combine.hash_equal pac (Shostak.Combine.ac_embed g) && Shostak.Combine.hash_equal v d then ()
           else
             match disjoint_union ac.l g.l with
             | _, [], _ -> ()
             | l1, _cm, l2 ->
               let rx = Shostak.Combine.color { ac with l = Ac.add h (d, 1) l1 } in
               let ry = Shostak.Combine.color { g with l = Ac.add h (v, 1) l2 } in
               Debug.critical_pair rx ry;
               if not (Shostak.Combine.hash_equal rx ry) then
                 Queue.push (rx, ry, Ast.Ex.union dep dep_rl) eqs)
        (RS.find h env.ac_rs)
    with Not_found -> assert false

  let comp_collapse eqs env (p, v, dep) =
    RS.fold
      (fun _ rls env ->
         SetRL.fold
           (fun ((g, d, dep_rl) as rul) env ->
              Util.Options.exec_thread_yield ();
              Util.Steps.incr Util.Steps.Ac;
              let env = { env with ac_rs = RS.remove_rule rul env.ac_rs } in
              let gx = Shostak.Combine.color g in
              let g2, ex_g2 = normal_form env (Ac.subst p v g) in
              let d2, ex_d2 = normal_form env (Shostak.Combine.subst p v d) in
              if Shostak.Combine.str_cmp g2 d2 <= 0 then (
                Debug.collapse_mult g2 d2;
                let ex =
                  Ast.Ex.union
                    (Ast.Ex.union ex_g2 ex_d2)
                    (Ast.Ex.union dep_rl dep)
                in
                Queue.push (g2, d2, ex) eqs;
                env)
              else if Shostak.Combine.hash_equal g2 gx then (
                (* compose *)
                Debug.compose p v g d;
                let ex = Ast.Ex.union ex_d2 (Ast.Ex.union dep_rl dep) in
                { env with ac_rs = RS.add_rule (g, d2, ex) env.ac_rs })
              else (
                (* collapse *)
                Debug.collapse g2 d2;
                let ex =
                  Ast.Ex.union
                    (Ast.Ex.union ex_g2 ex_d2)
                    (Ast.Ex.union dep_rl dep)
                in
                Queue.push (g2, d2, ex) eqs;
                env))
           rls env)
      env.ac_rs env

  (* TODO explications: ajout de dep dans ac_rs *)
  let apply_sigma_ac eqs env ((p, v, dep) as sigma) =
    match Shostak.Combine.ac_extract p with
    | None -> comp_collapse eqs env sigma
    | Some r ->
      let env = { env with ac_rs = RS.add_rule (r, v, dep) env.ac_rs } in
      let env = comp_collapse eqs env sigma in
      head_cp eqs env p r v dep;
      env

  let update_aux dep set env =
    SetXX.fold
      (fun (rr, nrr) env ->
         {
           env with
           neqs = update_neqs rr nrr dep env;
           classes = update_classes rr nrr env.classes;
         })
      set env

  (* Patch modudo AC for CC: if p is a leaf different from r and r is AC
     and reduced by p, then r --> nrr should be added as a PIVOT, not just
     as TOUCHED by p |-> ... This is required for a correct update of USE *)
  let update_global_tch global_tch p r nrr ex =
    if Shostak.Combine.hash_equal p r then global_tch
    else
      match Shostak.Combine.ac_extract r with
      | None -> global_tch
      | Some _ -> (r, [ (r, nrr, ex) ], nrr) :: global_tch

  let apply_sigma_uf env (p, v, dep) global_tch =
    assert (MapX.mem p env.gamma);
    let use_p = MapX.find p env.gamma in
    try
      let env, touched_p, global_tch, neqs_to_up =
        SetX.fold
          (fun r ((env, touched_p, global_tch, neqs_to_up) as acc) ->
             Util.Options.exec_thread_yield ();
             let rr, ex = MapX.find r env.repr in
             let nrr = Shostak.Combine.subst p v rr in
             if Shostak.Combine.hash_equal rr nrr then acc
             else
               let ex = Ast.Ex.union ex dep in
               let env =
                 {
                   env with
                   repr = MapX.add r (nrr, ex) env.repr;
                   gamma = add_to_gamma r nrr env.gamma;
                 }
               in
               ( env,
                 (r, nrr, ex) :: touched_p,
                 update_global_tch global_tch p r nrr ex,
                 SetXX.add (rr, nrr) neqs_to_up ))
          use_p
          (env, [], global_tch, SetXX.empty)
      in
      (* Correction : Do not update neqs twice for the same r *)
      (update_aux dep neqs_to_up env, touched_p, global_tch)
    with Not_found -> assert false

  let up_uf_rs dep env tch =
    if RS.is_empty env.ac_rs then (env, tch)
    else
      let env, tch, neqs_to_up =
        MapX.fold
          (fun r (rr, ex) ((env, tch, neqs_to_up) as acc) ->
             Util.Options.exec_thread_yield ();
             let nrr, ex_nrr = normal_form env rr in
             if Shostak.Combine.hash_equal nrr rr then acc
             else
               let ex = Ast.Ex.union ex ex_nrr in
               let env =
                 {
                   env with
                   repr = MapX.add r (nrr, ex) env.repr;
                   gamma = add_to_gamma r nrr env.gamma;
                 }
               in
               let tch =
                 if Shostak.Combine.is_a_leaf r then (r, [ (r, nrr, ex) ], nrr) :: tch else tch
               in
               (env, tch, SetXX.add (rr, nrr) neqs_to_up))
          env.repr (env, tch, SetXX.empty)
      in
      (* Correction : Do not update neqs twice for the same r *)
      (update_aux dep neqs_to_up env, tch)

  let apply_sigma eqs env tch ((p, v, dep) as sigma) =
    let env = init_leaves env p in
    let env = init_leaves env v in
    let env = apply_sigma_ac eqs env sigma in
    let env, touched_sigma, tch = apply_sigma_uf env sigma tch in
    up_uf_rs dep env ((p, touched_sigma, v) :: tch)
end

let add env t =
  Util.Options.tool_req 3 "TR-UFX-Add";
  if Ast.Expr.Map.mem t env.make then (env, [])
  else
    let env, l = Env.init_term env t in
    Debug.check_invariants "add" env;
    (env, l)

let ac_solve eqs dep (env, tch) (p, v) =
  Debug.ac_solve p v dep;
  let rv, ex_rv = Env.find_or_normal_form env v in
  if not (Shostak.Combine.hash_equal v rv) then (
    (* v is not in normal form ==> replay *)
    Queue.push (p, rv, Ast.Ex.union dep ex_rv) eqs;
    (env, tch))
  else
    let rp, ex_rp = Env.find_or_normal_form env p in
    if not (Shostak.Combine.hash_equal p rp) then (
      (* p is not in normal form ==> replay *)
      Queue.push (rp, v, Ast.Ex.union dep ex_rp) eqs;
      (env, tch))
    else
      (* both p and v are in normal form ==> apply subst p |-> v *)
      Env.apply_sigma eqs env tch (p, v, dep)

let x_solve env r1 r2 dep =
  let rr1, ex_r1 = Env.find_or_normal_form env r1 in
  let rr2, ex_r2 = Env.find_or_normal_form env r2 in
  let dep = Ast.Ex.union dep (Ast.Ex.union ex_r1 ex_r2) in
  Debug.x_solve rr1 rr2 dep;
  if Shostak.Combine.hash_equal rr1 rr2 then (
    Util.Options.tool_req 3 "TR-CCX-Remove";
    ([], dep (* Remove rule *)))
  else (
    ignore (Env.update_neqs rr1 rr2 dep env);
    try (Shostak.Combine.solve rr1 rr2, dep)
    with Util.Util.Unsolvable ->
      Util.Options.tool_req 3 "TR-CCX-Congruence-Conflict";
      raise (Ast.Ex.Inconsistent (dep, cl_extract env)))

let rec ac_x eqs env tch =
  if Queue.is_empty eqs then (env, tch)
  else
    let r1, r2, dep = Queue.pop eqs in
    Debug.ac_x r1 r2;
    let sbs, dep = x_solve env r1 r2 dep in
    let env, tch = List.fold_left (ac_solve eqs dep) (env, tch) sbs in
    if get_debug_uf () then Debug.all env;
    ac_x eqs env tch

let union env r1 r2 dep =
  Util.Options.tool_req 3 "TR-UFX-Union";
  let equations = Queue.create () in
  Queue.push (r1, r2, dep) equations;
  let env, res = ac_x equations env [] in
  Debug.check_invariants "union" env;
  (env, res)

let union env r1 r2 dep =
  if Util.Options.get_timers () then (
    try
      Util.Timers.exec_timer_start Util.Timers.M_UF Util.Timers.F_union;
      let res = union env r1 r2 dep in
      Util.Timers.exec_timer_pause Util.Timers.M_UF Util.Timers.F_union;
      res
    with e ->
      Util.Timers.exec_timer_pause Util.Timers.M_UF Util.Timers.F_union;
      raise e)
  else union env r1 r2 dep

let rec distinct env rl dep =
  Debug.all env;
  let d = LX.mk_distinct false rl in
  Debug.distinct d;
  let env, _, newds =
    List.fold_left
      (fun (env, mapr, newds) r ->
         Util.Options.exec_thread_yield ();
         let rr, ex = Env.find_or_normal_form env r in
         try
           let exr = MapX.find rr mapr in
           Util.Options.tool_req 3 "TR-CCX-Distinct-Conflict";
           raise
             (Ast.Ex.Inconsistent (Ast.Ex.union ex exr, cl_extract env))
         with Not_found ->
           let uex = Ast.Ex.union ex dep in
           let mdis = try MapX.find rr env.neqs with Not_found -> MapL.empty in
           let mdis =
             try MapL.add d (Ast.Ex.merge uex (MapL.find d mdis)) mdis
             with Not_found -> MapL.add d uex mdis
           in
           let env = Env.init_leaf env rr in
           let env = { env with neqs = MapX.add rr mdis env.neqs } in
           (env, MapX.add rr uex mapr, (rr, ex, mapr) :: newds))
      (env, MapX.empty, []) rl
  in
  List.fold_left
    (fun env (r1, ex1, mapr) ->
       MapX.fold
         (fun r2 ex2 env ->
            let ex = Ast.Ex.union ex1 (Ast.Ex.union ex2 dep) in
            try
              match Shostak.Combine.solve r1 r2 with
              | [ (a, b) ] ->
                if
                  (Shostak.Combine.hash_equal a r1 && Shostak.Combine.hash_equal b r2)
                  || (Shostak.Combine.hash_equal a r2 && Shostak.Combine.hash_equal b r1)
                then env
                else distinct env [ a; b ] ex
              | [] ->
                Util.Options.tool_req 3 "TR-CCX-Distinct-Conflict";
                raise (Ast.Ex.Inconsistent (ex, cl_extract env))
              | _ -> env
            with Util.Util.Unsolvable -> env)
         mapr env)
    env newds

let distinct env rl dep =
  let env = distinct env rl dep in
  Debug.check_invariants "distinct" env;
  env

let are_equal env t1 t2 ~added_terms =
  if Ast.Expr.equal t1 t2 then Some (Ast.Ex.empty, cl_extract env)
  else
    let lookup =
      if added_terms then Env.lookup_by_t else Env.lookup_by_t___without_failure
    in
    let r1, ex_r1 = lookup t1 env in
    let r2, ex_r2 = lookup t2 env in
    if Shostak.Combine.hash_equal r1 r2 then Some (Ast.Ex.union ex_r1 ex_r2, cl_extract env)
    else None

let are_distinct env t1 t2 =
  Debug.are_distinct t1 t2;
  let r1, ex_r1 = Env.lookup_by_t t1 env in
  let r2, ex_r2 = Env.lookup_by_t t2 env in
  try
    ignore (union env r1 r2 (Ast.Ex.union ex_r1 ex_r2));
    None
  with Ast.Ex.Inconsistent (ex, classes) -> Some (ex, classes)

let already_distinct env lr =
  let d = LX.mk_distinct false lr in
  try
    List.iter
      (fun r ->
         let mdis = MapX.find r env.neqs in
         ignore (MapL.find d mdis))
      lr;
    true
  with Not_found -> false

let mapt_choose m =
  let r = ref None in
  (try
     Ast.Expr.Map.iter
       (fun x rx ->
          r := Some (x, rx);
          raise Exit)
       m
   with Exit -> ());
  match !r with Some b -> b | _ -> raise Not_found

let model env =
  let eqs =
    MapX.fold
      (fun r cl acc ->
         let l, to_rel =
           List.fold_left
             (fun (l, to_rel) t ->
                let rt = Ast.Expr.Map.find t env.make in
                if get_complete_model () || Ast.Expr.is_in_model t then
                  if Shostak.Combine.hash_equal rt r then (l, (t, rt) :: to_rel)
                  else (t :: l, (t, rt) :: to_rel)
                else (l, to_rel))
             ([], [])
             (Ast.Expr.Set.elements cl)
         in
         (r, l, to_rel) :: acc)
      env.classes []
  in
  let rec extract_neqs acc makes =
    try
      let x, rx = mapt_choose makes in
      let makes = Ast.Expr.Map.remove x makes in
      let acc =
        if get_complete_model () || Ast.Expr.is_in_model x then
          Ast.Expr.Map.fold
            (fun y ry acc ->
               if
                 (get_complete_model () || Ast.Expr.is_in_model y)
                 && (already_distinct env [ rx; ry ]
                     || already_distinct env [ ry; rx ])
               then [ y; x ] :: acc
               else acc)
            makes acc
        else acc
      in
      extract_neqs acc makes
    with Not_found -> acc
  in
  let neqs = extract_neqs [] env.make in
  (eqs, neqs)

let find env t =
  Util.Options.tool_req 3 "TR-UFX-Find";
  Env.lookup_by_t t env

let find_r =
  Util.Options.tool_req 3 "TR-UFX-Find";
  Env.find_or_normal_form

let print = Debug.all
let mem = Env.mem

let class_of env t =
  try
    let rt, _ = MapX.find (Ast.Expr.Map.find t env.make) env.repr in
    MapX.find rt env.classes
  with Not_found -> Ast.Expr.Set.singleton t

let rclass_of env r =
  try MapX.find r env.classes with Not_found -> Ast.Expr.Set.empty

let term_repr uf t =
  let st = class_of uf t in
  try Ast.Expr.Set.min_elt st with Not_found -> t

let class_of env t = Ast.Expr.Set.elements (class_of env t)

let empty () =
  let env =
    {
      make = Ast.Expr.Map.empty;
      repr = MapX.empty;
      classes = MapX.empty;
      gamma = MapX.empty;
      neqs = MapX.empty;
      ac_rs = RS.empty;
    }
  in
  let env, _ = add env Ast.Expr.vrai in
  let env, _ = add env Ast.Expr.faux in
  distinct env [ Shostak.Combine.top (); Shostak.Combine.bot () ] Ast.Ex.empty

let make uf t = Ast.Expr.Map.find t uf.make

(*** add wrappers to profile exported functions ***)

let add env t =
  if Util.Options.get_timers () then (
    try
      Util.Timers.exec_timer_start Util.Timers.M_UF Util.Timers.F_add_terms;
      let res = add env t in
      Util.Timers.exec_timer_pause Util.Timers.M_UF Util.Timers.F_add_terms;
      res
    with e ->
      Util.Timers.exec_timer_pause Util.Timers.M_UF Util.Timers.F_add_terms;
      raise e)
  else add env t

let is_normalized env r =
  List.for_all
    (fun x ->
       try Shostak.Combine.hash_equal x (fst (MapX.find x env.repr)) with Not_found -> true)
    (Shostak.Combine.leaves r)

let distinct_from_constants rep env =
  let neqs = try MapX.find rep env.neqs with Not_found -> assert false in
  MapL.fold
    (fun lit _ acc ->
       let contains_rep = ref false in
       let lit_vals =
         match LX.view lit with Ast.Xliteral.Distinct (_, l) -> l | _ -> []
       in
       let acc2 =
         List.fold_left
           (fun acc r ->
              if Shostak.Combine.hash_equal rep r then contains_rep := true;
              match Shostak.Combine.leaves r with [] -> r :: acc | _ -> acc)
           acc lit_vals
       in
       if !contains_rep then acc2 else acc)
    neqs []

let assign_next env =
  let acc = ref None in
  let res, env =
    try
      MapX.iter
        (fun r eclass ->
           let eclass =
             try
               Ast.Expr.Set.fold
                 (fun t z -> (t, Ast.Expr.Map.find t env.make) :: z)
                 eclass []
             with Not_found -> assert false
           in
           let opt = Shostak.Combine.assign_value r (distinct_from_constants r env) eclass in
           match opt with
           | None -> ()
           | Some (s, is_cs) ->
             acc := Some (s, r, is_cs);
             raise Exit)
        env.classes;
      ([], env (* no cs *))
    with Exit -> (
        match !acc with
        | None -> assert false
        | Some (s, rep, is_cs) ->
          if get_debug_interpretation () then
            Util.Printer.print_dbg ~module_name:"Uf"
              ~function_name:"assign_next" "TRY assign-next %a = %a" Shostak.Combine.print rep
              Ast.Expr.print s;
          (*
          !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
          modify this to be able to returns CS on terms. This way,
          we will not modify env in this function
          !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        *)
          let env, _ = add env s in
          (* important for termination *)
          let eq = LX.view (LX.mk_eq rep (make env s)) in
          ([ (eq, is_cs, Ast.Th_util.CS (Ast.Th_util.Th_UF, Util.Numbers.Q.one)) ], env))
  in
  Debug.check_invariants "assign_next" env;
  (res, env)

module Profile = struct
  module P = Map.Make (struct
      type t = Ast.Sy.t * Ast.Ty.t list * Ast.Ty.t

      let ( ||| ) c1 c2 = if c1 <> 0 then c1 else c2

      let compare (a1, b1, c1) (a2, b2, c2) =
        let l1_l2 = List.length b1 - List.length b2 in
        let c = l1_l2 ||| Ast.Ty.compare c1 c2 ||| Ast.Sy.compare a1 a2 in
        if c <> 0 then c
        else
          let c = ref 0 in
          try
            List.iter2
              (fun ty1 ty2 ->
                 let d = Ast.Ty.compare ty1 ty2 in
                 if d <> 0 then (
                   c := d;
                   raise Exit))
              b1 b2;
            0
          with
          | Exit ->
            assert (!c <> 0);
            !c
          | Invalid_argument _ -> assert false
    end)

  module V = Set.Make (struct
      type t = (Ast.Expr.t * (Shostak.Combine.r * string)) list * (Shostak.Combine.r * string)

      let compare (l1, (v1, _)) (l2, (v2, _)) =
        let c = Shostak.Combine.hash_cmp v1 v2 in
        if c <> 0 then c
        else
          let c = ref 0 in
          try
            List.iter2
              (fun (_, (x, _)) (_, (y, _)) ->
                 let d = Shostak.Combine.hash_cmp x y in
                 if d <> 0 then (
                   c := d;
                   raise Exit))
              l1 l2;
            !c
          with
          | Exit -> !c
          | Invalid_argument _ -> List.length l1 - List.length l2
    end)

  let add p v mp =
    let prof_p = try P.find p mp with Not_found -> V.empty in
    if V.mem v prof_p then mp else P.add p (V.add v prof_p) mp

  let iter = P.iter
  let empty = P.empty
  let is_empty = P.is_empty
end

let assert_has_depth_one (e, _) =
  match Shostak.Combine.term_extract e with
  | Some t, true -> assert (Ast.Expr.const_term t)
  | _ -> ()

module SMT2LikeModelOutput = struct
  let x_print fmt (_, ppr) = fprintf fmt "%s" ppr

  let print_args fmt l =
    match l with
    | [] -> assert false
    | [ (_, e) ] -> fprintf fmt "%a" x_print e
    | (_, e) :: l ->
      fprintf fmt "%a" x_print e;
      List.iter (fun (_, e) -> fprintf fmt " %a" x_print e) l

  let print_symb ty fmt f =
    match (f, ty) with
    | Ast.Sy.Op Ast.Sy.Record, Ast.Ty.Trecord { Ast.Ty.name; _ }
      ->
      fprintf fmt "%a__%s" Ast.Sy.print f (Util.Hstring.view name)
    | _ -> Ast.Sy.print fmt f

  let output_constants_model cprofs =
    (*printf "; constants:@.";*)
    Profile.iter
      (fun (f, _xs_ty, ty) st ->
         match Profile.V.elements st with
         | [ ([], rep) ] ->
           (*printf "  (%a %a)  ; %a@."
             (print_symb ty) f x_print rep Ast.Ty.print ty*)
           Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "(%a %a)@ "
             (print_symb ty) f x_print rep
         | _ -> assert false)
      cprofs

  let output_functions_model fprofs =
    if not (Profile.is_empty fprofs) then (
      Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "@[<v 2>@ ";
      (*printf "@.; functions:@.";*)
      Profile.iter
        (fun (f, _xs_ty, ty) st ->
           (*printf "  ; fun %a : %a -> %a@."
             (print_symb ty) f Ast.Ty.print_list xs_ty Ast.Ty.print ty;*)
           Profile.V.iter
             (fun (xs, rep) ->
                Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ())
                  "((%a %a) %a)@ " (print_symb ty) f print_args xs x_print rep;
                List.iter (fun (_, x) -> assert_has_depth_one x) xs)
             st;
           Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "@]@ ")
        fprofs;
      Util.Printer.print_fmt (get_fmt_mdl ()) "@]")

  let output_arrays_model arrays =
    if not (Profile.is_empty arrays) then (
      Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "@[<v 2>@ ";
      (*printf "; arrays:@.";*)
      Profile.iter
        (fun (f, xs_ty, ty) st ->
           match xs_ty with
           | [ _ ] ->
             (*printf "  ; array %a : %a -> %a@."
               (print_symb ty) f Ast.Ty.print tyi Ast.Ty.print ty;*)
             Profile.V.iter
               (fun (xs, rep) ->
                  Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ())
                    "((%a %a) %a)@ " (print_symb ty) f print_args xs x_print rep;
                  List.iter (fun (_, x) -> assert_has_depth_one x) xs)
               st;
             Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "@]@ "
           | _ -> assert false)
        arrays;
      Util.Printer.print_fmt (get_fmt_mdl ()) "@]")
end
(* of module SMT2LikeModelOutput *)

let is_a_good_model_value (x, _) =
  match Shostak.Combine.leaves x with [] -> true | [ y ] -> Shostak.Combine.hash_equal x y | _ -> false

let model_repr_of_term t env mrepr =
  try (Ast.Expr.Map.find t mrepr, mrepr)
  with Not_found ->
    let mk =
      try Ast.Expr.Map.find t env.make with Not_found -> assert false
    in
    let rep, _ = try MapX.find mk env.repr with Not_found -> assert false in
    let cls =
      try Ast.Expr.Set.elements (MapX.find rep env.classes)
      with Not_found -> assert false
    in
    let cls =
      try List.rev_map (fun s -> (s, Ast.Expr.Map.find s env.make)) cls
      with Not_found -> assert false
    in
    let e = Shostak.Combine.choose_adequate_model t rep cls in
    (e, Ast.Expr.Map.add t e mrepr)

let output_concrete_model ({ make; _ } as env) =
  let i = get_interpretation () in
  let abs_i = abs i in
  if abs_i = 1 || abs_i = 2 || abs_i = 3 then
    let functions, constants, arrays, _ =
      Ast.Expr.Map.fold
        (fun t _mk ((fprofs, cprofs, carrays, mrepr) as acc) ->
           let { Ast.Expr.f; xs; ty; _ } =
             match Ast.Expr.term_view t with
             | Ast.Expr.Not_a_term _ -> assert false
             | Ast.Expr.Term tt -> tt
           in
           if
             Shostak.Combine.is_solvable_theory_symbol f ty
             || Ast.Expr.is_fresh t
             || Ast.Expr.is_fresh_skolem t
             || Ast.Expr.equal t Ast.Expr.vrai
             || Ast.Expr.equal t Ast.Expr.faux
           then acc
           else
             let xs, tys, mrepr =
               List.fold_left
                 (fun (xs, tys, mrepr) x ->
                    let rep_x, mrepr = model_repr_of_term x env mrepr in
                    assert (is_a_good_model_value rep_x);
                    ((x, rep_x) :: xs, Ast.Expr.type_info x :: tys, mrepr))
                 ([], [], mrepr) (List.rev xs)
             in
             let rep, mrepr = model_repr_of_term t env mrepr in
             assert (is_a_good_model_value rep);
             match (f, xs, ty) with
             | Ast.Sy.Op Ast.Sy.Set, _, _ -> acc
             | ( Ast.Sy.Op Ast.Sy.Get,
                 [ (_, (a, _)); ((_, (i, _)) as e) ],
                 _ ) -> (
                 match Shostak.Combine.term_extract a with
                 | Some ta, true ->
                   let { Ast.Expr.f = f_ta; xs = xs_ta; _ } =
                     match Ast.Expr.term_view ta with
                     | Ast.Expr.Not_a_term _ -> assert false
                     | Ast.Expr.Term tt -> tt
                   in
                   assert (xs_ta == []);
                   ( fprofs,
                     cprofs,
                     Profile.add
                       (f_ta, [ Shostak.Combine.type_info i ], ty)
                       ([ e ], rep) carrays,
                     mrepr )
                 | _ -> assert false)
             | _ ->
               if tys == [] then
                 ( fprofs,
                   Profile.add (f, tys, ty) (xs, rep) cprofs,
                   carrays,
                   mrepr )
               else
                 ( Profile.add (f, tys, ty) (xs, rep) fprofs,
                   cprofs,
                   carrays,
                   mrepr ))
        make
        (Profile.empty, Profile.empty, Profile.empty, Ast.Expr.Map.empty)
    in
    if i > 0 then (
      Util.Printer.print_fmt ~flushed:false (get_fmt_mdl ()) "(@ ";
      SMT2LikeModelOutput.output_constants_model constants;
      SMT2LikeModelOutput.output_functions_model functions;
      SMT2LikeModelOutput.output_arrays_model arrays;
      Util.Printer.print_fmt (get_fmt_mdl ()) ")")
