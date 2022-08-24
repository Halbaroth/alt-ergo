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

type 'a abstract =
  | Constr of {
      c_name : Util.Hstring.t;
      c_ty : Ast.Ty.t;
      c_args : (Util.Hstring.t * 'a) list;
    }
  | Select of { d_name : Util.Hstring.t; d_ty : Ast.Ty.t; d_arg : 'a }
  | Tester of { t_name : Util.Hstring.t; t_arg : 'a }
  (* tester is currently not used *)
  | Alien of 'a

module type ALIEN = sig
  include Intf.X.Sig

  val embed : r abstract -> r
  val extract : r -> r abstract option
end

(* TODO: can this function be replace with Ast.Ty.assoc_destrs ?? *)
let constr_of_destr ty dest =
  if get_debug_adt () then
    Util.Printer.print_dbg ~module_name:"Adt" ~function_name:"constr_of_destr"
      "ty = %a" Ast.Ty.print ty;
  match ty with
  | Ast.Ty.Tadt (s, params) -> (
      let bdy = Ast.Ty.type_body s params in
      match bdy with
      | Ast.Ty.Adt cases -> (
          try
            List.find
              (fun { Ast.Ty.destrs; _ } ->
                 List.exists (fun (d, _) -> Util.Hstring.equal dest d) destrs)
              cases
          with Not_found -> assert false (* invariant *)))
  | _ -> assert false

module Shostak (X : ALIEN) = struct
  type t = X.r abstract
  type r = X.r

  module SX = Set.Make (struct
      type t = r

      let compare = X.hash_cmp
    end)

  let name = "Adt"
  [@@ocaml.ppwarning "XXX: IsConstr not interpreted currently. Maybe it's OK"]

  let is_mine_symb sy ty =
    (not (get_disable_adts ()))
    &&
    match (sy, ty) with
    | Ast.Sy.Op (Ast.Sy.Constr _), Ast.Ty.Tadt _ -> true
    | Ast.Sy.Op (Ast.Sy.Destruct (_, guarded)), _ -> not guarded
    | _ -> false

  let embed r = match X.extract r with Some c -> c | None -> Alien r

  let print fmt = function
    | Alien x -> fprintf fmt "%a" X.print x
    | Constr { c_name; c_args; _ } -> (
        fprintf fmt "%a" Util.Hstring.print c_name;
        match c_args with
        | [] -> ()
        | (lbl, v) :: l ->
          fprintf fmt "(%a : %a " Util.Hstring.print lbl X.print v;
          List.iter
            (fun (lbl, v) ->
               fprintf fmt "; %a : %a" Util.Hstring.print lbl X.print v)
            l;
          fprintf fmt ")")
    | Select d ->
      fprintf fmt "%a#!!%a" X.print d.d_arg Util.Hstring.print d.d_name
    | Tester t ->
      fprintf fmt "(%a ? %a)" X.print t.t_arg Util.Hstring.print t.t_name

  let is_mine u =
    match u with
    | Alien r -> r
    | Constr _ | Tester _ ->
      X.embed u [@ocaml.ppwarning "TODO: canonize Constr(list of selects)"]
    | Select { d_arg; d_name; _ } -> (
        match embed d_arg with
        | Constr c -> (
            try
              snd
              @@ List.find
                (fun (lbl, _) -> Util.Hstring.equal d_name lbl)
                c.c_args
            with Not_found ->
              Util.Printer.print_err "is_mine %a failed" print u;
              assert false)
        | _ -> X.embed u)

  let equal s1 s2 =
    match (s1, s2) with
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Constr c1, Constr c2 -> (
        Util.Hstring.equal c1.c_name c2.c_name
        && Ast.Ty.equal c1.c_ty c2.c_ty
        &&
        try
          List.iter2
            (fun (hs1, v1) (hs2, v2) ->
               assert (Util.Hstring.equal hs1 hs2);
               if not (X.equal v1 v2) then raise Exit)
            c1.c_args c2.c_args;
          true
        with
        | Exit -> false
        | _ -> assert false)
    | Select d1, Select d2 ->
      Util.Hstring.equal d1.d_name d2.d_name
      && Ast.Ty.equal d1.d_ty d2.d_ty
      && X.equal d1.d_arg d2.d_arg
    | Tester t1, Tester t2 ->
      Util.Hstring.equal t1.t_name t2.t_name && X.equal t1.t_arg t2.t_arg
    | _ -> false

  let make t =
    assert (not (get_disable_adts ()));
    if get_debug_adt () then
      Util.Printer.print_dbg ~module_name:"Adt" ~function_name:"make" "make %a"
        Ast.Expr.print t;
    let { Ast.Expr.f; xs; ty; _ } =
      match Ast.Expr.term_view t with
      | Ast.Expr.Term t -> t
      | Ast.Expr.Not_a_term _ -> assert false
    in
    let sx, ctx =
      List.fold_left
        (fun (args, ctx) s ->
           let rs, ctx' = X.make s in
           (rs :: args, List.rev_append ctx' ctx))
        ([], []) xs
    in
    let xs = List.rev sx in
    match (f, xs, ty) with
    | Ast.Sy.Op (Ast.Sy.Constr hs), _, Ast.Ty.Tadt (name, params) ->
      let cases =
        match Ast.Ty.type_body name params with
        | Ast.Ty.Adt cases -> cases
      in
      let case_hs =
        try Ast.Ty.assoc_destrs hs cases with Not_found -> assert false
      in
      let c_args =
        try
          List.rev
          @@ List.fold_left2
            (fun c_args v (lbl, _) -> (lbl, v) :: c_args)
            [] xs case_hs
        with Invalid_argument _ -> assert false
      in
      (is_mine @@ Constr { c_name = hs; c_ty = ty; c_args }, ctx)
    | Ast.Sy.Op (Ast.Sy.Destruct (hs, guarded)), [ e ], _ ->
      if not guarded then
        let sel = Select { d_name = hs; d_arg = e; d_ty = ty } in
        (is_mine sel, ctx)
      else (X.term_embed t, ctx)
    (* No risk !
         if equal sel (embed sel_x) then X.term_embed t, ctx
         else sel_x, ctx (* canonization OK *)
    *)
    | _ -> assert false

  let hash x =
    abs
    @@
    match x with
    | Alien r -> X.hash r
    | Constr { c_name; c_ty; c_args } ->
      List.fold_left
        (fun acc (_, r) -> (acc * 7) + X.hash r)
        (Util.Hstring.hash c_name + (7 * Ast.Ty.hash c_ty))
        c_args
    | Select { d_name; d_ty; d_arg } ->
      ((Util.Hstring.hash d_name + (11 * Ast.Ty.hash d_ty)) * 11)
      + X.hash d_arg
    | Tester { t_name; t_arg } -> (Util.Hstring.hash t_name * 13) + X.hash t_arg

  let leaves r =
    let l =
      match r with
      | Alien r -> [ (Util.Hstring.empty, r) ]
      | Constr { c_args; _ } -> c_args
      | Select { d_arg; _ } -> [ (Util.Hstring.empty, d_arg) ]
      | Tester { t_arg; _ } -> [ (Util.Hstring.empty, t_arg) ]
    in
    SX.elements
    @@ List.fold_left
      (fun sx (_, r) ->
         List.fold_left (fun sx x -> SX.add x sx) sx (X.leaves r))
      SX.empty l
  [@@ocaml.ppwarning "TODO: not sure"]

  let fully_interpreted _ = false
  (* not sure *)
  (*
    not (get_disable_adts ()) &&
    match sb with
    | Ast.Sy.Op (Ast.Sy.Constr _) -> true
    | Ast.Sy.Op Ast.Sy.Destruct (_, guarded) -> not guarded
    | _ -> false
*)

  let type_info = function
    | Alien r -> X.type_info r
    | Constr { c_ty; _ } -> c_ty
    | Select { d_ty; _ } -> d_ty
    | Tester _ -> Ast.Ty.Tbool

  let compare s1 s2 =
    match (s1, s2) with
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien _, _ -> 1
    | _, Alien _ -> -1
    | Constr c1, Constr c2 -> (
        let c = Util.Hstring.compare c1.c_name c2.c_name in
        if c <> 0 then c
        else
          let c = Ast.Ty.compare c1.c_ty c2.c_ty in
          if c <> 0 then c
          else
            try
              List.iter2
                (fun (hs1, v1) (hs2, v2) ->
                   assert (Util.Hstring.equal hs1 hs2);
                   let c = X.str_cmp v1 v2 in
                   if c <> 0 then raise (Util.Util.Cmp c))
                c1.c_args c2.c_args;
              0
            with
            | Util.Util.Cmp c -> c
            | _ -> assert false)
    | Constr _, _ -> 1
    | _, Constr _ -> -1
    | Select d1, Select d2 ->
      let c = Util.Hstring.compare d1.d_name d2.d_name in
      if c <> 0 then c
      else
        let c = Ast.Ty.compare d1.d_ty d2.d_ty in
        if c <> 0 then c else X.str_cmp d1.d_arg d2.d_arg
    | Select _, _ -> 1
    | _, Select _ -> -1
    | Tester t1, Tester t2 ->
      let c = Util.Hstring.compare t1.t_name t2.t_name in
      if c <> 0 then c else X.str_cmp t1.t_arg t2.t_arg

  let abstract_selectors p acc =
    match p with
    | Alien _ -> assert false (* handled in Combine *)
    | Constr { c_args; _ } ->
      let same = ref true in
      let acc, _ =
        List.fold_left
          (fun (acc, l) (lbl, x) ->
             let y, acc = X.abstract_selectors x acc in
             same := !same && x == y;
             (acc, (lbl, y) :: l))
          (acc, []) c_args
      in
      if !same then (is_mine p, acc)
      else
        ( is_mine p,
          (acc [@ocaml.ppwarning "TODO: abstract Selectors: case to test"]) )
    (* assert false
       should probably reconstruct a new 'p' using args
    *)
    | Tester { t_arg; _ } ->
      let s_arg, acc = X.abstract_selectors t_arg acc in
      if
        not (X.equal s_arg t_arg)
        [@ocaml.ppwarning "TODO: abstract Selectors: case to test"]
      then assert false;
      (is_mine p, acc)
    | ((Select ({ d_arg; _ } as s))
       [@ocaml.ppwarning "TODO: abstract Selectors"]) -> (
        (* no need to abstract THIS selector. It's necessiraly
           toplevel in ADTs *)
        (*
         /!\ All this is not clear ! should review this code ==>
         Keep in mind that this is a non guarded select; the only one that
         is interpreted
      *)
        let s_arg, acc = X.abstract_selectors d_arg acc in
        if
          not (X.equal s_arg d_arg)
          [@ocaml.ppwarning "TODO: abstract Selectors"]
        then assert false;
        let x = is_mine @@ Select { s with d_arg = s_arg } in
        match embed x with
        | Select ({ d_name; d_arg; _ } as s) ->
          let { Ast.Ty.constr; destrs } =
            constr_of_destr (X.type_info d_arg) d_name
          in
          let xs =
            List.map (fun (_, ty) -> Ast.Expr.fresh_name ty) destrs
          in
          let cons =
            Ast.Expr.mk_term
              (Ast.Sy.constr (Util.Hstring.view constr))
              xs (X.type_info d_arg)
          in
          if get_debug_adt () then
            Util.Printer.print_dbg ~flushed:false ~module_name:"Adt"
              ~function_name:"abstract_selectors"
              "abstr with equality %a == %a@ " X.print d_arg
              Ast.Expr.print cons;
          let cons, _ = make cons in
          let acc = (d_arg, cons) :: acc in
          let xx = is_mine @@ Select { s with d_arg = cons } in
          if get_debug_adt () then
            Util.Printer.print_dbg ~header:false "%a becomes %a" X.print x
              X.print xx;
          (xx, acc)
        | _ -> (x, acc))

  let is_alien_of e x = List.exists (fun y -> X.equal x y) (X.leaves e)

  let solve r1 r2 pb =
    if get_debug_adt () then
      Util.Printer.print_dbg ~module_name:"Adt" ~function_name:"solve"
        "solve %a = %a" X.print r1 X.print r2;
    assert (not (get_disable_adts ()));
    match (embed r1, embed r2) with
    | Select _, _ | _, Select _ -> assert false (* should be eliminated *)
    | Tester _, _ | _, Tester _ -> assert false (* not interpreted *)
    | Alien _, Alien _ ->
      {
        pb with
        Intf.Solvable_theory.sbt = (if X.str_cmp r1 r2 > 0 then (r1, r2) else (r2, r1)) :: pb.Intf.Solvable_theory.sbt;
      }
    | Alien r, Constr _ ->
      if is_alien_of r2 r then raise Util.Util.Unsolvable;
      { pb with sbt = (r, r2) :: pb.sbt }
    | Constr _, Alien r ->
      if is_alien_of r1 r then raise Util.Util.Unsolvable;
      { pb with sbt = (r, r1) :: pb.sbt }
    | Constr c1, Constr c2 -> (
        if not (Util.Hstring.equal c1.c_name c2.c_name) then
          raise Util.Util.Unsolvable;
        try
          {
            pb with
            eqs =
              List.fold_left2
                (fun eqs (hs1, v1) (hs2, v2) ->
                   assert (Util.Hstring.equal hs1 hs2);
                   (v1, v2) :: eqs)
                pb.eqs c1.c_args c2.c_args;
          }
        with Invalid_argument _ -> assert false)

  let subst p v s =
    (*TODO: detect when there are no changes to improve *)
    assert (not (get_disable_adts ()));
    match s with
    | Alien r -> if X.equal p r then v else X.subst p v r
    | Constr c ->
      is_mine
      @@ Constr
        {
          c with
          c_args = List.map (fun (lbl, u) -> (lbl, X.subst p v u)) c.c_args;
        }
    | Select d -> is_mine @@ Select { d with d_arg = X.subst p v d.d_arg }
    | Tester t -> is_mine @@ Tester { t with t_arg = X.subst p v t.t_arg }

  let color _ = assert false
  let term_extract _ = (None, false)

  let assign_value _ _ _ =
    Util.Printer.print_err
      "[ADTs.models] assign_value currently not implemented";
    assert false

  let choose_adequate_model _ _ _ =
    Util.Printer.print_err
      "[ADTs.models] choose_adequate_model currently not implemented";
    assert false
end
