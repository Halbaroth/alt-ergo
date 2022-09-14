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
module Z = Util.Numbers.Z
module Q = Util.Numbers.Q

exception Not_a_num
exception Maybe_zero

module type S = sig
  include Intf.X.Sig

  val mult : r -> r -> r
end

module type T = sig
  type r
  type t

  val zero : Ast.Ty.t -> t
  val one : Ast.Ty.t -> t
  val make : coeffs:(r * Q.t) list -> ctt:Q.t -> ty:Ast.Ty.t -> t
  val to_list : t -> (Q.t * r) list * Q.t
  val to_monomial : t -> (Q.t * r * Q.t) option
  val to_rational : t -> Q.t option
  val coef : r -> t -> Q.t
  val choose : t -> r * Q.t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val add_const : Q.t -> t -> t
  val mult_const : Q.t -> t -> t
  val ppmc_denominators : t -> Q.t
  val pgcd_numerators : t -> Q.t
  val modulo : t -> t -> t

  val div : t -> t -> t * bool
  val is_const : t -> bool
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val leaves : t -> r list
  val print : Format.formatter -> t -> unit
  val type_info : t -> Ast.Ty.t

  val normal_form : t -> t * Q.t * Q.t
  val normal_form_pos : t -> t * Q.t * Q.t
  val abstract_selectors : t -> (r * r) list -> t * (r * r) list
  val separate_constant : t -> t * Q.t
end

module type EXTENDED_Polynome = sig
  include T

  val extract : r -> t option
  val embed : t -> r
end

module Make (X : S) = struct
  type r = X.r

  module M : Map.S with type key = r = Map.Make (struct
      type t = r

      (*sorted in decreasing order to comply with AC(X) order requirements*)
      let compare v w = X.str_cmp w v
    end)

  type t = {
    coeffs : Q.t M.t; (* Map of the semantic values to their coefficient
                    in the polynomial. *)
    ctt : Q.t; (* Constant term of the polynomial. *)
    ty : Ast.Ty.t (* Alt-Ergo type of the polynomial. *)
  }

  let[@inline] zero ty = { coeffs = M.empty; ctt = Q.zero; ty }
  let[@inline] one ty = { coeffs = M.empty; ctt = Q.one; ty }

  let[@inline] type_info p = p.ty

  (* TODO: rename this function. *)
  let find v m = try M.find v m with Not_found -> Q.zero
  let[@inline] coef v p = M.find v p.coeffs

  let[@inline] is_const p = M.is_empty p.coeffs

  (* TODO: rename this function. *)
  let[@inline] choose p = M.min_binding p.coeffs

  let to_monomial p =
    try
      M.fold
        (fun v a r -> match r with None -> Some (a, v, p.ctt) | _ -> raise Exit)
        p.coeffs None
    with Exit -> None

  let to_rational p = if M.is_empty p.coeffs then Some p.ctt else None

  let map_to_list m =
    List.rev (M.fold (fun x a aliens -> (a, x) :: aliens) m [])

  exception Out of int

  let compare_maps l1 l2 =
    try
      List.iter2
        (fun (a, x) (b, y) ->
           let c = X.str_cmp x y in
           if c <> 0 then raise (Out c);
           let c = Q.compare a b in
           if c <> 0 then raise (Out c))
        l1 l2;
      0
    with
    | Out c -> c
    | Invalid_argument s ->
      assert (String.compare s "List.iter2" = 0);
      List.length l1 - List.length l2

  let compare p q =
    let c = Ast.Ty.compare p.ty q.ty in
    if c <> 0 then c
    else
      match (is_const p, is_const q) with
      | true, false -> -1
      | false, true -> 1
      | true, true -> Q.compare p.ctt q.ctt
      | false, false ->
        let c = compare_maps (map_to_list p.coeffs) (map_to_list q.coeffs) in
        if c = 0 then Q.compare p.ctt q.ctt else c

  (* BUG: The function does not test the type of the polynomials. *)
  let equal { coeffs = m1; ctt = c1; _ } { coeffs = m2; ctt = c2; _ } =
    Q.equal c1 c2 && M.equal Q.equal m1 m2

  let hash p =
    let h =
      M.fold
        (fun k v acc -> (23 * acc) + (X.hash k * Q.hash v))
        p.coeffs
        ((19 * Q.hash p.ctt) + (17 * Ast.Ty.hash p.ty))
    in
    abs h

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    let pprint fmt p =
      let zero = ref true in
      M.iter
        (fun x n ->
           let s, n, op =
             if Q.equal n Q.one then ((if !zero then "" else "+"), "", "")
             else if Q.equal n Q.m_one then ("-", "", "")
             else if Q.sign n > 0 then
               ((if !zero then "" else "+"), Q.to_string n, "*")
             else ("-", Q.to_string (Q.minus n), "*")
           in
           zero := false;
           fprintf fmt "%s%s%s%a" s n op X.print x)
        p.coeffs;
      let s, n =
        if Q.sign p.ctt > 0 then 
          ((if !zero then "" else "+"), Q.to_string p.ctt)
        else if Q.sign p.ctt < 0 then ("-", Q.to_string (Q.minus p.ctt))
        else if !zero then ("", "0")
        else ("", "")
      in
      fprintf fmt "%s%s" s n

    let print fmt p =
      if Util.Options.get_term_like_pp () then pprint fmt p
      else (
        M.iter (fun t n -> fprintf fmt "%s*%a " 
          (Q.to_string n) X.print t) p.coeffs;
        fprintf fmt "%s%s"
          (if Q.compare_to_0 p.ctt >= 0 then "+ " else "")
          (Q.to_string p.ctt);
        fprintf fmt " [%a]" Ast.Ty.print p.ty)
  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  (* TODO: rename this function. *)
  (* BUG: not checking of the AE type of the elements in the list. *)
  let make ~coeffs ~ctt ~ty =
    let coeffs =
      List.fold_left
        (fun m (v, a) ->
           let b = Q.add a (find v m) in
           if Q.sign b = 0 then M.remove v m else M.add v b m)
        M.empty coeffs
    in
    { coeffs; ctt; ty }

  let add p1 p2 =
    Util.Options.tool_req 4 "TR-Arith-Poly plus";
    let coeffs =
      M.fold
        (fun x a m ->
           let a' = Q.add (find x m) a in
           if Q.sign a' = 0 then M.remove x m else M.add x a' m)
        p2.coeffs p1.coeffs
    in
    { coeffs; ctt = Q.add p1.ctt p2.ctt; ty = p1.ty }

  let sub p1 p2 =
    Util.Options.tool_req 4 "TR-Arith-Poly moins"; (*TODO: remove french. *)
    let coeffs =
      M.fold
        (fun x a m ->
           let a' = Q.sub (find x m) a in
           if Q.sign a' = 0 then M.remove x m else M.add x a' m)
        p2.coeffs p1.coeffs
    in
    { coeffs; ctt = Q.sub p1.ctt p2.ctt; ty = p1.ty }

  let add_const n p = { p with ctt = Q.add p.ctt n }

  let mult_const n p =
    if Q.sign n = 0 then zero (type_info p)
    else { p with coeffs = M.map (Q.mult n) p.coeffs; ctt = Q.mult n p.ctt }

  (* Multiply the polynome p by the monome av. *)
  let mult_monomial v a p =
    let av = { coeffs = M.add v a M.empty; ctt = Q.zero; ty = p.ty } in
    let acv = mult_const p.ctt av in
    let coeffs =
      M.fold (fun vi ai m -> M.add (X.mult v vi) (Q.mult a ai) m) 
      p.coeffs acv.coeffs
    in
    { acv with coeffs }

  let mult p q =
    Util.Options.tool_req 4 "TR-Arith-Poly mult";
    let r = mult_const p.ctt q in
    M.fold (fun v a r -> add (mult_monomial v a q) r) p.coeffs r

  (* TODO: move this function. *)
  let euc_mod_num c1 c2 =
    let c = Q.modulo c1 c2 in
    if Q.sign c < 0 then Q.add c (Q.abs c2) else c

  (* TODO: move this function. *)
  let euc_div_num c1 c2 = Q.div (Q.sub c1 (euc_mod_num c1 c2)) c2

  (* TODO: remove this function. *)
  let div p q =
    Util.Options.tool_req 4 "TR-Arith-Poly div";
    if not @@ is_const q then raise Maybe_zero;
    if Q.sign q.ctt = 0 then raise Division_by_zero;
    let r = mult_const (Q.div Q.one q.ctt) p in
    match (is_const r, r.ty) with
    | _, Ast.Ty.Treal -> (r, false)
    | true, Ast.Ty.Tint -> ({ r with ctt = euc_div_num p.ctt q.ctt }, false)
    | false, Ast.Ty.Tint -> (r, true (* XXX *))
    | _ -> assert false

  (* TODO: remove this function. *)
  let modulo p q =
    Util.Options.tool_req 4 "TR-Arith-Poly mod";
    if not @@ is_const q then raise Maybe_zero;
    if Q.sign q.ctt = 0 then raise Division_by_zero;
    if not @@ is_const p then raise Not_a_num;
    { p with ctt = euc_mod_num p.ctt q.ctt }

  let subst v p q =
    try
      let a = coef v q in
      add (mult_const a p) { q with coeffs = M.remove v q.coeffs }
    with Not_found -> q

  let remove v p = { p with coeffs = M.remove v p.coeffs }

  (** TODO: rename this function. *)
  let to_list p = (map_to_list p.coeffs, p.ctt)

  module SX = Set.Make (struct
      type t = r

      let compare = X.hash_cmp
    end)

  let xs_of_list sx l = List.fold_left (fun s x -> SX.add x s) sx l

  let leaves p =
    let s = 
      M.fold (fun a _ s -> xs_of_list s (X.leaves a)) p.coeffs SX.empty 
    in
    SX.elements s

  (* TODO: rename this function. *)
  let ppmc_denominators { coeffs; _ } =
    let res = M.fold (fun _ c acc -> Z.my_lcm (Q.den c) acc) coeffs Z.one in
    Q.abs (Q.from_z res)

  (* TODO: rename this function. *)
  let pgcd_numerators { coeffs; _ } =
    let res = M.fold (fun _ c acc -> Z.my_gcd (Q.num c) acc) coeffs Z.zero in
    Q.abs (Q.from_z res)

  let normal_form p =
    if is_const p then ({ p with ctt = Q.zero }, p.ctt, Q.one)
    else
      let ppcm = ppmc_denominators p in
      let pgcd = pgcd_numerators p in
      let p = mult_const (Q.div ppcm pgcd) p in
      ({ p with ctt = Q.zero }, p.ctt, Q.div pgcd ppcm)

  let normal_form_pos p =
    let p, c, d = normal_form p in
    try
      let _, a = choose p in
      if Q.sign a > 0 then (p, c, d)
      else (mult_const Q.m_one p, Q.minus c, Q.minus d)
    with Not_found -> (p, c, d)

  let abstract_selectors p acc =
    let mp, acc =
      M.fold
        (fun r i (mp, acc) ->
           let r, acc = X.abstract_selectors r acc in
           let mp =
             try
               let j = M.find r mp in
               let k = Q.add i j in
               if Q.sign k = 0 then M.remove r mp else M.add r k mp
             with Not_found -> M.add r i mp
           in
           (mp, acc))
        p.coeffs (M.empty, acc)
    in
    ({ p with coeffs = mp }, acc)

  let separate_constant p = ({ p with ctt = Q.zero }, p.ctt)
end
