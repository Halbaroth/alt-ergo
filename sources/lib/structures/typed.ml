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

[@@@ocaml.warning "-33"]
open Options


(** Anotations (used by the GUI). *)

type ('a, 'b) annoted =
  { c : 'a;
    annot : 'b }

let new_id = let r = ref 0 in fun () -> r := !r+1; !r

let mk ?(annot=new_id ()) c = { c; annot; }


(** Terms and Formulas *)

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type oplogic =
    OPand | OPor | OPxor | OPimp | OPnot | OPiff
  | OPif

(** type of pattern in match construct of ADTs *)
type pattern =
  | Constr of { name : Hstring.t ; args : (Var.t * Hstring.t * Ty.t) list}
  (** A pattern case which is a constructor. [name] is the name of
      constructor. [args] contains the variables bound by this pattern
      with their correponsing destructors and types *)

  | Var of Var.t
  (** a pattern that is a variable (or underscore) *)

type 'a tterm =
  { tt_ty : Ty.t; tt_desc : 'a tt_desc }

and 'a atterm = ('a tterm, 'a) annoted

and 'a tt_desc =
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTmapsTo of Var.t * ('a tterm, 'a) annoted
  | TTinInterval of 'a atterm * Symbols.bound * Symbols.bound
  (* bool = true <-> interval is_open *)

  | TTget of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTset of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTextract of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTconcat of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTdot of ('a tterm, 'a) annoted * Hstring.t
  | TTrecord of (Hstring.t * ('a tterm, 'a) annoted) list
  | TTlet of (Symbols.t * ('a tterm, 'a) annoted) list * ('a tterm, 'a) annoted
  | TTnamed of Hstring.t * ('a tterm, 'a) annoted
  | TTite of ('a tform, 'a) annoted *
             ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTproject of bool * ('a tterm, 'a) annoted  * Hstring.t
  | TTmatch of 'a atterm * (pattern * 'a atterm) list
  | TTform of 'a atform

and 'a atatom = ('a tatom, 'a) annoted

and 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted * bool (* true <-> negated *)
  | TTisConstr of ('a tterm, 'a) annoted  * Hstring.t

and 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : (('a tterm, 'a) annoted list * bool) list ;
  qf_hyp : ('a tform, 'a) annoted list;
  qf_form : ('a tform, 'a) annoted
}

and 'a atform = ('a tform, 'a) annoted

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted
  | TFmatch of 'a atterm * (pattern * 'a atform) list

and 'a tlet_kind =
  | TletTerm of ('a tterm, 'a) annoted
  | TletForm of ('a tform, 'a) annoted

(** Toplevel common components *)

let true_atatom     = {c=TAtrue; annot = new_id ()}
let false_atatom    = {c=TAfalse; annot = new_id ()}

let true_tform      = TFatom true_atatom
let false_tform     = TFatom false_atatom

let true_atform  = {c = true_tform; annot = new_id()}
let false_atform = {c = false_tform; annot = new_id()}

let true_term    = {tt_desc = TTconst Ttrue; tt_ty=Ty.Tbool}
let false_term   = {tt_desc = TTconst Tfalse; tt_ty=Ty.Tbool}

let true_atterm  = {c = true_term; annot = new_id ()}
let false_atterm = {c = false_term; annot = new_id ()}

(** Rewrite rules *)

type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

let print_rwt pp fmt r =
  Format.fprintf fmt "@<hv>%a@ --> %a@]" pp r.rwt_left pp r.rwt_right


(** Goal sort *)

type goal_sort = Cut | Check | Thm

let print_goal_sort fmt = function
  | Cut -> Format.fprintf fmt "cut"
  | Check -> Format.fprintf fmt "check"
  | Thm -> Format.fprintf fmt "thm"


(** Logic type *)

type tlogic_type =
  | TPredicate of Ty.t list
  | TFunction of Ty.t list * Ty.t

(** Declarations *)

type 'a atdecl = ('a tdecl, 'a) annoted

and 'a tdecl =
  (* to simplify impl and extension of GUI, a TTtheory is seen a list
     of tdecl, although we only allow axioms in theories
     declarations *)
  | TTheory of
      Loc.t * string * Util.theories_extensions * ('a tdecl, 'a) annoted list
  | TAxiom of Loc.t * string * Util.axiom_kind * ('a tform, 'a) annoted
  | TRewriting of Loc.t * string * (('a tterm, 'a) annoted rwt_rule) list
  | TGoal of Loc.t * goal_sort * string * ('a tform, 'a) annoted
  | TLogic of Loc.t * string list * tlogic_type
  | TPredicate_def of
      Loc.t * string *
      (string * Ty.t) list * ('a tform, 'a) annoted
  | TFunction_def of
      Loc.t * string *
      (string * Ty.t) list * Ty.t * ('a tform, 'a) annoted
  | TTypeDecl of Loc.t * Ty.t

(*****)

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | OPxor -> "xor"
  | OPif -> "ite"
  | _ -> assert false

type 'annot annot_printer = Format.formatter -> 'annot -> unit
type ('a,'annot) annoted_printer = Format.formatter -> ('a,'annot) annoted -> unit

let (no_print : _ annot_printer) = fun fmt _ -> fprintf fmt ""
let (int_print : int annot_printer) = fun fmt -> fprintf fmt ".%i"

let print_annot
    (annot : 'annot annot_printer)
    (print : ('a,'annot) annoted_printer)
    (fmt : Format.formatter) (t : ('a, 'annot) annoted) =
  fprintf fmt "%a%a" print t annot t.annot

let print_binder fmt (s, t) =
  fprintf fmt "%a :%a" Symbols.print s Ty.print t

let print_binders fmt l =
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l
 
let rec print_term ?(annot=no_print) fmt t =
  let printer fmt t =
    match t.c.tt_desc with
    | TTconst Ttrue ->
      fprintf fmt "true"
    | TTconst Tfalse ->
      fprintf fmt "false"
    | TTconst Tvoid ->
      fprintf fmt "void"
    | TTconst (Tint n) ->
      fprintf fmt "%s" n
    | TTconst (Treal n) ->
      fprintf fmt "%s" (Num.string_of_num n)
    | TTconst Tbitv s ->
      fprintf fmt "%s" s
    | TTvar s ->
      fprintf fmt "%a" Symbols.print s
    | TTapp(s,l) ->
      fprintf fmt "%a(%a)" Symbols.print s (print_term_list ~annot) l
    | TTinfix(t1,s,t2) ->
      fprintf fmt "%a %a %a" (print_term ~annot) t1 Symbols.print s (print_term ~annot) t2
    | TTprefix (s, t') ->
      fprintf fmt "%a %a" Symbols.print s (print_term ~annot) t'
    | TTget (t1, t2) ->
      fprintf fmt "%a[%a]" (print_term ~annot) t1 (print_term ~annot) t2
    | TTset (t1, t2, t3) ->
      fprintf fmt "%a[%a<-%a]" (print_term ~annot) t1 (print_term ~annot) t2 (print_term ~annot) t3
    | TTextract (t1, t2, t3) ->
      fprintf fmt "%a^{%a,%a}" (print_term ~annot) t1 (print_term ~annot) t2 (print_term ~annot) t3
    | TTconcat (t1, t2) ->
      fprintf fmt "%a @ %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TTdot (t1, s) ->
      fprintf fmt "%a.%s" (print_term ~annot) t1 (Hstring.view s)
    | TTrecord l ->
      fprintf fmt "{ ";
      List.iter
        (fun (s, t) -> fprintf fmt "%s = %a" (Hstring.view s) (print_term ~annot) t) l;
      fprintf fmt " }"
    | TTlet (binders, t2) ->
      fprintf fmt "let %a in %a" (print_term_binders ~annot) binders (print_term ~annot) t2
    | TTnamed (_, t) ->
      fprintf fmt "%a" (print_term ~annot) t

    | TTinInterval(e, i, j) ->
      fprintf fmt "%a in %a, %a"
        (print_term ~annot) e
        Symbols.print_bound i
        Symbols.print_bound j

    | TTmapsTo(x,e) ->
      fprintf fmt "%a |-> %a" Var.print x (print_term ~annot) e

    | TTite(cond, t1, t2) ->
      fprintf fmt "(if %a then %a else %a)"
        (print_formula ~annot) cond (print_term ~annot) t1 (print_term ~annot) t2
    | TTproject (grded, t1, s) ->
      fprintf fmt "%a#%s%s"
        (print_term ~annot) t1 (if grded then "" else "!") (Hstring.view s)

    | TTform f ->
      fprintf fmt "%a" (print_formula ~annot) f

    | TTmatch (e, cases) ->
      let pp_vars fmt l =
        match l with
          [] -> ()
        | [e,_,_] -> Var.print fmt e
        | (e,_,_) :: l ->
          fprintf fmt "(%a" Var.print e;
          List.iter (fun (e,_,_) -> fprintf fmt ", %a" Var.print e) l;
          fprintf fmt ")"
      in
      fprintf fmt "match %a with\n" (print_term ~annot) e;
      List.iter
        (fun (p, v) ->
           match p with
           | Constr {name = n; args = l} ->
             fprintf fmt "| %a %a -> %a\n" Hstring.print n pp_vars l (print_term ~annot) v
           | Var x ->
             fprintf fmt "| %a -> %a\n" Var.print x (print_term ~annot) v;
        )cases;
      fprintf fmt "end@."
  in
  print_annot annot printer fmt t

and print_term_binders ?(annot=no_print) fmt l =
  match l with
  | [] -> assert false
  | (sy, t) :: l ->
    fprintf fmt "%a = %a" Symbols.print sy (print_term ~annot) t;
    List.iter (fun (sy, t) ->
        fprintf fmt ", %a = %a" Symbols.print sy (print_term ~annot) t) l

and print_term_list
    ?(annot=no_print) fmt = List.iter (fprintf fmt "%a," (print_term ~annot))

and print_atom ?(annot: 'annot annot_printer =no_print) fmt (a : 'annot atatom) =
  let printer fmt a =
    match a.c with
    | TAtrue ->
      fprintf fmt "True"
    | TAfalse ->
      fprintf fmt "False"
    | TAeq [t1; t2] ->
      fprintf fmt "%a = %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TAneq [t1; t2] ->
      fprintf fmt "%a <> %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TAle [t1; t2] ->
      fprintf fmt "%a <= %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TAlt [t1; t2] ->
      fprintf fmt "%a < %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TApred (t, negated) ->
      if negated then fprintf fmt "(not (%a))" (print_term ~annot) t
      else (print_term ~annot) fmt t
    | TTisConstr (t1, s) ->
      fprintf fmt "%a ? %s" (print_term ~annot) t1 (Hstring.view s)
    | _ -> fprintf fmt "(atom pprint not implemented)"
  in
  print_annot annot printer fmt a

and print_triggers ?(annot=no_print) fmt l =
  List.iter (fun (tr, _) -> fprintf fmt "%a | " (print_term_list ~annot) tr) l

and print_formula ?(annot=no_print) fmt f =
  let print_formula = print_formula ~annot in
  let printer fmt f  =
    match f.c with
    | TFatom a ->
      (print_atom ~annot) fmt a
    | TFop(OPnot, [f]) ->
      fprintf fmt "not (%a)" print_formula f
    | TFop(OPif, [cond; f1;f2]) ->
      fprintf fmt "if (%a) then (%a) else (%a)"
        print_formula cond print_formula f1 print_formula f2
    | TFop(op, [f1; f2]) ->
      fprintf fmt "(%a) %s (%a)" print_formula f1 (string_of_op op) print_formula f2
    | TFforall { qf_bvars = l; qf_triggers = t; qf_form = f; _ } ->
      fprintf fmt "forall (%a) [%a]. (%a)"
        print_binders l (print_triggers ~annot) t print_formula f

    | TFlet (_, binders, f) ->
      List.iter
        (fun (sy, let_e) ->
           fprintf fmt " let %a = " Symbols.print sy;
           match let_e with
           | TletTerm t -> fprintf fmt "(%a) in@." (print_term ~annot) t
           | TletForm f -> fprintf fmt "(%a) in@." print_formula f
        )binders;
      fprintf fmt "%a" print_formula f
    | TFexists _ -> fprintf fmt "(existential formula pprint not implemented)"
    | TFmatch _ ->  fprintf fmt "(match formula pprint not implemented)"
    | TFop _ -> fprintf fmt "(operator formula pprint not implemented)"
    | TFnamed _ ->  fprintf fmt "(named formula pprint not implemented)"
  in
  print_annot annot printer fmt f

let rec print_tdecl ?(annot=no_print) fmt = function
  | TTheory (_, name, _, l) ->
    Format.fprintf fmt "th %s: @[<v>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space ~pp:print_atdecl) l
  | TAxiom (_, name, _kind, f) ->
    Format.fprintf fmt "ax %s: @[<hov>%a@]" name (print_formula ~annot) f
  | TRewriting (_, name, l) ->
    Format.fprintf fmt "rwt %s: @[<hov>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space
         ~pp:(print_rwt print_term)) l
  | TGoal (_, _sort, name, f) ->
    Format.fprintf fmt "goal %s: @[<hov>%a@]" name (print_formula ~annot) f
  | TPredicate_def (_,str,_,form) ->
    Format.fprintf fmt "Predicate %s :\n %a" str (print_formula ~annot) form
  | TFunction_def (_,str,_,_,form) ->
    Format.fprintf fmt "Function %s :\n %a" str (print_formula ~annot) form
  | _ -> Format.fprintf fmt ""

and print_atdecl ?(annot=no_print) fmt a =
  print_annot annot (fun fmt a -> print_tdecl ~annot fmt a.c) fmt a


let fresh_hypothesis_name =
  let cpt = ref 0 in
  fun sort ->
    incr cpt;
    match sort with
    | Thm -> "@H"^(string_of_int !cpt)
    | _ -> "@L"^(string_of_int !cpt)

let is_local_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@H" with Invalid_argument _ -> false
