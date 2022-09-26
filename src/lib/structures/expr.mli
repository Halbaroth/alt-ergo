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

(** {1 Types} *)

type t
(** Type of an expression. *)

type binders = (Ty.t * int) Symbols.Map.t (*int tag in globally unique *)

(** Type of kind of declaration. *)
type decl_kind =
  | Dtheory
  | Daxiom
  | Dgoal
  | Dpredicate of t
  | Dfunction of t

(* TODO: Make this type abstract. *)
type view = private {
  (* TODO: Rename this field to top_sy. *)
  f: Symbols.t;                      (** Top symbol. *)
  (* TODO: Rename this filed to args. *)
  xs: t list;                        (** List of arguments. *)
  ty: Ty.t;                          (** Alt-Ergo type of the expression. *)
  bind : bind_kind;                  (** Kind of bind used in the expression. *)
  (* TODO: Rename this field to id. *)
  tag: int;                          (** Tag used by the hconsing. *)
  vars : (Ty.t * int) Symbols.Map.t;
  (** Correspondance between variables and their type and number
      of occurences in the expression. *)

  vty : Ty.Svty.t;
  (** Set of free Alt-Ergo type variables occuring in the expression. *)

  depth: int;                        (** Depth of the expression. *)
  nb_nodes : int;                    (** Number of nodes in the expression. *)
  pure : bool;

  mutable neg : t option
  (** Negation of an expression of Alt-Ergo type {!constructor:Ty.Tbool}.
      If the expression is not of the type {!constructor:Ty.Tbool},
      this field is always equal to [None]. *)
}

(** Type of bind. *)
and bind_kind =
  | B_none                 (** No bind. *)
  | B_lemma of quantified
  | B_skolem of quantified
  | B_let of letin         (** Let bind. *)

(* TODO: Make this type abstract. *)
and quantified = private {
  name : string;
  main : t;
  toplevel : bool;
  user_trs : trigger list;
  binders : binders;
  (* These fields should be (ordered) lists ! important for skolemization *)
  sko_v : t list;
  sko_vty : Ty.t list;
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
  kind : decl_kind;
}

(** Type of a let expression: let let_v = let_e in in_e. *)
and letin = private {
  let_v: Symbols.t; (** Variable of the substitution. *)
  let_e : t;        (** Expression of the substitution. *)
  in_e : t;         (** Expression in which we apply the substitution. *)
  let_sko : t; (* fresh symb. with free vars *)
  is_bool : bool;
}

and semantic_trigger =
  | Interval of t * Symbols.bound * Symbols.bound
  | MapsTo of Var.t * t
  | NotTheoryConst of t
  | IsTheoryConst of t
  | LinearDependency of t * t

and trigger = (*private*) {
  content : t list;
  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : t list;
  t_depth : int;
  from_user : bool;
  guard : t option
}

type subst = t Symbols.Map.t * Ty.subst

type term_view = private
  | Term of view
  | Not_a_term of {is_lit : bool}

type lit_view = private
  | Eq of t * t
  | Eql of t list
  (** Equality of two expressions. *)

  | Distinct of t list
  | Builtin of bool * Symbols.builtin * t list
  | Pred of t * bool
  (** Predicate. *)

  | Not_a_lit of { is_form : bool }

type form_view = private
  | Unit of t*t          (** Unit clause *)
  | Clause of t*t*bool   (** a clause (t1 or t2) bool <-> is implication *)
  | Iff of t * t
  | Xor of t * t
  | Literal of t         (** Literal *)
  | Lemma of quantified  (** a lemma *)
  | Skolem of quantified (** lazy skolemization *)
  | Let of letin         (** a binding of an expr *)
  | Not_a_form

(** {1 Data structures} *)

module Set : Set.S with type elt = t
(** Set of expressions using the function {!val:compare} as
    comparison function. *)

module Map : Map.S with type key = t
(** Map whose the keys are expressions ordering by the function
    {!val:compare}. *)

(** {1 Smart constructors} *)

val mk_binders : Set.t -> binders

val mk_ite : t -> t -> t -> int -> t
(** [mk_ite cond th el] produces the expression
    [if cond then th else el]. If the expression [th] and [el] are
    of type {!constructor:Ty.Tbool}, the function produces the formula
    [mk_if cond th el] instead. *)

val mk_let : Symbols.t -> t -> t -> int -> t
(** [mk_let sy exp1 exp2] constructs the expression [let sy = exp1 in exp2].
    Obvious substitution are inlined during the construction. *)

val mk_match : t -> (Typed.pattern * t) list -> t

(** {2 For terms} *)

val mk_term : Symbols.t -> t list -> Ty.t -> t
(** [mk_term sy args ty] creates a term whose the top symbol is
    [sy], the arguments are [args] and its type is [ty]. *)

val pred : t -> t
(** [pred t] produces the expression [t-1].  *)

(** {3 Literal expressions} *)

val void : t
(** The unit expression. *)

val int : string -> t
(** [int str] produces the integer literal corresponding to
    the string representaiton [str]. *)

val real : string -> t
(** [real str] produces the real literal corresponding to
    the string representation [str]. *)

val bitv : string -> Ty.t -> t
(** [bitv str] produces the bitvector literal corresponding to
    the string representaiton [str]. *)

val fresh_name : Ty.t -> t

(** {2 For literals} *)

val mk_eq : iff:bool -> t -> t -> t
(** [mk_eq iff tm1 tm2] produces an equivalent formula to
    the formula [tm1 = tm2]. *)

val mk_distinct : iff:bool -> t list -> t
val mk_builtin : is_pos:bool -> Symbols.builtin -> t list -> t

(** {2 For formulas} *)

(* TODO: Rename the function top. *)
val vrai : t
(** The formula top. *)

(* TODO: Rename the function bottom. *)
val faux : t
(** The formula bottom. *)

val mk_or  : t -> t -> bool -> int -> t
(** [mk_or f1 f2] produces a formula equivalent to the {e disjunction} of the
    formula [f1] and [f2], that is {m f1 \lor f2}. *)

val mk_and : t -> t -> bool -> int -> t
(** [mk_and f1 f2] produces a formula equivalent to the {e conjunction} of
    the formula [f1] and [f2], that is {m f1 \land f2}. *)

val mk_imp : t -> t -> int -> t
(** [mk_imp f1 f2] produces a formula equivalent to {m f1 \implies f2}. *)

val mk_iff : t -> t -> int -> t
(** [mk_iff f1 f2] produces a formula equivalent to {m f1 \iff f2}. *)

val mk_if : t -> t -> t -> int -> t
(** [mk_if f1 f2] produces a formula equivalent to {m f1 \vee f2}. *)

val mk_xor : t -> t -> int -> t
(** [mk_xor f1 f2] produces a formula equivalent to the {e exclusive
    disjunction} of the formula [f1] and [f2], that is {m f1 \oplus f2}. *)

(** different views of an expression *)

val term_view : t -> term_view
val lit_view  : t -> lit_view
val form_view : t -> form_view

(** {1 Iterators on subterms} *)

val sub_terms : Set.t -> t -> Set.t
(** [sub_term acc exp] returns the accumulator [acc] augmented
    with the term [exp] and all its sub-terms.
    Return the [acc] if [exp] is not a term. Does not go
    through literals (except positive uninterpreted predicates
    application) and formulas *)

val max_pure_subterms : t -> Set.t
(** [max_pure_subterms exp] returns the set of maximal pure terms of
    the expression [exp]. *)

val max_terms_of_lit : t -> Set.t
(** [max_terms_of_lit lit] returns the maximal terms of the
    literal [lit]. Assertion failure if [lit] is not a literal. *)

val max_ground_terms_of_lit : t -> Set.t
(** [max_ground_terms_of_lit lit] returns the maximal ground terms of the
    given literal [lit]. Raise an assertion if [lit] is not a literal. *)

val atoms_rec_of_form : only_ground:bool -> t -> Set.t -> Set.t
(** [atoms_rec_of_form only_ground f acc] traverses a formula recursively
    and collects its atoms. Only ground atoms are kept
    if ~only_ground is true. *)

val max_ground_terms_rec_of_form : t -> Set.t
(** [max_ground_terms_rec_of_form f] traverses a formula recursively
    and collects its maximal ground terms. *)

(** {1 Comparison and test functions} *)

val compare : t -> t -> int
(** [compare exp1 exp2] compares two expresisons [exp1] and [exp2]. More
    precisely, if {m <} denotes the total order defined by [compare], we have
    {math exp1 < exp2 \iff (depth exp1, hash exp1)
    \prec (depth exp2, hash exp2)}
    where {m \prec} is the lexicographic order. *)

val equal : t -> t -> bool
(** [equal exp1 exp2] is [true] if and only if the expressions
    [exp1] and [exp2] are physically equal. *)

val hash  : t -> int
(** [hash exp] returns the hash of the expression [exp] used by the hconsing
    module. *)

val uid   : t -> int
val compare_subst : subst -> subst -> int
(** [compare_subst sub1 sub2] compares two substitutions [sub1] and [sub2]
    using the lexicographic order on . *)

val equal_subst : subst -> subst -> bool
val compare_quant : quantified -> quantified -> int
val compare_let : letin -> letin -> int

val is_fresh : t -> bool
val is_fresh_skolem : t -> bool

val is_int : t -> bool
(** [is_int exp] is true if and only if the expression [exp]
    is of type [Ty.Tint]. *)

val is_real : t -> bool
(** [is_real exp] is true if and only if the expression [exp]
    is of type [Ty.Treal]. *)

val is_positive : t -> bool
val is_in_model : t -> bool

val is_pure : t -> bool

val is_ground : t -> bool
(** [is_ground exp] is [true] if and only if the expression [exp] is ground,
    that is if [exp] does not contain free variable or free type variable. *)

(* TODO: Rename this function to is_const_term *)
val const_term : t -> bool
(** [const_term tm] returns true if and only if the expression
    [tm] is a term without arguments. *)

(** {1 Labeling and models} *)

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val name_of_lemma : t -> string
val name_of_lemma_opt : t option -> string
val print_tagged_classes : Format.formatter -> Set.t list -> unit

(** {1 Substitutions} *)

val apply_subst : subst -> t -> t
val apply_subst_trigger : subst -> trigger -> trigger

(** skolemization and other smart constructors for formulas **)

val make_triggers:
  t -> binders -> decl_kind -> Util.matching_env -> trigger list

val resolution_triggers: is_back:bool -> quantified -> trigger list

val mk_forall :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  toplevel:bool -> (* for future triggers computation in presence of vty *)
  decl_kind:decl_kind ->
  t

val mk_exists :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  toplevel:bool -> (* for future triggers computation in presence of
                      vty, and to construct a toplevel forall that
                      cover vtys *)
  decl_kind:decl_kind ->
  t

val skolemize : quantified -> t

val elim_let : recursive:bool -> letin -> t

val elim_iff : t -> t -> int -> with_conj:bool -> t
(** [elim_iff f1 f2 with_conj] constructs an equivalent formula
    to {m f1 \iff f2} using a combinaison of negations, disjunctions
    and conjuctions instead of the built-in symbol {!constructor:Sy.F_Iff}.
    If [with_conj] is [false], the construction doesn't use conjuction. *)

(*val purify_literal : t -> t*)
val purify_form : t -> t

type gformula = {
  ff: t;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: t option;
  origin_name : string;
  from_terms : t list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

type th_elt =
  {
    th_name : string;
    ax_name : string;
    ax_form : t;
    extends : Util.theories_extensions;
    axiom_kind : Util.axiom_kind;
  }

val print_th_elt : Format.formatter -> th_elt -> unit

(** {1 Misc} *)

val type_info : t -> Ty.t
(** [type_info t] returns the type of the expression [t]. *)

val print : Format.formatter -> t -> unit
(** [print fmt exp] pretty prints the expression [exp] with
    the printer [fmt]. *)

val print_triggers : Format.formatter -> trigger list -> unit
(** [print_triggers fmt lst] pretty prints the list of triggers [lst] with
    the printer [fmt]. *)

(* TODO: Move these functions. *)
val print_list : Format.formatter -> t list -> unit
val print_list_sep : string -> Format.formatter -> t list -> unit


val free_vars : t -> (Ty.t * int) Symbols.Map.t -> (Ty.t * int) Symbols.Map.t
val free_type_vars : t -> Ty.Svty.t
(** [free_type_vars exp] returns the set of the free type variables
    occuring in the expression [exp]. *)

val id : t -> int
val size : t -> int
(** [size exp] returns the size of the expression [exp]. *)

val depth : t -> int
(** [depth exp] returns the depth of the expression [exp]. *)

val neg : t -> t
(** [neg exp] returns the negative form of an expression [exp] of type
    {!constructor:Ty.Tbool}.
    Raise an assertion if [exp] is not of type {!constructor:Ty.Tbool}. *)


