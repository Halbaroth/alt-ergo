(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2024 --- OCamlPro SAS                                *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DE = Dolmen.Std.Expr

(** The purpose of this module is to construct an appropriate total order on
    constructors of a given ADT to ensure the termination of model generation
    for this theory.

    For each ADT type, we generate a minimal perfect hash function
    for its set of constructors, that is a bijection between this set
    on the integer between 0 and [n] exclusive, where [n] denotes the
    number of constructors. The total order on ADT constructors is given by
    the hash function. *)

val generate : DE.ty_def list -> (Uid.t * Uid.hash) list
(** [generate defs] generate minimal perfect hashes for each ADT of [defs].

    {b Note:} assume that [defs] is a list of definitions of a complete nest
    (in any order). By nest, we mean the set of all the constructors in a
    mutually recursive definition of ADTs. *)
