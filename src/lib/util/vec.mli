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

type 'a t
(** Type of vector. *)

(** {1 Constructors} *)

val make : cap:int -> dummy:'a -> 'a t
(** [make cap dummy] creates a new vector filled with value [dummy] and
    capacity [cap]. *)

val init : size:int -> dummy:'a -> 'a t

val create : unit -> 'a t
(** [create ()] creates an empty vector with null capacity. *)

val of_list : 'a list -> 'a t
(** [of_list lst] produces a vector from the list [lst]. The capacity
    of this vector is equal to the length of [lst]. *)

val clear : 'a t -> unit
(** [clear vec] set the size of the vector [vec] to 0 but doesn't free its
    elements. *)

val size : 'a t -> int
(** [size vec] returns the size of the vector [vec]. *)

val push : 'a t -> 'a -> unit
(** [push vec el] pushes the element [el] at the end of vector [vec]. *)

val pop : 'a t -> 'a
(** [pop vec] returns and removes the last element of the vector [vec]. *)

val get : 'a t -> int -> 'a
(** [get vec i] gets the element of index [i] in the vector [vec].
    @raise Invalid_argument if [i] doesn't satisfy 0 <= [i] <=
    [(size vec) - 1]. *)

val set : 'a t -> int -> 'a -> unit
(** [set vec i el] sets the element [el] at the index [i].
    @raise Invalid_argument if [i] doesn't satisfy 0 <= [i] <=
    [(size vec) - 1]. *)

val last : 'a t -> 'a
(** [last vec] returns the last element of [vec] without removing it. *)

val shrink : 'a t -> int -> unit
(** [shrink vec i] substracts [i] to the size of the vector [vec].
    Assumes that 0 <= i <= [size vec]. *)

val copy : 'a t -> 'a t
(** [copy vec] produces a fresh copy of the vector [vec]. *)

val fast_remove : 'a t -> 'a -> equal:('a -> 'a -> bool) -> unit
(** [remove vec ~equal el] remoes the first occurence of [el] in the vector
    [vec]. The value is found using the function [equal].
    This function does not preserve the order of elements.
    @raise Not_found if the element [el] is not present. *)

(** {1 Tests} *)

val is_empty : 'a t -> bool
(** [is_empty vec] checks if the vector [vec] is empty. *)

val is_full : 'a t -> bool
(** [is_full vec] checks if the vector [vec] is full, that is its capacity and
    size are equal. *)

(** {1 Iterators} *)

val iter : 'a t -> f:('a -> unit) -> unit
(** [iter vec ~f] iterates the function [f] on the elements of the vector
    [vec]. *)

(** {1 Misc} *)
val sort : 'a t -> cmp:('a -> 'a -> int) -> unit
(** [sort vec ~cmp] sorts the elements of [vec] with the comparison function
    [cmp]. *)

val grow_to_double_size : 'a t -> dummy:'a -> unit

val grow_by_double : 'a t -> dummy:'a -> limit:int -> unit
(** [grow_to_double_size vec] doubles the capacity of the vector [vec].
    The function may raise an exception if there is not enough memory. *)
