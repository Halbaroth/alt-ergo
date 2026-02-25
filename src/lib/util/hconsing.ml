(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module type HASHED =
sig
  type elt
  val eq : elt -> elt -> bool
  val hash : elt -> int
  val set_id : int -> elt -> elt
  val initial_size : int
  val disable_weaks : unit -> bool
end

module type S =
sig
  type ctx
  val make_ctx : unit -> ctx

  type t
  val save_cache: ctx -> unit
  val reinit_cache: ctx -> unit
  val make : ctx -> t -> t
  val elements : ctx -> t list
end

module Make(Hashed : HASHED) : (S with type t = Hashed.elt) =
struct
  type t = Hashed.elt

  module HWeak = Weak.Make
      (struct
        type t = Hashed.elt
        let equal = Hashed.eq
        let hash = Hashed.hash
      end)

  type ctx = {
    storage : HWeak.t;
    mutable saved_storage : HWeak.t option;
    mutable next_id : int;
    mutable saved_next_id : int;
    mutable retain_list : t list;
    mutable saved_retain_list : t list;
  }

  let make_ctx () = {
    storage = HWeak.create Hashed.initial_size;
    saved_storage = None;
    next_id = 0;
    saved_next_id = 0;
    retain_list = [];
    saved_retain_list = [];
  }

  let make ctx d =
    let d = Hashed.set_id ctx.next_id d in
    let o = HWeak.merge ctx.storage d in
    if o == d then begin
      ctx.next_id <- ctx.next_id + 1;
      if Hashed.disable_weaks() then
        (* retain a pointer to 'd' to prevent the GC from collecting
           the object if H.disable_weaks is set *)
        ctx.retain_list <- d :: ctx.retain_list
    end;
    o

  let elements ctx =
    let acc = ref [] in
    HWeak.iter (fun e -> acc := e :: !acc) ctx.storage;
    !acc

  let save_cache, reinit_cache =
    let save_cache ctx =
      ctx.saved_retain_list <- ctx.retain_list;
      ctx.saved_next_id <- ctx.next_id;
      ctx.saved_storage <- (
        let hw = HWeak.create Hashed.initial_size in
        HWeak.iter (HWeak.add hw) ctx.storage;
        Some hw
      )
    in
    let reinit_cache ctx =
      ctx.next_id <- ctx.saved_next_id;
      ctx.retain_list <- ctx.saved_retain_list;
      HWeak.clear ctx.storage;
      match ctx.saved_storage with
      | Some st -> HWeak.iter (HWeak.add ctx.storage) st
      | None -> ()
    in
    save_cache, reinit_cache
end
