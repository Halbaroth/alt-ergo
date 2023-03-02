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

let apply f l =
  let res, same =
    List.fold_left
      (fun (acc, same) a ->
         let b = f a in
         b :: acc, same && a == b
      )([], true) l
  in
  (if same then l else List.rev res), same

let apply_right f l =
  let res, same =
    List.fold_left
      (fun (acc, same) (v, a) ->
         let b = f a in
         (v, b) :: acc, same && a == b
      )([], true) l
  in
  (if same then l else List.rev res), same

let rec find_opt pred l =
  match l with
  | [] -> None
  | e :: r ->
    if pred e then Some e
    else find_opt pred r

let to_seq l =
  let rec aux l () = match l with
    | [] -> Seq.Nil
    | x :: tail -> Seq.Cons (x, aux tail)
  in
  aux l

let[@inline always] rec compare ~cmp l1 l2 =
  match l1, l2 with
  | [], []     -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | hd1 :: tl1, hd2 :: tl2 ->
    let res = cmp hd1 hd2 in
    if res <> 0 then res
    else compare ~cmp tl1 tl2

let[@inline always] rec equal ~eq l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | [], _ :: _ | _ :: _, [] -> false
  | hd1 :: tl1, hd2 :: tl2 ->
    eq hd1 hd2 && equal ~eq tl1 tl2


