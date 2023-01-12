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

type 'a t = { mutable data : 'a array; mutable size : int }

let make ~cap ~dummy = { data = Array.make cap dummy; size = 0 }
let init ~size ~dummy = { data = Array.make size dummy; size }

let[@inline] create () = { data = [||]; size = 0 }

let of_list lst =
  let data = Array.of_list lst in
  { data; size = Array.length data }

let[@inline] clear vec = vec.size <- 0

let[@inline] shrink vec i =
  assert (i >= 0 && i <= vec.size);
  vec.size <- vec.size - i

let[@inline] last { data; size } =
  if size = 0 then (raise (Invalid_argument "Vec.last"));
  Array.unsafe_get data (size - 1)

let[@inline] pop ({ size; _ } as vec) =
  let el = last vec in
  vec.size <- size - 1;
  el

let[@inline] size { size; _ } = size

let[@inline] is_empty { size; _ } = size = 0

let[@inline] is_full { data; size } = Array.length data = size

let[@inline] copy ({ data; _ } as vec) =
  let data = Array.copy data in
  { vec with data }

let grow ({ data; _ } as vec) ~dummy ~new_cap =
  if new_cap = Sys.max_array_length then (failwith "Array cannot growth");
  let new_arr = Array.make new_cap dummy in
  Array.blit data 0 new_arr 0 (Array.length data);
  vec.data <- new_arr

let grow_by_double =
  let closest_power_of_two init n =
    let i = ref init in
    while !i < n do
      i := 2 * !i
    done;
    !i
  in
  fun vec ~dummy ~limit ->
    let limit = max 1 limit in
    let new_cap =
      closest_power_of_two (max 1 (Array.length vec.data)) limit
    in
    if new_cap > Array.length vec.data then
      grow vec ~dummy ~new_cap;
    assert (Array.length vec.data <> 0)

let grow_to_double_size vec ~dummy =
  let new_cap = max 1 (Array.length vec.data) |> fun x -> 2 * x in
  grow vec ~dummy ~new_cap

let[@inline] push ({ data; size } as vec) el =
  if is_full vec then grow_to_double_size vec ~dummy:el;
  Array.unsafe_set data size el;
  vec.size <- size + 1

let[@inline] get { data; size } i =
  if i < 0 || i >= size then (
    raise (Invalid_argument "Vec.get")
  );
  Array.unsafe_get data i

let[@inline] set ({ data; size } as vec) i el =
  if i < 0 || i >= size then (
    raise (Invalid_argument "Vec.set"));
  if i = size then (
    push vec el
  ) else (
    Array.unsafe_set data i el
  )
(*vec.data.(i) <- el;
  vec.size <- max vec.size (i + 1)*)

let find { data; size } ~equal el =
  let exception Break of int in
  try
    for j = 0 to size - 1 do
      if equal (Array.unsafe_get data j) el then
        raise (Break j)
    done;
    raise Not_found
  with Break j -> j

let fast_remove ({ data; size } as vec) el ~equal =
  if size = 0 then (raise (Invalid_argument "Vec.fast_remove"));
  let j = find vec ~equal el in
  let last = Array.unsafe_get data (size - 1) in
  Array.unsafe_set data j last;
  vec.size <- size - 1

let sort ({ data; size } as vec) ~cmp =
  let sub_arr = Array.sub data 0 size in
  Array.fast_sort cmp sub_arr;
  vec.data <- sub_arr

let iter { data; size } ~f =
  for i = 0 to size - 1 do
    f (Array.unsafe_get data i)
  done
