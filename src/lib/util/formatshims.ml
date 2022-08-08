(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(*     Some parts of this file are exctracted from the                        *)
(*     projectOcaml-containers :                                              *)
(* https://github.com/c-cube/ocaml-containers/blob/master/src/core/mkshims.ml *)
(*     Thanks to Simon Cruanes                                                *)
(*                                                                            *)
(******************************************************************************)

module C = Configurator.V1

let write_file f s =
  let out = open_out f in
  output_string out s;
  flush out;
  close_out out

let shims_fmt_pre_408 =
  "\n\
   include Format\n\n\
   let pp_open_stag = pp_open_tag\n\
   let open_stag = open_tag\n\
   let pp_close_stag = pp_close_tag\n\
   let close_stag = close_tag\n\n\
   type formatter_stag_functions = formatter_tag_functions\n\n\
   let pp_get_formatter_stag_functions = pp_get_formatter_tag_functions\n\
   let get_formatter_stag_functions = get_formatter_tag_functions\n\
   let pp_set_formatter_stag_functions = pp_set_formatter_tag_functions\n\
   let set_formatter_stag_functions = set_formatter_tag_functions\n\n\
   let get_stag s = s\n\n\
   let update_stag_functions funs start_stag stop_stag =\n\
  \  let open Format in\n\
  \  { funs with\n\
  \    mark_open_tag = start_stag;\n\
  \    mark_close_tag = stop_stag }\n\n"

let shims_fmt_post_408 =
  "\n\
   include Format\n\n\
   let get_stag = function\n\
  \  | String_tag s -> s\n\
  \  | _ -> raise Not_found\n\n\
   let update_stag_functions funs start_stag stop_stag =\n\
  \  let open Format in\n\
  \  { funs with\n\
  \    mark_open_stag = start_stag;\n\
  \    mark_close_stag = stop_stag }\n"

let () =
  C.main ~name:"mkshims" (fun c ->
      let version = C.ocaml_config_var_exn c "version" in
      let major, minor =
        Scanf.sscanf version "%u.%u" (fun maj min -> (maj, min))
      in
      write_file "format_shims.ml"
        (if (major, minor) >= (4, 8) then shims_fmt_post_408
         else shims_fmt_pre_408))
