module Regexp = Re
open Why3
open Ptree
open Error_monad

let rec sort_of_pty (pty : pty) : Sort.t iresult =
  let elt1 l =
    match l with
    | [ pty ] -> sort_of_pty pty
    | _ -> error_with "expected 1 parameter"
  in
  let elt2 l =
    match l with
    | [ pty1; pty2 ] ->
        let* s1 = sort_of_pty pty1 in
        let* s2 = sort_of_pty pty2 in
        return (s1, s2)
    | _ -> error_with "expected 2 parameter"
  in
  match pty with
  | PTtyapp (Qident id, pl) -> (
      match id.id_str with
      | "string" -> return Sort.S_string
      | "nat" -> return Sort.S_nat
      | "int" -> return Sort.S_int
      | "bytes" -> return Sort.S_bytes
      | "bool" -> return Sort.S_bool
      | "unit" -> return Sort.S_unit
      | "timestamp" -> return Sort.S_timestamp
      | "mutez" -> return Sort.S_mutez
      | "address" -> return Sort.S_address
      | "key" -> return Sort.S_key
      | "key_hash" -> return Sort.S_key_hash
      | "signature" -> return Sort.S_signature
      | "chain_id" -> return Sort.S_chain_id
      | "operation" -> return Sort.S_operation
      | "list" ->
          let* s = elt1 pl in
          return @@ Sort.S_list s
      | "option" ->
          let* s = elt1 pl in
          return @@ Sort.S_option s
      | "or" ->
          let* s1, s2 = elt2 pl in
          return @@ Sort.S_or (s1, s2)
      | "set" ->
          let* s = elt1 pl in
          return @@ Sort.S_set s
      | "map" ->
          let* s1, s2 = elt2 pl in
          return @@ Sort.S_map (s1, s2)
      | "big_map" ->
          let* s1, s2 = elt2 pl in
          return @@ Sort.S_big_map (s1, s2)
      | "lambda" ->
          let* s1, s2 = elt2 pl in
          return @@ Sort.S_lambda (s1, s2)
      | "contract" ->
          let* s = elt1 pl in
          return @@ Sort.S_contract s
      | s -> error_with "unknown sort %s" s)
  | PTtuple [] -> return @@ Sort.S_unit
  | PTtuple [ pty ] -> sort_of_pty pty
  | PTtuple ([ _; _ ] as pl) ->
      let* s1, s2 = elt2 pl in
      return @@ Sort.S_pair (s1, s2)
  | PTtuple (pty :: tl) ->
      let* s = sort_of_pty pty in
      let* tl = sort_of_pty @@ PTtuple tl in
      return @@ Sort.S_pair (s, tl)
  | PTparen pty -> sort_of_pty pty
  | _ -> error_with "unknown sort %a" (Mlw_printer.pp_pty ~attr:true).closed pty

let is_id_type (pty : Ptree.pty) (id : string) : bool =
  match pty with
  | PTtyapp (Qident { id_str; _ }, []) when id_str = id -> true
  | _ -> false

let is_step_type (pty : Ptree.pty) : bool = is_id_type pty "step"
let is_storage_type (pty : Ptree.pty) : bool = is_id_type pty "storage"

type entrypoint_params = {
  epp_step : Ptree.param;
  epp_param : Ptree.param;
  epp_old_s : Ptree.param;
  epp_new_s : Ptree.param;
  epp_ops : Ptree.param;
}

type entrypoint = {
  ep_name : Ptree.ident;
  ep_params : entrypoint_params;
  ep_body : Ptree.term;
}

let parse_entrypoint (ld : Ptree.logic_decl) =
  let ep_name = ld.ld_ident in
  let* ep_params =
    match ld.ld_params with
    | [
     ((st_l, _, false, st_ty) as epp_step);
     ((p_l, _, false, p_ty) as epp_param);
     ((_, _, false, s_ty) as epp_old_s);
     ((op_l, _, false, op_ty) as epp_ops);
     ((_, _, false, s'_ty) as epp_new_s);
    ] ->
        let* () =
          error_unless (is_step_type st_ty)
            ~err:(error_of_fmt ~loc:st_l "step expected")
        in
        let* _ =
          trace ~err:(error_of_fmt ~loc:p_l "check param type")
          @@ sort_of_pty p_ty
        in
        let* () =
          error_unless (is_storage_type s_ty)
            ~err:(error_of_fmt "storage expected")
        in
        let* op_ty =
          trace ~err:(error_of_fmt ~loc:op_l "check ops type")
          @@ sort_of_pty op_ty
        in
        let* () =
          error_unless
            (op_ty = Sort.(S_list S_operation))
            ~err:(error_of_fmt "list operation expected")
        in
        let* () =
          error_unless (is_storage_type s'_ty)
            ~err:(error_of_fmt "storage expected")
        in
        return { epp_step; epp_param; epp_old_s; epp_ops; epp_new_s }
    | _ -> error_with "parameters do not follow the convention"
  in
  let* ep_body =
    Option.to_iresult ld.ld_def ~none:(error_of_fmt "spec body is missing")
  in
  return { ep_name; ep_params; ep_body }

let parse_entrypoint_spec (lds : Ptree.decl list) =
  List.fold_left_e
    (fun tl d ->
      match d with
      | Ptree.Dlogic [ ld ] ->
          let* ep = parse_entrypoint ld in
          return @@ (ep :: tl)
      | _ -> error_with "unexpected decl in Spec scope")
    [] lds

type contract = {
  c_name : Ptree.ident;
  c_store_ty : Ptree.type_decl;
  c_entrypoints : entrypoint list;
  c_num_kont : int;
}

let parse_storage_type (td : Ptree.type_decl) =
  let* () =
    error_unless (td.td_params = [])
      ~err:(error_of_fmt "storage type cannot have type parameters")
  in
  let* () =
    error_unless (td.td_vis = Ptree.Public) ~err:(error_of_fmt "public")
  in
  let* () = error_unless (td.td_mut = false) ~err:(error_of_fmt "immutable") in
  let* () = error_unless (td.td_inv = []) ~err:(error_of_fmt "pure record") in
  let* () = error_unless (td.td_wit = None) ~err:(error_of_fmt "pure record") in
  match td.td_def with
  | TDalias pty ->
      let* _ =
        trace ~err:(error_of_fmt ~loc:td.td_loc "alias") @@ sort_of_pty pty
      in
      return td
  | TDrecord _ -> return td
  | _ ->
      error_with
        "storage type must be a Michelson type or a record type of which \
         fields' type is a Michelson type"

let parse_upper_ops (e : Ptree.expr) =
  match e.expr_desc with
  | Econst (ConstInt i) -> (
      try return @@ BigInt.to_int i.il_int
      with Failure _ ->
        error_with "upper bound length of operation lists is too large")
  | _ -> error_with "upper_ops_len shall be an integer constant"

let parse_contract (d : Ptree.decl) =
  let* c_name, decls =
    match d with
    | Dscope (_, false, c_id, decls) -> return (c_id, decls)
    | _ -> error_with "scope is expected"
  in
  let* ostore, okont, oeps =
    List.fold_left_e
      (fun (ostore, okont, oeps) -> function
        | Ptree.Dtype [ td ] when td.td_ident.id_str = "storage" ->
            let* () =
              error_unless (ostore = None)
                ~err:(error_of_fmt "multiple declaration of storage type")
            in
            let* store = parse_storage_type td in
            return (Some store, okont, oeps)
        | Dlet (id, _, _, e) when id.id_str = "upper_ops" ->
            let* () =
              error_unless (okont = None)
                ~err:(error_of_fmt "multiple declaration of upper_ops")
            in
            let* kont = parse_upper_ops e in
            return (ostore, Some kont, oeps)
        | Dscope (_, _, id, dls) when id.id_str = "Spec" ->
            let* () =
              error_unless (oeps = None)
                ~err:(error_of_fmt "multiple declaration of Spec")
            in
            let* eps = parse_entrypoint_spec dls in
            return (ostore, okont, Some eps)
        | _ -> error_with "unexpected decl")
      (None, None, None) decls
  in
  let* c_store_ty =
    Option.to_iresult ostore ~none:(error_of_fmt "storage is missing")
  in
  let* c_num_kont =
    Option.to_iresult okont ~none:(error_of_fmt "upper_ops is missing")
  in
  let* c_entrypoints =
    Option.to_iresult oeps ~none:(error_of_fmt "Spec is missing")
  in
  return { c_name; c_store_ty; c_entrypoints; c_num_kont }

let parse_mlw (mlw : Ptree.mlw_file) : contract list iresult =
  match mlw with
  | Decls dls ->
      List.fold_left_e
        (fun tl d ->
          let* c = parse_contract d in
          return @@ (c :: tl))
        [] dls
  | _ -> error_with "tzw only consists of scopes"

let convert_gparam (cns : contract list) (t : Ptree.term) : Ptree.term iresult =
  let lident_of_sort pty =
    let s = match sort_of_pty pty with Ok s -> s | Error _ -> assert false in
    let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')' ]) in
    Sort.string_of_sort s |> String.capitalize_ascii
    |> Regexp.replace re ~f:(fun g ->
           match Regexp.Group.get g 0 with
           | " " -> "_"
           | "(" -> "'0"
           | ")" -> "'1"
           | _ -> assert false)
  in
  let convert id =
    match String.split_on_char '\'' id.Ptree.id_str with
    | "Gp" :: cn_n :: ep_ns ->
        let ep_n = String.concat "'" ep_ns in
        let _, _, _, pty =
          let cn =
            try List.find (fun cn -> cn.c_name.id_str = cn_n) cns
            with Not_found ->
              failwith (Format.sprintf "%s is not declared" cn_n)
          in
          let ep =
            try List.find (fun ep -> ep.ep_name.id_str = ep_n) cn.c_entrypoints
            with Not_found ->
              failwith (Format.sprintf "%s doesn't have %s" cn_n ep_n)
          in
          ep.ep_params.epp_param
        in
        { id with id_str = Format.sprintf "Gp'%s'%s" ep_n (lident_of_sort pty) }
    | _ -> id
  in
  let open Ptree_mapper in
  try return @@ apply_term t { default_mapper with ident = convert }
  with Failure s -> error_with "%s" s

let convert_entrypoint (cns : contract list) (ep : entrypoint) =
  let* body = convert_gparam cns ep.ep_body in
  return
    {
      ld_loc = Loc.dummy_position;
      ld_ident = ep.ep_name;
      ld_params =
        [
          ep.ep_params.epp_step;
          ep.ep_params.epp_param;
          ep.ep_params.epp_old_s;
          ep.ep_params.epp_ops;
          ep.ep_params.epp_new_s;
        ];
      ld_type = None;
      ld_def = Some body;
    }

let convert_contract (cns : contract list) (c : contract) =
  let* eps =
    List.fold_left_e
      (fun tl ep ->
        let* ep = convert_entrypoint cns ep in
        return @@ (Dlogic [ ep ] :: tl))
      [] c.c_entrypoints
  in
  return
  @@ Dscope
       ( Loc.dummy_position,
         false,
         c.c_name,
         [
           Dtype [ c.c_store_ty ];
           Dscope (Loc.dummy_position, false, Ptree_helpers.ident "Spec", eps);
         ] )

let convert_mlw (cs : contract list) =
  let* ds = List.map_e (convert_contract cs) cs in
  return @@ Decls ds

let from_file s =
  let f = Lexer.parse_mlw_file @@ Lexing.from_channel @@ open_in s in
  let r =
    let* cs = parse_mlw f in
    convert_mlw cs
  in
  raise_error r
