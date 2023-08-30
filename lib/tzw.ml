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
  | PTtuple ptys ->
      let* sl = List.map_e sort_of_pty ptys in
      return @@ Sort.S_tuple sl
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
  epp_param : Ptree.param list;
  epp_old_s : Ptree.param;
  epp_new_s : Ptree.param;
  epp_ops : Ptree.param;
}

type entrypoint = {
  ep_name : Ptree.ident;
  ep_params : entrypoint_params;
  ep_body : Ptree.term;
}

let parse_entrypoint_params (params : Ptree.param list) =
  let param_loc (l, _, _, _) = l in
  let param_pty (_, _, _, pty) = pty in
  let* st, params =
    match params with
    | x :: xs -> return (x, xs)
    | _ -> error_with "invalid format: parameters"
  in
  let* s, s', op, params =
    let rec aux params = function
      | [ s; op; s' ] -> return (s, s', op, List.rev params)
      | x :: (_ :: _ :: _ :: _ as xs) -> aux (x :: params) xs
      | _ -> error_with "invalid format: parameters"
    in
    aux [] params
  in
  let* () =
    error_unless
      (is_step_type @@ param_pty st)
      ~err:
        (error_of_fmt ~loc:(param_loc st)
           "invalid format: step type is expected")
  in
  let* () =
    error_unless
      (is_storage_type @@ param_pty s)
      ~err:
        (error_of_fmt ~loc:(param_loc s)
           "invalid format: storage type is expected")
  in
  let* () =
    error_unless
      (is_storage_type @@ param_pty s')
      ~err:
        (error_of_fmt ~loc:(param_loc s')
           "invalid format: storage type is expected")
  in
  let* op_ty =
    trace
      ~err:
        (error_of_fmt ~loc:(param_loc op)
           "invalid format: list operation type is expected")
    @@ sort_of_pty @@ param_pty op
  in
  let* () =
    error_unless
      (op_ty = Sort.(S_list S_operation))
      ~err:
        (error_of_fmt ~loc:(param_loc op)
           "invalid format: list operation type is expected")
  in
  let* () =
    List.fold_left_e
      (fun () p ->
        let* _ =
          trace
            ~err:
              (error_of_fmt ~loc:(param_loc p)
                 "invalid format: Michelson type is expected")
          @@ sort_of_pty @@ param_pty p
        in
        return ())
      () params
  in
  return
    {
      epp_step = st;
      epp_param = params;
      epp_old_s = s;
      epp_new_s = s';
      epp_ops = op;
    }

let parse_entrypoint_pred (ld : Ptree.logic_decl) : entrypoint iresult =
  let ep_name = ld.ld_ident in
  let* ep_params = parse_entrypoint_params ld.ld_params in
  let* ep_body =
    Option.to_iresult ld.ld_def ~none:(error_of_fmt "spec body is missing")
  in
  return { ep_name; ep_params; ep_body }

let parse_entrypoint_scope (lds : Ptree.decl list) =
  List.fold_left_e
    (fun tl d ->
      match d with
      | Ptree.Dlogic [ ld ] ->
          let* ep = parse_entrypoint_pred ld in
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

let parse_contract loc id ds =
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
            let* eps = parse_entrypoint_scope dls in
            return (ostore, okont, Some eps)
        | _ -> error_with "unexpected decl")
      (None, None, None) ds
  in
  let* c_store_ty =
    Option.to_iresult ostore ~none:(error_of_fmt ~loc "storage is missing")
  in
  let* c_num_kont =
    Option.to_iresult okont ~none:(error_of_fmt ~loc "upper_ops is missing")
  in
  let* c_entrypoints =
    Option.to_iresult oeps ~none:(error_of_fmt ~loc "Spec is missing")
  in
  return { c_name = id; c_store_ty; c_entrypoints; c_num_kont }

let parse_unknown (ds : Ptree.decl list) =
  let parse_entrypoint_type (ds : Ptree.decl list) =
    List.fold_left_e
      (fun m -> function
        | Dlogic [ ld ] ->
            let* s =
              List.map_e
                (fun (loc, _, _, pty) ->
                  trace ~err:(error_of_fmt ~loc "Michelson type is expected")
                  @@ sort_of_pty pty)
                ld.ld_params
            in
            return @@ StringMap.add ld.ld_ident.id_str s m
        | _ -> error_with "invalid format: predicate declaration is expected")
      StringMap.empty ds
  in
  let* oep =
    List.fold_left_e
      (fun oep -> function
        | Dscope (_, _, id, ds) when id.id_str = "Entrypoint" ->
            let* () =
              error_unless (oep = None)
                ~err:(error_of_fmt "multiple declaration of Entrypoint")
            in
            let* ep = parse_entrypoint_type ds in
            return (Some ep)
        | _ -> error_with "invalid format: unexpected declaration")
      None ds
  in
  return @@ Option.value oep ~default:StringMap.empty

let parse_mlw (mlw : Ptree.mlw_file) =
  let* scopes =
    match mlw with
    | Decls ds ->
        List.fold_left_e
          (fun m -> function
            | Dscope (loc, _, id, ds) ->
                if StringMap.exists (fun k _ -> k = id.id_str) m then
                  error_with ~loc "%s has been declared" id.id_str
                else return @@ StringMap.add id.id_str (loc, id, ds) m
            | _ -> error_with "invalid format: top level must consist of scopes")
          StringMap.empty ds
    | _ -> error_with "invalid format: top level must consist of scopes"
  in
  let* _loc, _id, ds =
    StringMap.find_opt "Unknown" scopes
    |> Option.to_iresult ~none:(error_of_fmt "Unknown scope must be declared")
  in
  let* ep = parse_unknown ds in
  let scopes = StringMap.remove "Unknown" scopes in
  let* cs, epp =
    StringMap.fold_e
      (fun name (loc, id, ds) (cs, eps) ->
        let* c = parse_contract loc id ds in
        let* epp =
          List.fold_left_e
            (fun m ep ->
              let* s =
                List.map_e
                  (fun (_, _, _, pty) -> sort_of_pty pty)
                  ep.ep_params.epp_param
              in
              return @@ StringMap.add ep.ep_name.id_str s m)
            StringMap.empty c.c_entrypoints
        in
        return @@ (c :: cs, StringMap.add name epp eps))
      scopes
      ([], StringMap.singleton "Unknown" ep)
  in
  return (cs, epp)

let gen_gparam_cstr (ep : string) (s : Sort.t list) =
  let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')'; char ',' ]) in
  List.map
    (fun s ->
      Sort.string_of_sort s |> String.capitalize_ascii
      |> Regexp.replace re ~f:(fun g ->
             match Regexp.Group.get g 0 with
             | " " -> "_"
             | "(" -> "'0"
             | ")" -> "'1"
             | "," -> "'2"
             | _ -> assert false))
    s
  |> String.concat "'3"
  |> Format.sprintf "Gp'0%s'0%s" ep

let convert_gparam (epp : Sort.t list StringMap.t StringMap.t) (t : Ptree.term)
    : Ptree.term iresult =
  let convert id =
    match String.split_on_char '\'' id.Ptree.id_str with
    | "Gp" :: cn_n :: ep_ns ->
        let ep_n = String.concat "'" ep_ns in
        let cn =
          try StringMap.find cn_n epp
          with Not_found ->
            failwith (Format.sprintf "%s is not declared" cn_n)
        in
        let s =
          try StringMap.find ep_n cn
          with Not_found ->
            failwith (Format.sprintf "%s doesn't have %s" cn_n ep_n)
        in
        { id with id_str = gen_gparam_cstr ep_n s }
    | _ -> id
  in
  let open Ptree_mapper in
  try return @@ apply_term t { default_mapper with ident = convert }
  with Failure s -> error_with "%s" s

let convert_entrypoint (epp : Sort.t list StringMap.t StringMap.t)
    (ep : entrypoint) =
  let* body = convert_gparam epp ep.ep_body in
  return
    {
      ld_loc = Loc.dummy_position;
      ld_ident = ep.ep_name;
      ld_params =
        ep.ep_params.epp_step :: ep.ep_params.epp_old_s :: ep.ep_params.epp_ops
        :: ep.ep_params.epp_new_s :: ep.ep_params.epp_param;
      ld_type = None;
      ld_def = Some body;
    }

let gen_spec (epp : Sort.t list StringMap.t) =
  let st : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "st"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "step" ], []) )
  in
  let gp : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "gp"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "gparam" ], []) )
  in
  let s : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "s"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "storage" ], []) )
  in
  let op : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "op"),
      false,
      Gen_mlw.pty_of_sort Sort.(S_list S_operation) )
  in
  let s' : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "s'"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "storage" ], []) )
  in
  let args =
    Ptree_helpers.
      [
        tvar @@ qualid [ "st" ];
        tvar @@ qualid [ "s" ];
        tvar @@ qualid [ "op" ];
        tvar @@ qualid [ "s'" ];
      ]
  in
  let cls =
    StringMap.fold
      (fun en s cls ->
        let params =
          List.mapi
            (fun i _ ->
              Ptree_helpers.(pat_var @@ ident @@ Format.sprintf "p%d" i))
            s
        in
        let args =
          args
          @ List.mapi
              (fun i _ ->
                Ptree_helpers.(tvar @@ qualid [ Format.sprintf "p%d" i ]))
              s
        in
        Ptree_helpers.
          ( pat @@ Papp (qualid [ gen_gparam_cstr en s ], params),
            tapp (qualid [ "Spec"; en ]) args )
        :: cls)
      epp
      [ Ptree_helpers.(pat Pwild, term Tfalse) ]
  in
  let body =
    Ptree_helpers.term @@ Tcase (Ptree_helpers.(tvar (qualid [ "gp" ])), cls)
  in
  let ld_loc = Loc.dummy_position in
  let ld_ident = Ptree_helpers.ident "spec" in
  let ld_params = [ st; gp; s; op; s' ] in
  let ld_type = None in
  let ld_def = Some body in
  { ld_loc; ld_ident; ld_params; ld_type; ld_def }

let convert_contract (epp : Sort.t list StringMap.t StringMap.t) (c : contract)
    =
  let* eps =
    List.fold_left_e
      (fun tl ep ->
        let* ep = convert_entrypoint epp ep in
        return @@ (Dlogic [ ep ] :: tl))
      [] c.c_entrypoints
  in
  return
  @@ Dscope
       ( Loc.dummy_position,
         false,
         c.c_name,
         [
           Dlogic
             [
               {
                 ld_loc = Loc.dummy_position;
                 ld_ident = Ptree_helpers.ident "addr";
                 ld_params = [];
                 ld_type = Some (Gen_mlw.pty_of_sort Sort.S_address);
                 ld_def = None;
               };
             ];
           Dtype [ c.c_store_ty ];
           Dscope (Loc.dummy_position, false, Ptree_helpers.ident "Spec", eps);
           Dlogic [ gen_spec (StringMap.find c.c_name.id_str epp) ];
         ] )

let gen_gparam (epp : Sort.t list StringMap.t StringMap.t) =
  let module S = Set.Make (struct
    type t = Loc.position * ident * param list

    let compare = compare
  end) in
  let td_def =
    TDalgebraic
      (S.elements
      @@ StringMap.fold
           (fun _ ->
             StringMap.fold (fun en s cstrs ->
                 S.add
                   ( Loc.dummy_position,
                     Ptree_helpers.ident @@ gen_gparam_cstr en s,
                     List.map
                       (fun s ->
                         (Loc.dummy_position, None, false, Gen_mlw.pty_of_sort s))
                       s )
                   cstrs))
           epp S.empty)
  in
  Dtype
    [
      {
        td_loc = Loc.dummy_position;
        td_ident = Ptree_helpers.ident "gparam";
        td_params = [];
        td_vis = Public;
        td_mut = false;
        td_inv = [];
        td_wit = None;
        td_def;
      };
    ]

let convert_mlw (epp : Sort.t list StringMap.t StringMap.t) (cs : contract list)
    =
  let* ds = List.map_e (convert_contract epp) cs in
  return @@ Decls (gen_gparam epp :: ds)

let from_file s =
  let f = Lexer.parse_mlw_file @@ Lexing.from_channel @@ open_in s in
  let r =
    let* cs, epp = parse_mlw f in
    convert_mlw epp cs
  in
  raise_error r
