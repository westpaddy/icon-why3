module Regexp = Re
open Why3
open Ptree
open Error_monad

let is_id_type (pty : Ptree.pty) (id : ident) : bool =
  match pty with
  | PTtyapp (Qident { id_str; _ }, []) when id_str = id.id_str -> true
  | _ -> false

let is_step_type (pty : Ptree.pty) : bool = is_id_type pty Id.step_ty
let is_storage_type (pty : Ptree.pty) : bool = is_id_type pty Id.storage_ty

type entrypoint_params = {
  epp_step : Ptree.param;
  epp_param : Ptree.param list;
  epp_old_s : Ptree.param;
  epp_new_s : Ptree.param;
  epp_ops : Ptree.param;
}

type entrypoint = {
  ep_loc : Loc.position;
  ep_name : Ptree.ident;
  ep_params : entrypoint_params;
  ep_body : Ptree.term;
}

type contract = {
  c_name : Ptree.ident;
  c_store_ty : Ptree.type_decl;
  c_entrypoints : entrypoint list;
  c_num_kont : int;
  c_pre : Ptree.logic_decl;
  c_post : Ptree.logic_decl;
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
    @@ Sort.sort_of_pty @@ param_pty op
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
          @@ Sort.sort_of_pty @@ param_pty p
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
  let ep_loc = ld.ld_loc in
  let ep_name = ld.ld_ident in
  let* ep_params = parse_entrypoint_params ld.ld_params in
  let* () =
    error_unless (ld.ld_type = None)
      ~err:(error_of_fmt ~loc:ep_loc "invalid format: predicate is expected")
  in
  let* ep_body =
    Option.to_iresult ld.ld_def
      ~none:(error_of_fmt ~loc:ep_loc "invalid format: spec body is missing")
  in
  return { ep_loc; ep_name; ep_params; ep_body }

let parse_entrypoint_scope (lds : Ptree.decl list) =
  List.fold_left_e
    (fun tl d ->
      match d with
      | Ptree.Dlogic [ ld ] ->
          let* ep = parse_entrypoint_pred ld in
          return @@ (ep :: tl)
      | _ -> error_with "invalid format: unexpected decl in Spec scope")
    [] lds

let check_storage_type_decl (td : Ptree.type_decl) : Ptree.type_decl iresult =
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
        trace ~err:(error_of_fmt ~loc:td.td_loc "Michelson type is expected")
        @@ Sort.sort_of_pty pty
      in
      return td
  | TDrecord flds ->
      let* () =
        List.iter_e
          (fun f ->
            let* _ =
              trace
                ~err:(error_of_fmt ~loc:f.f_loc "Michelson type is expected")
              @@ Sort.sort_of_pty f.f_pty
            in
            return ())
          flds
      in
      return td
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
  let* ostore, okont, oeps, opre, opost =
    List.fold_left_e
      (fun (ostore, okont, oeps, opre, opost) -> function
        | Ptree.Dtype [ td ] when td.td_ident.id_str = Id.storage_ty.id_str ->
            let* () =
              error_unless (ostore = None)
                ~err:(error_of_fmt "multiple declaration of storage type")
            in
            let* store = check_storage_type_decl td in
            return (Some store, okont, oeps, opre, opost)
        | Dlet (id, _, _, e) when id.id_str = Id.upper_ops.id_str ->
            let* () =
              error_unless (okont = None)
                ~err:(error_of_fmt "multiple declaration of upper_ops")
            in
            let* kont = parse_upper_ops e in
            return (ostore, Some kont, oeps, opre, opost)
        | Dscope (loc, _, id, dls) when id.id_str = Id.spec_scope.id_str ->
            let* () =
              error_unless (oeps = None)
                ~err:(error_of_fmt ~loc "multiple declaration of Spec")
            in
            let* eps = parse_entrypoint_scope dls in
            return (ostore, okont, Some eps, opre, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.pre.id_str ->
            let* () =
              error_unless (opre = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (ostore, okont, oeps, Some ld, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.post.id_str ->
            let* () =
              error_unless (opost = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (ostore, okont, oeps, opre, Some ld)
        | _ -> error_with "unexpected decl")
      (None, None, None, None, None)
      ds
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
  let* c_pre =
    Option.to_iresult opre ~none:(error_of_fmt ~loc "pre is missing")
  in
  let* c_post =
    Option.to_iresult opost ~none:(error_of_fmt ~loc "post is missing")
  in
  return { c_name = id; c_store_ty; c_entrypoints; c_num_kont; c_pre; c_post }

let parse_unknown (ds : Ptree.decl list) =
  let parse_entrypoint_type (ds : Ptree.decl list) =
    List.fold_left_e
      (fun m -> function
        | Dlogic [ ld ] ->
            let* s =
              List.map_e
                (fun (loc, _, _, pty) ->
                  trace ~err:(error_of_fmt ~loc "Michelson type is expected")
                  @@ Sort.sort_of_pty pty)
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
  let preambles =
    match StringMap.find_opt Id.preambles_scope.id_str scopes with
    | None -> []
    | Some (_, _, ds) -> ds
  in
  let scopes = StringMap.remove Id.preambles_scope.id_str scopes in
  let postambles =
    match StringMap.find_opt Id.postambles_scope.id_str scopes with
    | None -> []
    | Some (_, _, ds) -> ds
  in
  let scopes = StringMap.remove Id.postambles_scope.id_str scopes in
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
                  (fun (_, _, _, pty) -> Sort.sort_of_pty pty)
                  ep.ep_params.epp_param
              in
              return @@ StringMap.add ep.ep_name.id_str s m)
            StringMap.empty c.c_entrypoints
        in
        return @@ (c :: cs, StringMap.add name epp eps))
      scopes
      ([], StringMap.singleton "Unknown" ep)
  in
  return (preambles, postambles, cs, epp)

(** Generate the global parameter constructor name for entrypoint [ep] of type [s]. *)
let gen_gparam_cstr (ep : string) (s : Sort.t list) : string =
  let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')'; char ',' ]) in
  List.map
    (fun s ->
      Sort.string_of_sort s
      |> Regexp.replace re ~f:(fun g ->
             match Regexp.Group.get g 0 with
             | " " -> "0"
             | "(" -> "1"
             | ")" -> "2"
             | "," -> "3"
             | _ -> assert false))
    s
  |> String.concat "4"
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
            raise
            @@ Loc.Located
                 (id.id_loc, Failure (Format.sprintf "%s is not declared" cn_n))
        in
        let s =
          try StringMap.find ep_n cn
          with Not_found ->
            raise
            @@ Loc.Located
                 ( id.id_loc,
                   Failure (Format.sprintf "%s doesn't have %s" cn_n ep_n) )
        in
        { id with id_str = gen_gparam_cstr ep_n s }
    | _ -> id
  in
  let open Ptree_mapper in
  try return @@ apply_term t { default_mapper with ident = convert }
  with Loc.Located (loc, Failure s) -> error_with ~loc "%s" s

let convert_entrypoint (epp : Sort.t list StringMap.t StringMap.t)
    (ep : entrypoint) =
  let* body = convert_gparam epp ep.ep_body in
  return
    {
      ld_loc = ep.ep_loc;
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
      Sort.pty_of_sort Sort.(S_list S_operation) )
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

let gen_storage_wf td =
  let sto : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "s"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "storage" ], []) )
  in
  let* body =
    match td.td_def with
    | TDalias pty ->
        let* s = Sort.sort_of_pty pty in
        return @@ Gen_mlw.sort_wf s Gen_mlw.(E.mk_var @@ param_id sto)
    | TDrecord flds ->
        List.fold_left_e
          (fun t f ->
            let* s = Sort.sort_of_pty f.f_pty in
            let p =
              Gen_mlw.(
                sort_wf s
                @@ Ptree_helpers.eapp (qid f.f_ident)
                     [ E.mk_var @@ param_id sto ])
            in
            return @@ Gen_mlw.T.mk_and p t)
          (Ptree_helpers.term Ttrue) flds
    | _ -> assert false
  in
  return
    {
      ld_loc = Loc.dummy_position;
      ld_ident = Ptree_helpers.ident "storage_wf";
      ld_params = [ sto ];
      ld_type = None;
      ld_def = Some body;
    }

let convert_contract (epp : Sort.t list StringMap.t StringMap.t) (c : contract)
    =
  let* eps =
    List.fold_left_e
      (fun tl ep ->
        let* ep = convert_entrypoint epp ep in
        return @@ (Dlogic [ ep ] :: tl))
      [] c.c_entrypoints
  in
  let* storage_wf = gen_storage_wf c.c_store_ty in
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
                 ld_type = Some (Sort.pty_of_sort Sort.S_address);
                 ld_def = None;
               };
             ];
           Dtype [ c.c_store_ty ];
           Dlogic [ storage_wf ];
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
                         (Loc.dummy_position, None, false, Sort.pty_of_sort s))
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

let convert_mlw (preambles : decl list) (postambles : decl list)
    (epp : Sort.t list StringMap.t StringMap.t) (cs : contract list) =
  let* ds = List.map_e (convert_contract epp) cs in
  let* invariants =
    let* lds =
      List.map_e
        (fun c ->
          let* pre_def = Option.map_e (convert_gparam epp) c.c_pre.ld_def in
          let* post_def = Option.map_e (convert_gparam epp) c.c_post.ld_def in
          return
            [
              Dlogic
                [
                  {
                    c.c_pre with
                    ld_ident =
                      Ptree_helpers.ident @@ String.uncapitalize_ascii
                      @@ c.c_name.id_str ^ "_pre";
                    ld_def = pre_def;
                  };
                ];
              Dlogic
                [
                  {
                    c.c_post with
                    ld_ident =
                      Ptree_helpers.ident @@ String.uncapitalize_ascii
                      @@ c.c_name.id_str ^ "_post";
                    ld_def = post_def;
                  };
                ];
            ])
        cs
    in
    return @@ List.flatten lds
  in
  let open Gen_mlw in
  let d_contracts =
    List.map
      (fun c ->
        {
          cn_name = String.uncapitalize_ascii c.c_name.id_str;
          cn_num_kont = c.c_num_kont;
        })
      cs
  in
  let module G = Generator (struct
    let desc = { d_contracts; d_whyml = [] }
  end) in
  return
  @@ Decls
       (preambles
       @ (gen_gparam epp :: G.operation_ty_def :: ds)
       @ [ G.ctx_ty_def; G.ctx_wf_def ]
       @ postambles @ invariants
       @ [ Drec (G.unknown_func_def :: G.func_def) ])

let from_file s =
  let f = Lexer.parse_mlw_file @@ Lexing.from_channel @@ open_in s in
  let r =
    let* preambles, postambles, cs, epp = parse_mlw f in
    convert_mlw preambles postambles epp cs
  in
  raise_error r
