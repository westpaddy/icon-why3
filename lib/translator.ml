open Why3
open Ptree
open Gen_mlw

type 'a iresult = ('a, string) Result.t

let return = Result.ok

let error ?(loc = Loc.dummy_position) msg =
  Format.kasprintf (fun s -> Result.error @@ Loc.errorm ~loc "%s" s) msg

let ( >>= ) = Result.bind
let ( let* ) = Result.bind

module StringMap = struct
  include Map.Make (String)

  let fold_e (f : key -> 'a -> 'b -> 'b iresult) (m : 'a t) (acc : 'b) :
      'b iresult =
    fold
      (fun k e acc ->
        let* acc = acc in
        f k e acc)
      m (return acc)
end

module List = struct
  include List

  let fold_left_e (f : 'a -> 'b -> 'a iresult) (acc : 'a) (l : 'b list) =
    fold_left
      (fun acc x ->
        let* acc = acc in
        f acc x)
      (return acc) l
end

let rec sort_of_pty (pty : pty) : Sort.t iresult =
  let elt1 l =
    match l with
    | [ pty ] -> sort_of_pty pty
    | _ -> error "expected 1 parameter"
  in
  let elt2 l =
    match l with
    | [ pty1; pty2 ] ->
        let* s1 = sort_of_pty pty1 in
        let* s2 = sort_of_pty pty2 in
        return (s1, s2)
    | _ -> error "expected 2 parameter"
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
      | s -> error "unknown sort %s" s)
  | PTtuple pl ->
      let* s1, s2 = elt2 pl in
      return @@ Sort.S_pair (s1, s2)
  | PTparen pty -> sort_of_pty pty
  | _ -> error "unknown sort %a" (Mlw_printer.pp_pty ~attr:true).closed pty

let find_type_def id decls =
  List.find_map
    (function
      | Dtype [ td ] when td.td_ident.id_str = id -> Some td | _ -> None)
    decls
  |> Option.to_result ~none:(Format.sprintf "type %s is missing" id)

let find_predicate_def id decls =
  List.find_map
    (function
      | Dlogic [ ld ] when ld.ld_ident.id_str = id -> Some ld | _ -> None)
    decls
  |> Option.to_result ~none:(Format.sprintf "predicate %s is missing" id)

let find_let_def id decls =
  List.find_map
    (function Dlet (x, _, _, e) when x.id_str = id -> Some e | _ -> None)
    decls
  |> Option.to_result ~none:(Format.sprintf "constant %s is missing" id)

let contract name decls =
  let sort_alias id =
    find_type_def id decls >>= fun td ->
    match td.td_def with TDalias pty -> sort_of_pty pty | _ -> error "alias"
  in
  let* cn_spec = find_predicate_def "spec" decls in
  let* cn_pre = find_predicate_def "pre" decls in
  let* cn_post = find_predicate_def "post" decls in
  let* cn_param_ty = sort_alias "param" in
  let* cn_store_ty = sort_alias "store" in
  let* cn_num_kont =
    find_let_def "upper_ops" decls >>= fun e ->
    match e.expr_desc with
    | Econst (ConstInt i) -> (
        try return @@ BigInt.to_int i.il_int
        with Failure _ ->
          error "upper bound length of operation lists is too large")
    | _ -> error "upper_ops_len shall be an integer constant"
  in
  return
    {
      cn_name = String.uncapitalize_ascii name;
      cn_param_ty;
      cn_store_ty;
      cn_spec;
      cn_pre;
      cn_post;
      cn_num_kont;
      cn_index = 0;
    }

let from_tzw mlw : desc iresult =
  let* decls =
    match mlw with
    | Decls dl ->
        List.fold_left_e
          (fun m d ->
            match d with
            | Dscope (loc, _, id, dl) ->
                if Option.is_some @@ StringMap.find_opt id.id_str m then
                  error ~loc "scope %s has been declared" id.id_str
                else return @@ StringMap.add id.id_str dl m
            | _ -> error "tzw only consists of scopes")
          StringMap.empty dl
    | _ -> error "tzw only consists of scopes"
  in
  let d_whyml = StringMap.find_opt "WhyML" decls |> Option.value ~default:[] in
  let decls = StringMap.remove "WhyML" decls in
  let* unknown_decls =
    StringMap.find_opt "Unknown" decls
    |> Option.to_result ~none:"mandatory scope Unknown is missing"
  in
  let* d_inv_pre = find_predicate_def "pre" unknown_decls in
  let* d_inv_post = find_predicate_def "post" unknown_decls in
  let decls = StringMap.remove "Unknown" decls in
  let* d_contracts =
    StringMap.fold_e
      (fun name decls contracts ->
        let* contract = contract name decls in
        return (contract :: contracts))
      decls []
  in
  return { d_contracts; d_inv_pre; d_inv_post; d_whyml }

let parse_file s =
  let f = Lexer.parse_mlw_file @@ Lexing.from_channel @@ open_in s in
  match from_tzw f with Ok l -> l | Error e -> Loc.errorm "%s@." e
