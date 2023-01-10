open Why3
open Ptree
open Ptree_helpers

type contract = {
  cn_name : string;
  cn_param_ty : Sort.t;
  cn_store_ty : Sort.t;
  cn_num_kont : int;
  cn_index : int;
      (* cn_post : term; *)
      (* cn_kont : ops list; *)
}

(** Convert [Sort.t] value into [Why3.Ptree.pty] value.  *)
let rec pty_of_sort (s : Sort.t) : Ptree.pty =
  let ty s = PTtyapp (qualid [ s ], []) in
  match s with
  | S_string -> ty "string"
  | S_nat -> ty "nat"
  | S_int -> ty "int"
  | S_bytes -> ty "bytes"
  | S_bool -> ty "bool"
  | S_unit -> ty "unit"
  | S_list s -> PTtyapp (qualid [ "list" ], [ pty_of_sort s ])
  | S_pair (s1, s2) -> PTtuple [ pty_of_sort s1; pty_of_sort s2 ]
  | S_option s -> PTtyapp (qualid [ "option" ], [ pty_of_sort s ])
  | S_or (s1, s2) ->
      PTtyapp (qualid [ "or" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_set s -> PTtyapp (qualid [ "set" ], [ pty_of_sort s ])
  | S_map (s1, s2) ->
      PTtyapp (qualid [ "map" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_big_map (s1, s2) ->
      PTtyapp (qualid [ "map" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_lambda (s1, s2) ->
      PTtyapp (qualid [ "lambda" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_timestamp -> ty "timestamp"
  | S_mutez -> ty "mutez"
  | S_address -> ty "address"
  | S_contract s -> PTtyapp (qualid [ "contract" ], [ pty_of_sort s ])
  | S_operation -> ty "operation"
  | S_key -> ty "key"
  | S_key_hash -> ty "key_hash"
  | S_signature -> ty "signature"
  | S_chain_id -> ty "chain_id"
  | _ -> assert false

let constr_of_sort (s : Sort.t) : string =
  let open Re in
  let re = compile @@ alt [ char ' '; char '('; char ')' ] in
  Sort.string_of_sort s |> String.capitalize_ascii
  |> Re.replace re ~f:(fun g ->
         match Re.Group.get g 0 with
         | " " -> "_"
         | "(" -> "'0"
         | ")" -> "'1"
         | _ -> assert false)
  |> Format.sprintf "P%s"

let fresh_id =
  let count = ref 0 in
  fun () ->
    incr count;
    Format.sprintf "x%d" !count

let gas_ident = "g"
let gas_qualid : qualid = qualid [ gas_ident ]
let terminate_ident = "Terminate"
let terminate_qualid : qualid = qualid [ terminate_ident ]
let mk_internal_id s = s
let mk_binder ?ty x : binder = (Loc.dummy_position, Some (ident x), false, ty)
let mk_xpost qid : xpost = (Loc.dummy_position, [ (qid, None) ])

(** convert expression to term *)
let rec term_of_expr (e : expr) : term =
  let term_desc =
    match e.expr_desc with
    | Eident qid -> Tident qid
    | Eidapp (f, l) -> Tidapp (f, List.map term_of_expr l)
    | Etuple el -> Ttuple (List.map term_of_expr el)
    | Ematch (e, cls, []) ->
        Tcase (term_of_expr e, List.map (fun (p, e) -> (p, term_of_expr e)) cls)
    | _ -> assert false
  in
  { term_desc; term_loc = e.expr_loc }

module E = struct
  let mk_var (x : string) : expr = evar @@ qualid [ x ]

  let var_of_param (x : param) : expr =
    match x with
    | _, Some x, _, _ -> evar @@ qualid [ x.id_str ]
    | _ -> assert false

  let mk_let (x : string) (e1 : expr) (e2 : expr) : expr =
    expr @@ Elet (ident x, false, RKnone, e1, e2)

  let mk_seq (el : expr list) : expr =
    match List.rev el with
    | [] -> assert false
    | x :: xs -> List.fold_left (fun tl hd -> expr @@ Esequence (hd, tl)) x xs

  let mk_if (e1 : expr) (e2 : expr) (e3 : expr) : expr = expr @@ Eif (e1, e2, e3)

  let mk_any (ty : pty) : expr =
    expr @@ Eany ([], RKnone, Some ty, pat Pwild, Ity.MaskVisible, empty_spec)

  let mk_bin (e1 : expr) (o : string) (e2 : expr) : expr =
    expr @@ Einnfix (e1, ident @@ Ident.op_infix o, e2)

  let mk_tuple (el : expr list) : expr = expr @@ Etuple el

  let mk_proj (e : expr) (m : int) (n : int) : expr =
    assert (m > 0 && m > n);
    let p =
      pat
      @@ Ptuple
           (List.init m (fun i ->
                if i = n then pat @@ Pvar (ident "x") else pat Pwild))
    in
    expr @@ Ematch (e, [ (p, mk_var "x") ], [])

  let mk_update (e1 : expr) (m : int) (n : int) (e2 : expr) : expr =
    assert (m > 0 && m > n);
    let p =
      pat
      @@ Ptuple
           (List.init m (fun i -> pat @@ Pvar (ident @@ Format.sprintf "x%d" i)))
    in
    let e =
      expr
      @@ Etuple
           (List.init m (fun i ->
                if i = n then e2 else mk_var (Format.sprintf "x%d" i)))
    in
    expr @@ Ematch (e1, [ (p, e) ], [])

  let mk_assume (t : term) : expr = expr @@ Eassert (Expr.Assume, t)
end

module Step_constant = struct
  let mk source sender self amount : expr =
    E.mk_tuple [ source; sender; self; amount ]

  let source st : expr = eapp (qualid [ "source" ]) [ st ]
  let sender st : expr = eapp (qualid [ "sender" ]) [ st ]
  let self st : expr = eapp (qualid [ "self" ]) [ st ]
  let amount st : expr = eapp (qualid [ "amount" ]) [ st ]
end

let wrap_gas_check e =
  let open E in
  mk_if
    (mk_bin (mk_var gas_ident) "<=" (econst 0))
    (expr @@ Eraise (terminate_qualid, None))
    e

let gas_variant : variant = [ (tvar gas_qualid, None) ]

module type Desc = sig
  val contracts : contract list
end

module Generator (D : Desc) = struct
  module M = Map.Make (String)

  let contracts =
    List.fold_left
      (fun (s, i) c -> (M.add c.cn_name { c with cn_index = i } s, i + 1))
      (M.empty, 0) D.contracts
    |> fst

  let balance_of (ctx : expr) (c : contract) : expr =
    eapp (qualid [ c.cn_name ^ "_balance" ]) [ ctx ]

  let store_of (ctx : expr) (c : contract) : expr =
    eapp (qualid [ c.cn_name ^ "_store" ]) [ ctx ]

  let update_balance_of (ctx : expr) (c : contract) (e : expr) : expr =
    eapp (qualid [ c.cn_name ^ "_balance_update" ]) [ ctx; e ]

  let update_store_of (ctx : expr) (c : contract) (e : expr) : expr =
    eapp (qualid [ c.cn_name ^ "_store_update" ]) [ ctx; e ]

  let incr_balance_of (ctx : expr) (c : contract) (amt : expr) : expr =
    update_balance_of ctx c (E.mk_bin (balance_of ctx c) "+" amt)

  let decr_balance_of (ctx : expr) (c : contract) (amt : expr) : expr =
    update_balance_of ctx c (E.mk_bin (balance_of ctx c) "-" amt)

  let assume_spec_of (c : contract) st p s ops s' : expr =
    E.mk_assume @@ term_of_expr
    @@ eapp (qualid [ c.cn_name ^ "_spec" ]) [ st; p; s; ops; s' ]

  let dispatch_transfer (ctx : expr) (st : expr) p : expr =
    let extract_param p ty body =
      expr
      @@ Ematch
           ( p,
             [
               ( pat
                 @@ Papp (qualid [ constr_of_sort ty ], [ pat_var @@ ident "p" ]),
                 body (E.mk_var "p") );
               (pat @@ Pwild, expr @@ Eabsurd);
             ],
             [] )
    in
    List.fold_left
      (fun e { cn_name; cn_param_ty; _ } ->
        E.mk_if
          (E.mk_bin (Step_constant.self st) "=" (E.mk_var cn_name))
          ( extract_param p cn_param_ty @@ fun p ->
            eapp
              (qualid [ Format.sprintf "%s_func" cn_name ])
              [ E.mk_bin (E.mk_var gas_ident) "-" (econst 1); st; p; ctx ] )
          e)
      (eapp (qualid [ "unknown" ])
         [ E.mk_bin (E.mk_var gas_ident) "-" (econst 1); ctx ])
      D.contracts

  let ( let* ) e f =
    let x = fresh_id () in
    E.mk_let x e (f (E.mk_var x))

  let declare_accessor contract =
    let ctx_ty = PTtyapp (qualid [ "ctx" ], []) in
    let n = M.cardinal contracts in
    let ctx : param = (Loc.dummy_position, Some (ident "c"), false, ctx_ty) in
    let amt : param =
      (Loc.dummy_position, Some (ident "m"), false, pty_of_sort Sort.S_mutez)
    in
    let s : param =
      ( Loc.dummy_position,
        Some (ident "s"),
        false,
        pty_of_sort contract.cn_store_ty )
    in
    [
      {
        ld_loc = Loc.dummy_position;
        ld_ident = ident @@ contract.cn_name ^ "_balance";
        ld_params = [ ctx ];
        ld_type = Some (pty_of_sort Sort.S_mutez);
        ld_def =
          Some
            (term_of_expr
            @@ E.mk_proj (E.var_of_param ctx) (2 * n) contract.cn_index);
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = ident @@ contract.cn_name ^ "_store";
        ld_params = [ ctx ];
        ld_type = Some (pty_of_sort contract.cn_store_ty);
        ld_def =
          Some
            (term_of_expr
            @@ E.mk_proj (E.var_of_param ctx) (2 * n) (n + contract.cn_index));
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = ident @@ contract.cn_name ^ "_balance_update";
        ld_params = [ ctx; amt ];
        ld_type = Some ctx_ty;
        ld_def =
          Some
            (term_of_expr
            @@ E.mk_update (E.var_of_param ctx) (2 * n) contract.cn_index
                 (E.var_of_param amt));
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = ident @@ contract.cn_name ^ "_store_update";
        ld_params = [ ctx; s ];
        ld_type = Some ctx_ty;
        ld_def =
          Some
            (term_of_expr
            @@ E.mk_update (E.var_of_param ctx) (2 * n) (n + contract.cn_index)
                 (E.var_of_param s));
      };
    ]

  let known_contract (contract : contract) : fundef =
    let st = E.mk_var "st" in
    let param = E.mk_var "p" in
    let ctx = E.mk_var "c" in
    let spec =
      {
        empty_spec with
        sp_xpost = [ mk_xpost terminate_qualid ];
        sp_variant = gas_variant;
      }
    in
    let transfer ctx param amt dst : expr =
      let* ctx = decr_balance_of ctx contract amt in
      let* st = Step_constant.(mk (source st) (self st) dst amt) in
      dispatch_transfer ctx st param
    in
    let rec mk_ops_pat n acc =
      if n > 0 then
        let p = fresh_id () in
        let amt = fresh_id () in
        let dst = fresh_id () in
        let p_xfer =
          pat
          @@ Papp
               ( qualid [ "Xfer" ],
                 [
                   pat_var @@ ident p;
                   pat_var @@ ident amt;
                   pat_var @@ ident dst;
                 ] )
        in
        mk_ops_pat (n - 1)
          ( pat @@ Papp (qualid [ "Cons" ], [ p_xfer; fst acc ]),
            (E.mk_var p, E.mk_var amt, E.mk_var dst) :: snd acc )
      else acc
    in
    let mk_clause ctx n =
      let ops_p, binders =
        mk_ops_pat n (pat @@ Papp (qualid [ "Nil" ], []), [])
      in
      let rec aux ctx l =
        match l with
        | [] -> ctx
        | (p, amt, dst) :: tl ->
            let* ctx = transfer ctx p amt dst in
            aux ctx tl
      in
      (ops_p, aux ctx binders)
    in
    let body =
      let* ctx = incr_balance_of ctx contract (Step_constant.amount st) in
      let* new_s = E.mk_any @@ pty_of_sort contract.cn_store_ty in
      let* ops = E.mk_any @@ pty_of_sort @@ Sort.(S_list S_operation) in
      let* _ =
        assume_spec_of contract st param (store_of ctx contract) ops new_s
      in
      let* ctx = update_store_of ctx contract new_s in
      let cls =
        (pat @@ Pwild, expr @@ Eabsurd)
        :: List.rev_map
             (fun i -> mk_clause ctx i)
             (List.init (contract.cn_num_kont + 1) Fun.id)
      in
      expr @@ Ematch (ops, List.rev cls, [])
    in
    let body = wrap_gas_check body in
    ( ident @@ contract.cn_name ^ "_func",
      true,
      RKnone,
      [ mk_binder gas_ident; mk_binder "st"; mk_binder "p"; mk_binder "c" ],
      None,
      pat Pwild,
      Ity.MaskVisible,
      spec,
      body )

  let accessor =
    List.map (fun (_, c) -> declare_accessor c) @@ M.bindings contracts
    |> List.flatten

  let func_def =
    List.map (fun (_, c) -> known_contract c) @@ M.bindings contracts
end

let file () =
  let module G = Generator (struct
    let contracts =
      [
        {
          cn_name = "boomerang";
          cn_param_ty = Sort.S_unit;
          cn_store_ty = Sort.S_unit;
          cn_num_kont = 2;
          cn_index = 0;
        };
      ]
  end) in
  Decls
    ([ use ~import:false [ "michelson"; "Michelson" ] ]
    @ List.map (fun ld -> Dlogic [ ld ]) G.accessor
    @ [ Drec G.func_def ])
