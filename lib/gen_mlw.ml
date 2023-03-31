open Why3
open Ptree
open Ptree_helpers

let fresh_id =
  let count = ref 0 in
  fun ?(x = "x") () ->
    incr count;
    ident @@ Format.sprintf "%s%d" x !count

type contract = {
  cn_name : string;
  cn_param_ty : Sort.t;
  cn_store_ty : Sort.t;
  cn_num_kont : int;
  cn_index : int;
  cn_spec : logic_decl;
  cn_pre : logic_decl;
  cn_post : logic_decl;
}

type desc = {
  d_contracts : contract list;
  d_inv_pre : logic_decl;
  d_inv_post : logic_decl;
  d_whyml : decl list;
}

(* id definitions
   Magical words should be defined here. *)

let ctx_ty_ident = ident "ctx"
let ctx_wf_ident = ident "ctx_wf"
let step_ty_ident = ident "step"
let step_wf_ident = ident "st_wf"
let gparam_ty_ident = ident "param"
let operation_ty_ident = ident "operation"
let gas_ident = ident "g"
let terminate_ident = ident "Terminate"
let insufficient_mutez_ident = ident "Insufficient_mutez"
let unknown_ident = ident "unknown"
let id_contract_of (c : contract) : ident = ident c.cn_name
let id_gparam_of (c : contract) : ident = ident @@ c.cn_name ^ "_gparam"
let id_param_wf_of (c : contract) : ident = ident @@ c.cn_name ^ "_param_wf"
let id_store_wf_of (c : contract) : ident = ident @@ c.cn_name ^ "_store_wf"
let id_func_of (c : contract) : ident = ident @@ c.cn_name ^ "_func"
let id_spec_of (c : contract) : ident = ident @@ c.cn_name ^ "_spec"
let id_pre_of (c : contract) : ident = ident @@ c.cn_name ^ "_pre"
let id_post_of (c : contract) : ident = ident @@ c.cn_name ^ "_post"
let id_balance_of (c : contract) : ident = ident @@ c.cn_name ^ "_balance"
let id_store_of (c : contract) : ident = ident @@ c.cn_name ^ "_store"

let id_update_balance_of (c : contract) : ident =
  ident @@ c.cn_name ^ "_balance_update"

let id_update_store_of (c : contract) : ident =
  ident @@ c.cn_name ^ "_store_update"

let id_is_param_of (c : contract) : ident =
  ident @@ "is_" ^ c.cn_name ^ "_param"

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
  | S_operation -> ty operation_ty_ident.id_str
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

let qid (id : ident) : qualid = Qident id

let binder_id (x : binder) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let param_id (x : param) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let mk_internal_id s = s
let mk_binder ?pty id : binder = (Loc.dummy_position, Some id, false, pty)
let mk_param x pty = (Loc.dummy_position, Some (ident x), false, pty)

let mk_post t : post =
  (Loc.dummy_position, [ (pat @@ Pvar (ident "result"), t) ])

let mk_xpost id : xpost = (Loc.dummy_position, [ (qid id, None) ])

module T = struct
  let mk_not (t : term) : term = term @@ Tnot t

  let mk_imply (t1 : term) (t2 : term) : term =
    term @@ Tbinnop (t1, Dterm.DTimplies, t2)

  let mk_and (t1 : term) (t2 : term) : term =
    term @@ Tbinnop (t1, Dterm.DTand, t2)

  (** convert expression to term *)
  let rec of_expr (e : expr) : term =
    let term_desc =
      match e.expr_desc with
      | Etrue -> Ttrue
      | Efalse -> Tfalse
      | Econst c -> Tconst c
      | Eident qid -> Tident qid
      | Eidapp (f, l) -> Tidapp (f, List.map of_expr l)
      | Einnfix (e1, o, e2) -> Tinnfix (of_expr e1, o, of_expr e2)
      | Etuple el -> Ttuple (List.map of_expr el)
      | Ematch (e, cls, []) ->
          Tcase (of_expr e, List.map (fun (p, e) -> (p, of_expr e)) cls)
      | _ -> assert false
    in
    { term_desc; term_loc = e.expr_loc }
end

module E = struct
  let mk_var (x : ident) : expr = evar @@ qid x

  let var_of_binder (x : binder) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let var_of_param (x : param) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let mk_let (x : ident) (e1 : expr) (e2 : expr) : expr =
    expr @@ Elet (x, false, RKnone, e1, e2)

  let mk_seq (e1 : expr) (e2 : expr) : expr = expr @@ Esequence (e1, e2)
  let mk_if (e1 : expr) (e2 : expr) (e3 : expr) : expr = expr @@ Eif (e1, e2, e3)

  let mk_any ?ensure (pty : pty) : expr =
    let sp_post =
      match ensure with
      | None -> []
      | Some t ->
          [ (Loc.dummy_position, [ (pat @@ Pvar (ident "result"), t) ]) ]
    in
    expr
    @@ Eany
         ( [],
           RKnone,
           Some pty,
           pat Pwild,
           Ity.MaskVisible,
           { empty_spec with sp_post } )

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
    expr @@ Ematch (e, [ (p, mk_var @@ ident "x") ], [])

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
                if i = n then e2 else mk_var (ident @@ Format.sprintf "x%d" i)))
    in
    expr @@ Ematch (e1, [ (p, e) ], [])

  let mk_assume (t : term) : expr = expr @@ Eassert (Expr.Assume, t)
  let mk_raise (x : ident) : expr = expr @@ Eraise (qid x, None)
end

module Step_constant = struct
  let mk source sender self amount : expr =
    E.mk_tuple [ source; sender; self; amount ]

  let source st : expr = eapp (qualid [ "source" ]) [ st ]
  let sender st : expr = eapp (qualid [ "sender" ]) [ st ]
  let self st : expr = eapp (qualid [ "self" ]) [ st ]
  let amount st : expr = eapp (qualid [ "amount" ]) [ st ]
end

let rec sort_wf (s : Sort.t) (p : expr) : term =
  match s with
  | S_nat | S_mutez -> term Ttrue (* T.of_expr @@ E.mk_bin p ">=" @@ econst 0 *)
  | S_pair (s1, s2) ->
      T.mk_and (sort_wf s1 @@ E.mk_proj p 2 0) (sort_wf s2 @@ E.mk_proj p 2 1)
  | S_or (s1, s2) ->
      term
      @@ Tcase
           ( T.of_expr p,
             [
               ( pat @@ Papp (qualid [ "Left" ], [ pat @@ Pvar (ident "p") ]),
                 sort_wf s1 @@ E.mk_var @@ ident "p" );
               ( pat @@ Papp (qualid [ "Right" ], [ pat @@ Pvar (ident "p") ]),
                 sort_wf s2 @@ E.mk_var @@ ident "p" );
             ] )
  | _ -> term Ttrue

module type Desc = sig
  val desc : desc
end

module Generator (D : Desc) = struct
  module M = Map.Make (String)

  let contracts =
    List.fold_left
      (fun (s, i) c -> (M.add c.cn_name { c with cn_index = i } s, i + 1))
      (M.empty, 0) D.desc.d_contracts
    |> fst

  (* code fragment makers *)

  let wrap_assume ~(assumption : term) (e : expr) : expr =
    E.mk_seq (E.mk_assume assumption) e

  let wrap_gas_check (e : expr) : expr =
    E.mk_if
      (E.mk_bin (E.mk_var gas_ident) "<=" (econst 0))
      (E.mk_raise terminate_ident)
      e

  let gas_decr : expr = E.mk_bin (E.mk_var gas_ident) "-" @@ econst 1
  let gas_variant : variant = [ (tvar @@ qid gas_ident, None) ]
  let ctx_pty = PTtyapp (qid ctx_ty_ident, [])
  let step_pty = PTtyapp (qid step_ty_ident, [])
  let gparam_pty = PTtyapp (qid gparam_ty_ident, [])
  let call_ctx_wf (ctx : expr) : expr = eapp (qid ctx_wf_ident) [ ctx ]
  let call_st_wf (st : expr) : expr = eapp (qid step_wf_ident) [ st ]
  let call_inv_pre (ctx : expr) : expr = eapp (qualid [ "inv_pre" ]) [ ctx ]

  let call_inv_post (ctx : expr) (ctx' : expr) : expr =
    eapp (qualid [ "inv_post" ]) [ ctx; ctx' ]

  let is_contract_of (c : contract) (e : expr) : expr =
    E.mk_bin e "=" @@ E.mk_var @@ id_contract_of c

  let wrap_extract_param_of (c : contract) (gp : expr) (body : expr -> expr) :
      expr =
    let p = fresh_id ~x:"p" () in
    expr
    @@ Ematch
         ( gp,
           [
             ( pat
               @@ Papp (qualid [ constr_of_sort c.cn_param_ty ], [ pat_var p ]),
               body @@ E.mk_var p );
             (pat Pwild, expr Eabsurd);
           ],
           [] )

  let call_param_wf_of (c : contract) (p : expr) : expr =
    eapp (qid @@ id_param_wf_of c) [ p ]

  let call_store_wf_of (c : contract) (s : expr) : expr =
    eapp (qid @@ id_store_wf_of c) [ s ]

  let call_spec_of (c : contract) (st : expr) (p : expr) (s : expr) (ops : expr)
      (s' : expr) : expr =
    eapp (qid @@ id_spec_of c) [ st; p; s; ops; s' ]

  let call_pre_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_pre_of c) [ ctx ]

  let call_post_of (c : contract) (st : expr) (p : expr) (ctx : expr)
      (ctx' : expr) : expr =
    eapp (qid @@ id_post_of c) [ st; p; ctx; ctx' ]

  let call_is_param_of (c : contract) (gp : expr) : expr =
    eapp (qid @@ id_is_param_of c) [ gp ]

  let balance_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_balance_of c) [ ctx ]

  let store_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_store_of c) [ ctx ]

  let update_balance_of (c : contract) (ctx : expr) (e : expr) : expr =
    eapp (qid @@ id_update_balance_of c) [ ctx; e ]

  let update_store_of (c : contract) (ctx : expr) (e : expr) : expr =
    eapp (qid @@ id_update_store_of c) [ ctx; e ]

  let incr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx
    @@ eapp (qid @@ ident "mutez_add") [ balance_of c ctx; amt ]

  let decr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx
    @@ eapp (qid @@ ident "mutez_sub") [ balance_of c ctx; amt ]

  let call_func_of (c : contract) (st : expr) (gp : expr) (ctx : expr) : expr =
    wrap_extract_param_of c gp @@ fun p ->
    eapp (qid @@ id_func_of c) [ gas_decr; st; p; ctx ]

  let call_unknown (ctx : expr) : expr =
    eapp (qid unknown_ident) [ gas_decr; ctx ]

  let dispatch_transfer (ctx : expr) (st : expr) (gp : expr) : expr =
    M.fold
      (fun _ c e ->
        E.mk_if
          (is_contract_of c @@ Step_constant.self st)
          (wrap_assume ~assumption:(T.of_expr @@ call_is_param_of c gp)
          @@ call_func_of c st gp ctx)
          e)
      contracts (call_unknown ctx)

  let ( let* ) e f =
    let x = fresh_id () in
    E.mk_let x e (f (E.mk_var x))

  let declare_accessor (contract : contract) : logic_decl list =
    let n = M.cardinal contracts in
    let ctx : param = mk_param "c" ctx_pty in
    let amt : param = mk_param "m" @@ pty_of_sort Sort.S_mutez in
    let gp : param = mk_param "gp" gparam_pty in
    let p : param = mk_param "p" @@ pty_of_sort contract.cn_param_ty in
    let s : param = mk_param "s" @@ pty_of_sort contract.cn_store_ty in
    [
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_contract_of contract;
        ld_params = [];
        ld_type = Some (pty_of_sort Sort.S_address);
        ld_def = None;
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_gparam_of contract;
        ld_params = [ p ];
        ld_type = Some gparam_pty;
        ld_def =
          Some
            (T.of_expr
            @@ eapp
                 (qualid [ constr_of_sort contract.cn_param_ty ])
                 [ E.var_of_param p ]);
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_param_wf_of contract;
        ld_params = [ p ];
        ld_type = None;
        ld_def = Some (sort_wf contract.cn_param_ty @@ E.var_of_param p);
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_store_wf_of contract;
        ld_params = [ s ];
        ld_type = None;
        ld_def = Some (sort_wf contract.cn_store_ty @@ E.var_of_param s);
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_is_param_of contract;
        ld_params = [ gp ];
        ld_type = None;
        ld_def =
          (let p = fresh_id ~x:"p" () in
           Some
             (T.of_expr @@ expr
             @@ Ematch
                  ( E.var_of_param gp,
                    [
                      ( pat
                        @@ Papp
                             ( qualid [ constr_of_sort contract.cn_param_ty ],
                               [ pat @@ Pvar p ] ),
                        call_param_wf_of contract @@ E.mk_var p );
                      (pat Pwild, expr Efalse);
                    ],
                    [] )));
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_balance_of contract;
        ld_params = [ ctx ];
        ld_type = Some (pty_of_sort Sort.S_mutez);
        ld_def =
          Some
            (T.of_expr
            @@ E.mk_proj (E.var_of_param ctx) (2 * n) contract.cn_index);
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_store_of contract;
        ld_params = [ ctx ];
        ld_type = Some (pty_of_sort contract.cn_store_ty);
        ld_def =
          Some
            (T.of_expr
            @@ E.mk_proj (E.var_of_param ctx) (2 * n) (n + contract.cn_index));
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_update_balance_of contract;
        ld_params = [ ctx; amt ];
        ld_type = Some ctx_pty;
        ld_def =
          Some
            (T.of_expr
            @@ E.mk_update (E.var_of_param ctx) (2 * n) contract.cn_index
                 (E.var_of_param amt));
      };
      {
        ld_loc = Loc.dummy_position;
        ld_ident = id_update_store_of contract;
        ld_params = [ ctx; s ];
        ld_type = Some ctx_pty;
        ld_def =
          Some
            (T.of_expr
            @@ E.mk_update (E.var_of_param ctx) (2 * n) (n + contract.cn_index)
                 (E.var_of_param s));
      };
    ]

  let declare_spec (contract : contract) : logic_decl list =
    [
      { contract.cn_spec with ld_ident = id_spec_of contract };
      { contract.cn_pre with ld_ident = id_pre_of contract };
      { contract.cn_post with ld_ident = id_post_of contract };
    ]

  let known_contract (contract : contract) : fundef =
    let st = mk_binder @@ ident "st" in
    let param = mk_binder @@ ident "p" in
    let ctx = mk_binder @@ ident "c" in
    let spec =
      {
        empty_spec with
        sp_pre =
          [
            T.of_expr @@ is_contract_of contract @@ Step_constant.self
            @@ E.var_of_binder st;
            T.of_expr @@ call_param_wf_of contract @@ E.var_of_binder param;
            T.of_expr @@ call_ctx_wf @@ E.var_of_binder ctx;
            T.of_expr @@ call_st_wf @@ E.var_of_binder st;
            T.of_expr @@ call_pre_of contract @@ E.var_of_binder ctx;
          ];
        sp_post =
          [
            mk_post @@ T.of_expr @@ call_ctx_wf @@ E.mk_var @@ ident "result";
            mk_post @@ T.of_expr
            @@ call_post_of contract (E.var_of_binder st)
                 (E.var_of_binder param) (E.var_of_binder ctx)
                 (E.mk_var @@ ident "result");
          ];
        sp_xpost =
          (if contract.cn_num_kont > 0 then
           [ mk_xpost terminate_ident; mk_xpost insufficient_mutez_ident ]
          else [ mk_xpost terminate_ident ]);
        sp_variant = gas_variant;
      }
    in
    let rec mk_ops_pat n acc =
      if n > 0 then
        let p = fresh_id () in
        let amt = fresh_id () in
        let dst = fresh_id () in
        let p_xfer =
          pat
          @@ Papp (qualid [ "Xfer" ], [ pat_var p; pat_var amt; pat_var dst ])
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
            let* ctx =
              wrap_assume ~assumption:(sort_wf Sort.S_mutez amt)
              @@ E.mk_if
                   (eapp
                      (qid @@ ident "mutez_lt")
                      [ balance_of contract ctx; amt ])
                   (E.mk_raise insufficient_mutez_ident)
              @@ let* ctx = decr_balance_of contract ctx amt in
                 let* st =
                   Step_constant.(
                     mk
                       (source @@ E.var_of_binder st)
                       (self @@ E.var_of_binder st)
                       dst amt)
                 in
                 dispatch_transfer ctx st p
            in
            aux ctx tl
      in
      (ops_p, aux ctx binders)
    in
    let body =
      let* ctx =
        incr_balance_of contract (E.var_of_binder ctx)
          (Step_constant.amount @@ E.var_of_binder st)
      in
      let* new_s = E.mk_any @@ pty_of_sort contract.cn_store_ty in
      let* ops = E.mk_any @@ pty_of_sort Sort.(S_list S_operation) in
      wrap_assume
        ~assumption:
          (T.of_expr
          @@ call_spec_of contract (E.var_of_binder st) (E.var_of_binder param)
               (store_of contract ctx) ops new_s)
      @@ let* ctx = update_store_of contract ctx new_s in
         let cls =
           (pat @@ Pwild, expr @@ Eabsurd)
           :: List.rev_map
                (fun i -> mk_clause ctx i)
                (List.init (contract.cn_num_kont + 1) Fun.id)
         in
         expr @@ Ematch (ops, List.rev cls, [])
    in
    let body = wrap_gas_check body in
    ( id_func_of contract,
      true,
      Expr.RKnone,
      [ mk_binder gas_ident; st; param; ctx ],
      None,
      pat Pwild,
      Ity.MaskVisible,
      spec,
      body )

  let unknown_func_def =
    let ctx = mk_binder @@ ident "c" in
    let spec =
      {
        empty_spec with
        sp_pre =
          [
            T.of_expr @@ call_ctx_wf @@ E.var_of_binder ctx;
            T.of_expr @@ call_inv_pre @@ E.var_of_binder ctx;
          ];
        sp_post =
          [
            mk_post @@ T.of_expr @@ call_ctx_wf @@ E.mk_var @@ ident "result";
            mk_post @@ T.of_expr
            @@ call_inv_post (E.var_of_binder ctx)
            @@ E.mk_var @@ ident "result";
          ];
        sp_xpost =
          [ mk_xpost terminate_ident; mk_xpost insufficient_mutez_ident ];
        sp_variant = gas_variant;
      }
    in
    let wf st =
      M.fold
        (fun _ c t ->
          T.mk_not (T.of_expr @@ is_contract_of c @@ Step_constant.source st)
          :: T.mk_not (T.of_expr @@ is_contract_of c @@ Step_constant.sender st)
          :: t)
        contracts []
      |> List.fold_left T.mk_and @@ term Ttrue
    in
    let body =
      E.mk_if (E.mk_any @@ pty_of_sort Sort.S_bool) (E.var_of_binder ctx)
      @@ let* st =
           E.mk_any
             ~ensure:(T.of_expr @@ call_st_wf @@ E.mk_var @@ ident "result")
             step_pty
         in
         let* p = E.mk_any gparam_pty in
         wrap_assume ~assumption:(wf st)
         @@ let* ctx = dispatch_transfer (E.var_of_binder ctx) st p in
            call_unknown ctx
    in
    let body = wrap_gas_check body in
    ( unknown_ident,
      true,
      Expr.RKnone,
      [ mk_binder gas_ident; ctx ],
      None,
      pat Pwild,
      Ity.MaskVisible,
      spec,
      body )

  let ctx_ty_def =
    let stores =
      M.bindings contracts |> List.map snd
      |> List.sort (fun c1 c2 -> compare c1.cn_index c2.cn_index)
      |> List.map (fun c -> pty_of_sort c.cn_store_ty)
    in
    let balances =
      List.init (M.cardinal contracts) @@ fun _ -> pty_of_sort Sort.S_mutez
    in
    Dtype
      [
        {
          td_loc = Loc.dummy_position;
          td_ident = ctx_ty_ident;
          td_params = [];
          td_vis = Public;
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def = TDalias (PTtuple (balances @ stores));
        };
      ]

  let param_ty_def =
    let module S = Set.Make (struct
      type t = Sort.t

      let compare = compare
    end) in
    let d =
      M.fold
        (fun _ c -> S.add c.cn_param_ty)
        contracts (S.singleton Sort.S_unit)
      |> S.elements
      |> List.map (fun ty ->
             ( Loc.dummy_position,
               ident @@ constr_of_sort ty,
               [ (Loc.dummy_position, None, false, pty_of_sort ty) ] ))
    in
    Dtype
      [
        {
          td_loc = Loc.dummy_position;
          td_ident = gparam_ty_ident;
          td_params = [];
          td_vis = Public;
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def = TDalgebraic d;
        };
      ]

  let operation_ty_def =
    Dtype
      [
        {
          td_loc = Loc.dummy_position;
          td_ident = operation_ty_ident;
          td_params = [];
          td_vis = Public;
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def =
            TDalgebraic
              [
                ( Loc.dummy_position,
                  ident @@ "Xfer",
                  [
                    (Loc.dummy_position, None, false, gparam_pty);
                    (Loc.dummy_position, None, false, pty_of_sort Sort.S_mutez);
                    (Loc.dummy_position, None, false, pty_of_sort Sort.S_address);
                  ] );
              ];
        };
      ]

  let ctx_wf_def : decl =
    let ctx : param = mk_param "ctx" ctx_pty in
    let d =
      M.fold
        (fun _ c t ->
          T.mk_and (sort_wf Sort.S_mutez @@ balance_of c @@ E.var_of_param ctx)
          @@ T.mk_and
               (T.of_expr @@ call_store_wf_of c @@ store_of c
              @@ E.var_of_param ctx)
               t)
        contracts
      @@ term Ttrue
    in
    Dlogic
      [
        {
          ld_loc = Loc.dummy_position;
          ld_ident = ctx_wf_ident;
          ld_params = [ ctx ];
          ld_type = None;
          ld_def = Some d;
        };
      ]

  let accessor =
    List.map (fun (_, c) -> declare_accessor c) @@ M.bindings contracts
    |> List.flatten

  let spec =
    { D.desc.d_inv_pre with ld_ident = ident @@ "inv_pre" }
    :: { D.desc.d_inv_post with ld_ident = ident @@ "inv_post" }
    :: (List.map (fun (_, c) -> declare_spec c) @@ M.bindings contracts
       |> List.flatten)

  let func_def =
    List.map (fun (_, c) -> known_contract c) @@ M.bindings contracts
end

let file desc =
  let module G = Generator (struct
    let desc = desc
  end) in
  Decls
    ([ use ~import:false [ "michelson"; "Michelson" ] ]
    @ [ G.ctx_ty_def; G.param_ty_def; G.operation_ty_def ]
    @ List.map (fun ld -> Dlogic [ ld ]) G.accessor
    @ [ G.ctx_wf_def ] @ desc.d_whyml
    @ List.map (fun ld -> Dlogic [ ld ]) G.spec
    @ [ Drec (G.unknown_func_def :: G.func_def) ])
