module Regexp = Re
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
  (* cn_param_ty : Sort.t; *)
  (* cn_store_ty : Sort.t; *)
  cn_num_kont : int;
      (* cn_index : int; *)
      (* cn_spec : logic_decl; *)
      (* cn_pre : logic_decl; *)
      (* cn_post : logic_decl; *)
}

type desc = {
  d_contracts : contract list;
  (* d_inv_pre : logic_decl; *)
  (* d_inv_post : logic_decl; *)
  d_whyml : decl list;
}

(* id definitions
   Magical words should be defined here. *)

let ctx_ty_ident = ident "ctx"
let ctx_wf_ident = ident "ctx_wf"
let step_ty_ident = ident "step"
let step_wf_ident = ident "st_wf"
let spec_ident = ident "spec"
let addr_ident = ident "addr"
let storage_ty_ident = ident "storage"
let storage_wf_ident = ident "storage_wf"
let gparam_ty_ident = ident "gparam"
let operation_ty_ident = ident "operation"
let gas_ident = ident "g"
let terminate_ident = ident "Terminate"
let insufficient_mutez_ident = ident "Insufficient_mutez"
let unknown_ident = ident "unknown"
let unknown_param_ctr_ident = ident "Punknown"
let xfer_cstr_ident = ident "Xfer"
let sdel_cstr_ident = ident "Sdel"

let qid_of (c : contract) (id : ident) =
  qualid [ String.capitalize_ascii c.cn_name; id.id_str ]

let id_contract_of (c : contract) : ident = ident c.cn_name
let id_gparam_of (c : contract) : ident = ident @@ c.cn_name ^ "_gparam"
let id_param_wf_of (c : contract) : ident = ident @@ c.cn_name ^ "_param_wf"
let id_func_of (c : contract) : ident = ident @@ c.cn_name ^ "_func"
let id_spec_of (c : contract) : ident = ident @@ c.cn_name ^ "_spec"
let id_pre_of (c : contract) : ident = ident @@ c.cn_name ^ "_pre"
let id_post_of (c : contract) : ident = ident @@ c.cn_name ^ "_post"
let id_balance_of (c : contract) : ident = ident @@ c.cn_name ^ "_balance"
let id_store_of (c : contract) : ident = ident @@ c.cn_name ^ "_storage"

let id_is_param_of (c : contract) : ident =
  ident @@ "is_" ^ c.cn_name ^ "_param"

let constr_of_sort (s : Sort.t) : string =
  let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')' ]) in
  Sort.string_of_sort s |> String.capitalize_ascii
  |> Regexp.replace re ~f:(fun g ->
         match Regexp.Group.get g 0 with
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
  | S_nat | S_mutez -> T.of_expr @@ E.mk_bin p ">=" @@ econst 0
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
    List.fold_left (fun s c -> M.add c.cn_name c s) M.empty D.desc.d_contracts

  (* code fragment makers *)

  let wrap_assume ~(assumption : term) (e : expr) : expr =
    E.mk_seq (E.mk_assume assumption) e

  let wrap_gas_check (e : expr) : expr =
    E.mk_if
      (E.mk_bin (E.mk_var gas_ident) "<" (econst 0))
      (E.mk_raise terminate_ident)
      e

  let gas_decr : expr = E.mk_bin (E.mk_var gas_ident) "-" @@ econst 1
  let gas_variant : variant = [ (tvar @@ qid gas_ident, None) ]
  let ctx_pty = PTtyapp (qid ctx_ty_ident, [])
  let step_pty = PTtyapp (qid step_ty_ident, [])
  let gparam_pty = PTtyapp (qid gparam_ty_ident, [])
  let storage_pty_of c = PTtyapp (qid_of c storage_ty_ident, [])
  let qid_storage_wf_of (c : contract) : qualid = qid_of c storage_wf_ident
  let call_ctx_wf (ctx : expr) : expr = eapp (qid ctx_wf_ident) [ ctx ]
  let call_st_wf (st : expr) : expr = eapp (qid step_wf_ident) [ st ]
  let call_inv_pre (ctx : expr) : expr = eapp (qualid [ "inv_pre" ]) [ ctx ]

  let call_inv_post (ctx : expr) (ctx' : expr) : expr =
    eapp (qualid [ "inv_post" ]) [ ctx; ctx' ]

  let is_contract_of (c : contract) (e : expr) : expr =
    E.mk_bin e "=" @@ evar @@ qid_of c addr_ident

  let call_param_wf_of (c : contract) (p : expr) : expr =
    eapp (qid @@ id_param_wf_of c) [ p ]

  let call_storage_wf_of (c : contract) (s : expr) : expr =
    eapp (qid_storage_wf_of c) [ s ]

  let call_spec_of (c : contract) (st : expr) (gp : expr) (s : expr)
      (ops : expr) (s' : expr) : expr =
    eapp (qid_of c spec_ident) [ st; gp; s; ops; s' ]

  let call_pre_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_pre_of c) [ ctx ]

  let call_post_of (c : contract) (st : expr) (p : expr) (ctx : expr)
      (ctx' : expr) : expr =
    eapp (qid @@ id_post_of c) [ st; p; ctx; ctx' ]

  let call_is_param_of (c : contract) (gp : expr) : expr =
    eapp (qid @@ id_is_param_of c) [ gp ]

  let balance_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_balance_of c) [ ctx ]

  let storage_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_store_of c) [ ctx ]

  let update_balance_of (c : contract) (ctx : expr) (e : expr) : expr =
    expr @@ Eupdate (ctx, [ (qid @@ id_balance_of c, e) ])

  let update_storage_of (c : contract) (ctx : expr) (e : expr) : expr =
    expr @@ Eupdate (ctx, [ (qid @@ id_store_of c, e) ])

  let incr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx @@ E.mk_bin (balance_of c ctx) "+" amt

  let decr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx @@ E.mk_bin (balance_of c ctx) "-" amt

  let call_func_of (c : contract) (st : expr) (gp : expr) (ctx : expr) : expr =
    eapp (qid @@ id_func_of c) [ gas_decr; st; gp; ctx ]

  let call_unknown (ctx : expr) : expr =
    eapp (qid unknown_ident) [ gas_decr; ctx ]

  let dispatch_transfer (ctx : expr) (st : expr) (gp : expr) : expr =
    M.fold
      (fun _ c e ->
        E.mk_if
          (is_contract_of c @@ Step_constant.self st)
          (call_func_of c st gp ctx) e)
      contracts (call_unknown ctx)

  let ( let+ ) e f =
    let x = fresh_id () in
    E.mk_let x e (f (E.mk_var x))

  let known_contract (contract : contract) : fundef =
    let st = mk_binder @@ ident "st" in
    let gparam = mk_binder @@ ident "gp" in
    let ctx = mk_binder @@ ident "c" in
    let spec =
      {
        empty_spec with
        sp_pre =
          List.map T.of_expr
            [
              is_contract_of contract @@ Step_constant.self
              @@ E.var_of_binder st;
              call_ctx_wf @@ E.var_of_binder ctx;
              call_st_wf @@ E.var_of_binder st;
              call_pre_of contract @@ E.var_of_binder ctx;
            ];
        sp_post =
          [
            mk_post @@ T.of_expr @@ call_ctx_wf @@ E.mk_var Id.result;
            mk_post @@ T.of_expr
            @@ call_post_of contract (E.var_of_binder st)
                 (E.var_of_binder gparam) (E.var_of_binder ctx)
                 (E.mk_var Id.result);
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
        let o = fresh_id () in
        mk_ops_pat (n - 1)
          ( pat @@ Papp (qualid [ "Cons" ], [ pat_var o; fst acc ]),
            E.mk_var o :: snd acc )
      else acc
    in
    let mk_clause ctx n =
      let ops_p, binders =
        mk_ops_pat n (pat @@ Papp (qualid [ "Nil" ], []), [])
      in
      let rec aux ctx l =
        match l with
        | [] -> ctx
        | o :: tl ->
            let gp = fresh_id () in
            let amt = fresh_id () in
            let dst = fresh_id () in
            let+ ctx =
              expr
              @@ Ematch
                   ( o,
                     [
                       (pat @@ Papp (qualid [ "Sdel" ], [ pat Pwild ]), ctx);
                       ( pat
                         @@ Papp
                              ( qualid [ "Xfer" ],
                                [ pat_var gp; pat_var amt; pat_var dst ] ),
                         wrap_assume
                           ~assumption:(sort_wf Sort.S_mutez @@ E.mk_var amt)
                         @@ E.mk_if
                              (E.mk_bin (balance_of contract ctx) "<"
                              @@ E.mk_var amt)
                              (E.mk_raise insufficient_mutez_ident)
                         @@ let+ ctx =
                              decr_balance_of contract ctx @@ E.mk_var amt
                            in
                            let+ st =
                              Step_constant.(
                                mk
                                  (source @@ E.var_of_binder st)
                                  (self @@ E.var_of_binder st)
                                  (E.mk_var dst) (E.mk_var amt))
                            in
                            dispatch_transfer ctx st (E.mk_var gp) );
                     ],
                     [] )
            in
            aux ctx tl
      in
      (ops_p, aux ctx binders)
    in
    let body =
      let+ ctx =
        incr_balance_of contract (E.var_of_binder ctx)
          (Step_constant.amount @@ E.var_of_binder st)
      in
      let+ new_s =
        E.mk_any
          ~ensure:
            (T.of_expr
            @@ call_storage_wf_of contract
            @@ E.mk_var @@ ident "result")
        @@ storage_pty_of contract
      in
      let+ ops = E.mk_any @@ Sort.pty_of_sort Sort.(S_list S_operation) in
      wrap_assume
        ~assumption:
          (T.of_expr
          @@ call_spec_of contract (E.var_of_binder st) (E.var_of_binder gparam)
               (storage_of contract ctx) ops new_s)
      @@ let+ ctx = update_storage_of contract ctx new_s in
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
      [ mk_binder gas_ident; st; gparam; ctx ],
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
      E.mk_if (E.mk_any @@ Sort.pty_of_sort Sort.S_bool) (E.var_of_binder ctx)
      @@ let+ st =
           E.mk_any
             ~ensure:(T.of_expr @@ call_st_wf @@ E.mk_var @@ ident "result")
             step_pty
         in
         let+ p = E.mk_any gparam_pty in
         wrap_assume ~assumption:(wf st)
         @@ let+ ctx = dispatch_transfer (E.var_of_binder ctx) st p in
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
    let flds =
      M.fold
        (fun _ c flds ->
          {
            f_loc = Loc.dummy_position;
            f_ident = id_store_of c;
            f_pty = storage_pty_of c;
            f_mutable = false;
            f_ghost = false;
          }
          :: {
               f_loc = Loc.dummy_position;
               f_ident = id_balance_of c;
               f_pty = Sort.pty_of_sort Sort.S_mutez;
               f_mutable = false;
               f_ghost = false;
             }
          :: flds)
        contracts []
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
          td_def = TDrecord flds;
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
                  xfer_cstr_ident,
                  [
                    (Loc.dummy_position, None, false, gparam_pty);
                    ( Loc.dummy_position,
                      None,
                      false,
                      Sort.pty_of_sort Sort.S_mutez );
                    ( Loc.dummy_position,
                      None,
                      false,
                      Sort.pty_of_sort Sort.S_address );
                  ] );
                ( Loc.dummy_position,
                  sdel_cstr_ident,
                  [
                    ( Loc.dummy_position,
                      None,
                      false,
                      Sort.pty_of_sort Sort.(S_option S_key_hash) );
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
               (T.of_expr @@ call_storage_wf_of c @@ storage_of c
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

  let func_def =
    List.map (fun (_, c) -> known_contract c) @@ M.bindings contracts
end

let file desc =
  let module G = Generator (struct
    let desc = desc
  end) in
  Decls
    ([ use ~import:false [ "michelson"; "Michelson" ] ]
    @ [ G.ctx_ty_def; G.operation_ty_def ]
    (* @ List.map (fun ld -> Dlogic [ ld ]) G.accessor *)
    @ [ G.ctx_wf_def ]
    @ desc.d_whyml
    (* @ List.map (fun ld -> Dlogic [ ld ]) G.spec *)
    @ [ Drec (G.unknown_func_def :: G.func_def) ])
