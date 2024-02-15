open Why3
open Ptree
open Ptree_helpers

let ident = ident
let qid (id : ident) : qualid = Qident id

let _binder_id (x : binder) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let param_id (x : param) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let _mk_internal_id s = s
let mk_binder ?pty id : binder = (Loc.dummy_position, Some id, false, pty)
let mk_param x pty = (Loc.dummy_position, Some (ident x), false, pty)

let mk_post t : post =
  (Loc.dummy_position, [ (pat @@ Pvar (ident "result"), t) ])

let mk_xpost id : xpost = (Loc.dummy_position, [ (qid id, None) ])

module P = struct
  let c_wild : pattern = pat Pwild
  let mk_var (x : ident) : pattern = pat_var x
  let mk_tuple (pl : pattern list) : pattern = pat @@ Ptuple pl
  let mk_app (qid : qualid) (ps : pattern list) = pat @@ Papp (qid, ps)
end

module T = struct
  let c_true : term = term @@ Ttrue
  let mk_var (x : ident) : term = tvar @@ qid x
  let mk_not (t : term) : term = term @@ Tnot t

  let _mk_imply (t1 : term) (t2 : term) : term =
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
  let c_int (n : int) : expr = econst n
  let mk_var (x : ident) : expr = evar @@ qid x

  let var_of_binder (x : binder) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let var_of_param (x : param) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let mk_app (f : qualid) (e_args : expr list) : expr = eapp f e_args

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
  let mk_record (el : (qualid * expr) list) : expr = expr @@ Erecord el

  let mk_match (e : expr) (cls : (pattern * expr) list) : expr =
    expr @@ Ematch (e, cls, [])

  let mk_proj (e : expr) (m : int) (n : int) : expr =
    assert (m > 0 && m > n);
    let p =
      P.mk_tuple
        (List.init m (fun i ->
             if i = n then P.mk_var @@ ident "x" else P.c_wild))
    in
    mk_match e [ (p, mk_var @@ ident "x") ]

  let _mk_update (e1 : expr) (m : int) (n : int) (e2 : expr) : expr =
    assert (m > 0 && m > n);
    let p =
      pat
      @@ Ptuple
           (List.init m (fun i ->
                pat @@ Pvar (ident @@ Format.sprintf "_x%d" i)))
    in
    let e =
      expr
      @@ Etuple
           (List.init m (fun i ->
                if i = n then e2 else mk_var (ident @@ Format.sprintf "_x%d" i)))
    in
    expr @@ Ematch (e1, [ (p, e) ], [])

  let mk_assume (t : term) : expr = expr @@ Eassert (Expr.Assume, t)
  let mk_raise (x : ident) : expr = expr @@ Eraise (qid x, None)
end

(**  {1 PTree builder for Michelson types}  *)

module Step_constant = struct
  let mk source sender self amount : expr =
    E.mk_record
      [
        (qualid [ "source" ], source);
        (qualid [ "sender" ], sender);
        (qualid [ "self" ], self);
        (qualid [ "amount" ], amount);
      ]

  let source st : expr = eapp (qualid [ "source" ]) [ st ]
  let sender st : expr = eapp (qualid [ "sender" ]) [ st ]
  let self st : expr = eapp (qualid [ "self" ]) [ st ]
  let amount st : expr = eapp (qualid [ "amount" ]) [ st ]
end

module Contract = struct
  let mk (ep : ident) (addr : expr) : expr =
    E.(mk_tuple [ mk_app (qid ep) []; addr ])

  let ep (c : expr) : expr = E.(mk_proj c 2 0)
  let addr (c : expr) : expr = E.(mk_proj c 2 1)
end
