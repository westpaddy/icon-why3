open Why3

let parse_predicate s =
  Lexer.parse_decl @@ Lexing.from_string s |> function
  | Dlogic [ d ] -> d
  | _ -> assert false

let boomerang_spec =
  parse_predicate
    {|
predicate spec (st : step) (p : unit) (s : unit) (ops : list operation) (s' : unit) =
  s = s' /\
  (st.amount = 0 -> ops = Nil) /\
  (st.amount > 0 -> ops = Cons (Xfer (PUnit ()) st.amount st.source) Nil)
|}

let boomerang_pre = parse_predicate {|
predicate pre (c : ctx) = true
|}

let boomerang_post =
  parse_predicate
    {|
predicate post (st : step) (p : unit) (c : ctx) (c' : ctx) =
  c.boomerang_balance = c'.boomerang_balance
|}

let d_inv_pre =
  parse_predicate
    {|
predicate pre (c : ctx) = true
                               |}

let d_inv_post =
  parse_predicate
    {|
predicate post (c : ctx) (c' : ctx) =
  c.boomerang_balance = c'.boomerang_balance
                                |}

let boomerang_desc =
  let open Gen_mlw in
  {
    d_contracts =
      [
        {
          cn_name = "boomerang";
          cn_param_ty = Sort.S_unit;
          cn_store_ty = Sort.S_unit;
          cn_num_kont = 1;
          cn_index = 0;
          cn_spec = boomerang_spec;
          cn_pre = boomerang_pre;
          cn_post = boomerang_post;
        };
      ];
    d_inv_pre;
    d_inv_post;
  }

let cpmm_spec =
  parse_predicate
    {|
  predicate spec (st : step) (p : (nat, (address, address))) (s : (nat, (nat, address))) (ops : list operation) (s' : (nat, (nat, address))) =
    let token_pool, (xtz_pool, token_contract) = s in
    let token_pool', (xtz_pool', token_contract') = s' in
    let token_sold, (token_owner, receipient) = p in
    let b = div (token_sold * xtz_pool) (token_sold + token_pool) in
    token_sold > 0 /\
    token_owner <> st.self /\
    token_pool' = token_pool + token_sold /\
    xtz_pool' = xtz_pool - b /\
    token_contract = token_contract' /\
    ops = Cons (Xfer (P'0or_'0pair_address_'0pair_address_nat'1'1_address'1 (Left (token_owner, (st.self, token_sold)))) 0 token_contract)
                (Cons (Xfer (PUnit ()) b receipient)
                  Nil)
     |}

let cpmm_pre =
  parse_predicate
    {|
  predicate pre (c : ctx) =
    let token_pool, (xtz_pool, token_contract) = c.cpmm_store in
    let token_ledger, approval = c.fa_store in
    token_contract = fa /\
    approval[cpmm] = const false /\
    token_pool <= token_ledger[cpmm]
     |}

let cpmm_post =
  parse_predicate
    {|
  predicate post (st : step) (p : (nat, (address, address))) (c : ctx) (c' : ctx) =
    let token_pool, (xtz_pool, token_contract) = c.cpmm_store in
    let token_pool', (xtz_pool', token_contract') = c'.cpmm_store in
    let token_ledger, approval = c.fa_store in
    let token_ledger', approval' = c'.fa_store in
    token_contract' = fa /\
    approval'[cpmm] = const false /\
    token_pool' <= token_ledger'[cpmm]
     |}

let fa_spec =
  parse_predicate
    {|
  predicate spec (st : step) (p : (or (address, (address, nat)) address)) (s : (map address nat, map address (map address bool))) (ops : list operation) (s' : (map address nat, map address (map address bool))) =
    let (ledger, approval) = s in
    let (ledger', approval') = s' in
    match p with
    | Left (_from, (_to, _val)) ->
      approval = approval' /\
      (let l = ledger[_from <- ledger[_from] - _val] in ledger' = l[_to <- l[_to] + _val]) /\
      (not (_from = st.sender || approval[_from][st.sender]) || not (ledger[_from] >= _val) -> false) /\
      ops = Nil
    | Right _spender ->
      ledger = ledger' /\
      approval[st.sender <- approval[st.sender][_spender <- true]] = approval' /\
      ops = Nil
    end
     |}

let fa_pre = parse_predicate {|
  predicate pre (c : ctx) = true
 |}

let fa_post =
  parse_predicate
    {|
  predicate post (st : step) (p : (or (address, (address, nat)) address)) (c : ctx) (c' : ctx) =
    c.cpmm_store = c'.cpmm_store /\
    fa_spec st p c.fa_store Nil c'.fa_store
     |}

let d_inv_pre =
  parse_predicate
    {|
predicate inv_pre (c : ctx) =
  let token_pool, (xtz_pool, token_contract) = c.cpmm_store in
  let token_ledger, approval = c.fa_store in
  token_contract = fa /\
  approval[cpmm] = const false /\
  token_pool <= token_ledger[cpmm]
     |}

let d_inv_post =
  parse_predicate
    {|
predicate inv_post (c : ctx) (c' : ctx) =
  let token_pool, (xtz_pool, token_contract) = c.cpmm_store in
  let token_pool', (xtz_pool', token_contract') = c'.cpmm_store in
  let token_ledger, approval = c.fa_store in
  let token_ledger', approval' = c'.fa_store in
  token_contract' = fa /\
  approval'[cpmm] = const false /\
  token_pool' <= token_ledger'[cpmm]
|}

let dexter_desc =
  let open Gen_mlw in
  {
    d_contracts =
      [
        {
          cn_name = "cpmm";
          cn_param_ty = Sort.(S_pair (S_nat, S_pair (S_address, S_address)));
          cn_store_ty = Sort.(S_pair (S_nat, S_pair (S_nat, S_address)));
          cn_num_kont = 2;
          cn_index = 0;
          cn_spec = cpmm_spec;
          cn_pre = cpmm_pre;
          cn_post = cpmm_post;
        };
        {
          cn_name = "fa";
          cn_param_ty =
            Sort.(
              S_or (S_pair (S_address, S_pair (S_address, S_nat)), S_address));
          cn_store_ty =
            Sort.(
              S_pair
                ( S_map (S_address, S_nat),
                  S_map (S_address, S_map (S_address, S_bool)) ));
          cn_num_kont = 0;
          cn_index = 0;
          cn_spec = fa_spec;
          cn_pre = fa_pre;
          cn_post = fa_post;
        };
      ];
    d_inv_pre;
    d_inv_post;
  }

(* let mlw_file = Gen_mlw.file dexter_desc *)

let mlw_file = Gen_mlw.file @@ Translator.parse_file "test/dexter_c.mlw"
let () = Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file
let config : Whyconf.config = Whyconf.init_config None
let main : Whyconf.main = Whyconf.get_main config
let libdir = Whyconf.libdir main
let datadir = Whyconf.datadir main
let env : Env.env = Env.create_env ("./whyml/stdlib" :: Whyconf.loadpath main)
let mods = Typing.type_mlw_file env [] "myfile.mlw" mlw_file
