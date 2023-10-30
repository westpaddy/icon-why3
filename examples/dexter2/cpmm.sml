<< ContractAnnot %add_liquidity
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let ((owner, min_lqt_minted), (max_tokens_deposited, deadline)) = p in
  lqt_address <> "tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU" &&
  lqt_address' = lqt_address &&
  let lqt_minted = lqt_total' - lqt_total in
  match o, contract_opt %transfer token_address, contract_opt %mintOrBurn lqt_address with
  | [Transfer<list (pair address (list (pair address (pair nat nat))))> _ _ tkc; Transfer<pair int address> (q, _) _ lqc], Some tkc', Some lqc' ->
      q = lqt_minted && tkc = tkc' && lqc = lqc'
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %remove_liquidity
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let ((to_, lqt_burned), (min_xtz_withdrawn, (min_tokens_withdrawn, deadline))) = p in
  lqt_address <> "tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU" &&
  lqt_address' = lqt_address &&
  lqt_total' + lqt_burned = lqt_total &&
  match o, contract_opt %mintOrBurn lqt_address, contract_opt %transfer token_address, contract_opt to_ with
  | [Transfer<pair int address> (q, _) _ lqc; Transfer<list (pair address (list (pair address (pair nat nat))))> _ _ tkc; Transfer<unit> _ _ xtc], Some lqc', Some tkc', Some xtc' ->
      lqc = lqc' && tkc = tkc' && xtc = xtc' &&
      q = 0 - lqt_burned
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %xtz_to_token
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let (to_, (min_tokens_bought, deadline)) = p in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  match o, contract_opt %transfer token_address with
  | [Transfer<list (pair address (list (pair address (pair nat nat))))> _ _ tkc], Some tkc' ->
      tkc = tkc'
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %token_to_xtz
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let ((to_, tokens_sold), (min_xtz_bought, deadline)) = p in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  match o, contract_opt %transfer token_address, contract_opt to_ with
  | [Transfer<list (pair address (list (pair address (pair nat nat))))> _ _ tkc; Transfer<unit> _ _ xtc], Some tkc', Some xtc' ->
      tkc = tkc' && xtc = xtc'
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %token_to_token
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let ((output_dexter_contract, min_tokens_bought), (to_, (tokens_sold, deadline))) = p in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  match o, contract_opt %transfer token_address, contract_opt %xtz_to_token output_dexter_contract with
  | [Transfer<list (pair address (list (pair address (pair nat nat))))> _ _ tkc; Transfer<pair address (pair nat timestamp)> _ _ ttc], Some tkc', Some ttc' ->
      tkc = tkc' && ttc = ttc'
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %set_baker
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  let (baker, freeze_baker) = p in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  match o with
  | [SetDelegate _] -> True
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %set_manager
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  o = []
} &
{ e | True }
>>

<< ContractAnnot %set_lqt_address
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  lqt_address = "tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU" &&
  lqt_address' = p &&
  lqt_total' = lqt_total &&
  o = []
} &
{ e | True }
>>

<< ContractAnnot %update_token_pool
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  match o, contract_opt %balance_of token_address with
  | [Transfer<pair (list (pair address nat)) (contract (list (pair (pair address nat) nat)))> _ _ tkc], Some tkc' ->
      tkc = tkc'
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %update_token_pool_internal
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  o = []
} &
{ e | True }
>>

<< ContractAnnot %default
{ (p, s) | True } ->
{ (o, s') |
  let (((token_pool, xtz_pool), (lqt_total, self_is_updating_token_pool)),
       ((freeze_baker, manager), (token_address, (token_id, lqt_address)))) = s in
  let (((token_pool', xtz_pool'), (lqt_total', self_is_updating_token_pool')),
       ((freeze_baker', manager'), (token_address', (token_id', lqt_address')))) = s' in
  lqt_address' = lqt_address &&
  lqt_total' = lqt_total &&
  o = []
} &
{ e | True }
>>
