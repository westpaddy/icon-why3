<< Measure tok_total (x : big_map address nat) : nat =
match x with
| EmptyMap -> 0
| Bind  _ n tl -> n + tok_total tl
>>

<< ContractAnnot %transfer
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (address_from, (address_to, value)) = p in
  total_supply' = total_supply &&
  admin' = admin &&
  o = [] &&
  let from_balance = match find_opt_b address_from tokens with Some n -> n | None -> 0 in
  let from_balance = from_balance - value in
  from_balance >= 0 &&
  let from_balance = abs from_balance in
  let maybe_from_balance = if from_balance = 0 then None else Some from_balance in
  let tokens = update_b address_from maybe_from_balance tokens in
  let to_balance = match find_opt_b address_to tokens with Some n -> n | None -> 0 in
  let to_balance = to_balance + value in
  let maybe_to_balance = if to_balance = 0 then None else Some to_balance in
  tokens' = update_b address_to maybe_to_balance tokens
} &
{ e | True }
>>

<< ContractAnnot %approve
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (spender, target) = p in
  total_supply' = total_supply &&
  admin' = admin &&
  o = []
} &
{ e | True }
>>

<< ContractAnnot %mintOrBurn
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (quantity, target) = p in
  sender = admin &&
  let old_balance = match find_opt_b target tokens with Some n -> n | None -> 0 in
  old_balance + quantity >= 0 &&
  total_supply' = abs (total_supply + quantity) &&
  admin' = admin &&
  o = [] &&
  let old_balance = match find_opt_b target tokens with Some n -> n | None -> 0 in
  old_balance + quantity >= 0 &&
  let new_balance = old_balance + quantity in
  new_balance >= 0 &&
  let new_balance = abs new_balance in
  let maybe_new_balance = if new_balance = 0 then None else Some new_balance in
  tokens' = update_b target maybe_new_balance tokens
} &
{ e | True }
>>

<< ContractAnnot %getAllowance
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (_, callback) = p in
  total_supply' = total_supply &&
  admin' = admin &&
  match o with
  | [Transfer _ _ c] -> c = callback
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %getBalance
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (_, callback) = p in
  total_supply' = total_supply &&
  admin' = admin &&
  match o with
  | [Transfer _ _ c] -> c = callback
  | _ -> False
} &
{ e | True }
>>

<< ContractAnnot %getTotalSupply
{ (p, s) | True } ->
{ (o, s') |
  let ((tokens, allowances), (admin, total_supply)) = s in
  let ((tokens', allowances'), (admin', total_supply')) = s' in
  let (_, callback) = p in
  total_supply' = total_supply &&
  admin' = admin &&
  match o with
  | [Transfer _ _ c] -> c = callback
  | _ -> False
} &
{ e | True }
>>