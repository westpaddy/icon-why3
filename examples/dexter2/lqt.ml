open SCaml

type transfer = { address_from : address; address_to : address; value : nat }
type approve = { spender : address; value : nat }
type mintOrBurn = { quantity : int; target : address }
type allowance_key = { owner : address; spender : address }
type getAllowance = { request : allowance_key; callback : nat contract }
type getBalance = { owner : address; callback : nat contract }
type getTotalSupply = { request : unit; callback : nat contract }
type tokens = (address, nat) big_map
type allowances = (allowance_key, nat) big_map

type storage = {
  tokens : tokens;
  allowances : allowances;
  admin : address;
  total_supply : nat;
}

type result = operation list * storage

let maybe (n : nat) : nat option =
  if n = Nat 0 then (None : nat option) else Some n

let[@entry] transfer (param : transfer) (storage : storage) : result =
  let allowances = storage.allowances in
  let tokens = storage.tokens in
  let allowances =
    if Global.get_sender () = param.address_from then allowances
    else
      let allowance_key =
        { owner = param.address_from; spender = Global.get_sender () }
      in
      let authorized_value =
        match BigMap.find allowance_key allowances with
        | Some value -> value
        | None -> Nat 0
      in
      let authorized_value =
        match isnat (authorized_value -^ param.value) with
        | None -> (failwith "NotEnoughAllowance" : nat)
        | Some authorized_value -> authorized_value
      in
      BigMap.update allowance_key (maybe authorized_value) allowances
  in
  let tokens =
    let from_balance =
      match BigMap.find param.address_from tokens with
      | Some value -> value
      | None -> Nat 0
    in
    let from_balance =
      match isnat (from_balance -^ param.value) with
      | None -> (failwith "NotEnoughBalance" : nat)
      | Some from_balance -> from_balance
    in
    BigMap.update param.address_from (maybe from_balance) tokens
  in
  let tokens =
    let to_balance =
      match BigMap.find param.address_to tokens with
      | Some value -> value
      | None -> Nat 0
    in
    let to_balance = to_balance +^ param.value in
    BigMap.update param.address_to (maybe to_balance) tokens
  in
  (([] : operation list), { storage with tokens; allowances })

let[@entry] approve (param : approve) (storage : storage) : result =
  let allowances = storage.allowances in
  let allowance_key =
    { owner = Global.get_sender (); spender = param.spender }
  in
  let previous_value =
    match BigMap.find allowance_key allowances with
    | Some value -> value
    | None -> Nat 0
  in
  if previous_value > Nat 0 && param.value > Nat 0 then
    failwith "UnsafeAllowanceChange"
  else ();
  let allowances = BigMap.update allowance_key (maybe param.value) allowances in
  (([] : operation list), { storage with allowances })

let[@entry] mintOrBurn (param : mintOrBurn) (storage : storage) : result =
  if Global.get_sender () <> storage.admin then failwith "OnlyAdmin" else ();
  let tokens = storage.tokens in
  let old_balance =
    match BigMap.find param.target tokens with None -> Nat 0 | Some bal -> bal
  in
  let new_balance =
    (* [param.quantity] can be negative for burning. *)
    match isnat (int_of_nat old_balance + param.quantity) with
    | None -> (failwith "Cannot burn more than the target's balance." : nat)
    | Some bal -> bal
  in
  let tokens = BigMap.update param.target (maybe new_balance) storage.tokens in
  (* This use of [abs] is ok as far as total_supply is more than each balance. *)
  let total_supply = abs (int_of_nat storage.total_supply + param.quantity) in
  (([] : operation list), { storage with tokens; total_supply })

let[@entry] getAllowance (param : getAllowance) (storage : storage) : result =
  let value =
    match BigMap.find param.request storage.allowances with
    | Some value -> value
    | None -> Nat 0
  in
  ([ Operation.transfer_tokens value (Tz 0.) param.callback ], storage)

let[@entry] getBalance (param : getBalance) (storage : storage) : result =
  let value =
    match BigMap.find param.owner storage.tokens with
    | Some value -> value
    | None -> Nat 0
  in
  ([ Operation.transfer_tokens value (Tz 0.) param.callback ], storage)

let[@entry] getTotalSupply (param : getTotalSupply) (storage : storage) : result
    =
  let total = storage.total_supply in
  ([ Operation.transfer_tokens total (Tz 0.) param.callback ], storage)
