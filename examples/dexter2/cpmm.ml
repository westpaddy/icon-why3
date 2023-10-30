(* This is a translation of https://gitlab.com/dexter2tz/dexter2tz/-/blob/master/dexter.mligo  *)

open SCaml

type storage = {
  token_pool : nat;
  xtz_pool : tz;
  lqt_total : nat;
  self_is_updating_token_pool : bool;
  freeze_baker : bool;
  manager : address;
  token_address : address; (* FA2 contract for which exchange *)
  token_id : nat; (* target token ID of the FA2 contract *)
  lqt_address : address; (* FA1.2 contract holding liquidity *)
}

type add_liquidity = {
  owner : address;
  min_lqt_minted : nat;
  max_tokens_deposited : nat;
  deadline : timestamp;
}

type remove_liquidity = {
  to_ : address;
  lqt_burned : nat;
  min_xtz_withdrawn : tz;
  min_tokens_withdrawn : nat;
  deadline : timestamp;
}

type xtz_to_token = {
  to_ : address;
  min_tokens_bought : nat;
  deadline : timestamp;
}

type token_to_xtz = {
  to_ : address;
  tokens_sold : nat;
  min_xtz_bought : tz;
  deadline : timestamp;
}

type set_baker = { baker : key_hash option; freeze_baker : bool }

type token_to_token = {
  output_dexter_contract : address;
  min_tokens_bought : nat;
  to_ : address;
  tokens_sold : nat;
  deadline : timestamp;
}

type update_token_pool_internal = ((address * nat) * nat) list
type balance_of = (address * nat) list * ((address * nat) * nat) list contract

let null_address : address = Address "tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU"
let error_TOKEN_CONTRACT_MUST_HAVE_A_TRANSFER_ENTRYPOINT = Nat 1
(* we change here 0 to 1 because SCaml uses the value [Nat 0] for DIV_by_0 exception. *)

(* Nat 1 *)
let error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE = Nat 2
let error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE = Nat 3

let error_MAX_TOKENS_DEPOSITED_MUST_BE_GREATER_THAN_OR_EQUAL_TO_TOKENS_DEPOSITED
    =
  Nat 4

let error_LQT_MINTED_MUST_BE_GREATER_THAN_MIN_LQT_MINTED = Nat 5

(* Nat 6 *)
(* Nat 7 *)
let error_XTZ_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_BOUGHT = Nat 8
let error_INVALID_TO_ADDRESS = Nat 9
let error_AMOUNT_MUST_BE_ZERO = Nat 10

let error_THE_AMOUNT_OF_XTZ_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_WITHDRAWN
    =
  Nat 11

let error_LQT_CONTRACT_MUST_HAVE_A_MINT_OR_BURN_ENTRYPOINT = Nat 12

let error_THE_AMOUNT_OF_TOKENS_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_WITHDRAWN
    =
  Nat 13

let error_CANNOT_BURN_MORE_THAN_THE_TOTAL_AMOUNT_OF_LQT = Nat 14
let error_TOKEN_POOL_MINUS_TOKENS_WITHDRAWN_IS_NEGATIVE = Nat 15

(* Nat 16 *)
(* Nat 17 *)
let error_TOKENS_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_BOUGHT =
  Nat 18

let error_TOKEN_POOL_MINUS_TOKENS_BOUGHT_IS_NEGATIVE = Nat 19
let error_ONLY_MANAGER_CAN_SET_BAKER = Nat 20
let error_ONLY_MANAGER_CAN_SET_MANAGER = Nat 21
let error_BAKER_PERMANENTLY_FROZEN = Nat 22
let error_ONLY_MANAGER_CAN_SET_LQT_ADRESS = Nat 23
let error_LQT_ADDRESS_ALREADY_SET = Nat 24
let error_CALL_NOT_FROM_AN_IMPLICIT_ACCOUNT = Nat 25

(* Nat 26 *)
(* Nat 27 *)
let error_INVALID_FA2_TOKEN_CONTRACT_MISSING_BALANCE_OF = Nat 28

let error_THIS_ENTRYPOINT_MAY_ONLY_BE_CALLED_BY_GETBALANCE_OF_TOKENADDRESS =
  Nat 29

(* Nat 30 *)
let error_INVALID_INTERMEDIATE_CONTRACT = Nat 31
let error_INVALID_FA2_BALANCE_RESPONSE = Nat 32
let error_UNEXPECTED_REENTRANCE_IN_UPDATE_TOKEN_POOL = Nat 33

let mint_or_burn (s : storage) (target : address) (quantity : int) =
  (* Does this assertion need? Original code doesn't have. *)
  assert (not (s.lqt_address = null_address));
  let lqt_contract =
    match Contract.contract' s.lqt_address "mintOrBurn" with
    | None -> failwith error_LQT_CONTRACT_MUST_HAVE_A_MINT_OR_BURN_ENTRYPOINT
    | Some c -> c
  in
  let param = (quantity, target) in
  Operation.transfer_tokens param (Tz 0.) lqt_contract

let token_transfer (s : storage) (from_ : address) (to_ : address)
    (amount : nat) =
  let token_contract =
    match Contract.contract' s.token_address "transfer" with
    | None -> failwith error_TOKEN_CONTRACT_MUST_HAVE_A_TRANSFER_ENTRYPOINT
    | Some c -> c
  in
  let param = [ (from_, [ (to_, (s.token_id, amount)) ]) ] in
  Operation.transfer_tokens param (Tz 0.) token_contract

let xtz_transfer (to_ : address) (amount : tz) =
  let c =
    match Contract.contract to_ with
    | None -> failwith error_INVALID_TO_ADDRESS
    | Some c -> c
  in
  Operation.transfer_tokens () amount c

let cail_div (n : nat) (m : nat) : nat =
  (* We may be better to use original definition. *)
  nat_of_int (n +^ m -^ Nat 1) /^ m

let[@entry] add_liquidity (p : add_liquidity) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_now () >= p.deadline then
    failwith error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE;
  let xtz_pool : nat = nat_of_mutez s.xtz_pool in
  let nat_amount : nat = nat_of_mutez @@ Global.get_amount () in
  let lqt_minted : nat =
    (* error_DIV_by_0 *)
    nat_amount *^ s.lqt_total /^ xtz_pool
  in
  let tokens_deposited : nat =
    (* error_DIV_by_0 *)
    cail_div (nat_amount *^ s.token_pool) xtz_pool
  in
  if tokens_deposited > p.max_tokens_deposited then
    failwith
      error_MAX_TOKENS_DEPOSITED_MUST_BE_GREATER_THAN_OR_EQUAL_TO_TOKENS_DEPOSITED;
  if lqt_minted < p.min_lqt_minted then
    failwith error_LQT_MINTED_MUST_BE_GREATER_THAN_MIN_LQT_MINTED;
  let s' =
    {
      s with
      lqt_total = s.lqt_total +^ lqt_minted;
      token_pool = s.token_pool +^ tokens_deposited;
      xtz_pool = s.xtz_pool +$ Global.get_amount ();
      (* error_OVERFLOW *)
    }
  in
  let op_token =
    token_transfer s (Global.get_sender ()) Contract.self_address
      tokens_deposited
  in
  let op_lqt = mint_or_burn s p.owner (int_of_nat lqt_minted) in
  ([ op_token; op_lqt ], s')

let[@entry] remove_liquidity (p : remove_liquidity) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_now () >= p.deadline then
    failwith error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  let xtz_withdrawn : tz =
    (* error_DIV_by_0 *)
    (* error_OVERFLOW *)
    mutez_of_nat (p.lqt_burned *^ nat_of_mutez s.xtz_pool /^ s.lqt_total)
  in
  let tokens_withdrawn : nat =
    (* error_DIV_by_0 *) p.lqt_burned *^ s.token_pool /^ s.lqt_total
  in
  if xtz_withdrawn < p.min_xtz_withdrawn then
    failwith
      error_THE_AMOUNT_OF_XTZ_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_WITHDRAWN;
  if tokens_withdrawn < p.min_tokens_withdrawn then
    failwith
      error_THE_AMOUNT_OF_TOKENS_WITHDRAWN_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_WITHDRAWN;
  let lqt_total : nat =
    match isnat (s.lqt_total -^ p.lqt_burned) with
    | None -> failwith error_CANNOT_BURN_MORE_THAN_THE_TOTAL_AMOUNT_OF_LQT
    | Some n -> n
  in
  let token_pool : nat =
    match isnat (s.token_pool -^ tokens_withdrawn) with
    | None -> failwith error_TOKEN_POOL_MINUS_TOKENS_WITHDRAWN_IS_NEGATIVE
    | Some n -> n
  in
  let s' =
    (* error_OVERFLOW *)
    { s with token_pool; xtz_pool = s.xtz_pool -$ xtz_withdrawn; lqt_total }
  in
  let op_lqt =
    mint_or_burn s (Global.get_sender ()) (Int 0 - int_of_nat p.lqt_burned)
  in
  let op_token =
    token_transfer s Contract.self_address p.to_ tokens_withdrawn
  in
  let op_xtz = xtz_transfer p.to_ xtz_withdrawn in
  ([ op_lqt; op_token; op_xtz ], s')

let[@entry] xtz_to_token (p : xtz_to_token) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_now () >= p.deadline then
    failwith error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE;
  let xtz_pool : nat = nat_of_mutez s.xtz_pool in
  let nat_amount : nat = nat_of_mutez @@ Global.get_amount () in
  let tokens_bought : nat =
    (* error_DIV_by_0 *)
    nat_amount *^ Nat 997 *^ s.token_pool
    /^ ((xtz_pool *^ Nat 1000) +^ (nat_amount *^ Nat 997))
  in
  if tokens_bought < p.min_tokens_bought then
    failwith
      error_TOKENS_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_TOKENS_BOUGHT;
  let token_pool : nat =
    match isnat (s.token_pool -^ tokens_bought) with
    | None -> failwith error_TOKEN_POOL_MINUS_TOKENS_BOUGHT_IS_NEGATIVE
    | Some n -> n
  in
  let s' =
    (* error_OVERFLOW *)
    { s with xtz_pool = s.xtz_pool +$ Global.get_amount (); token_pool }
  in
  let op = token_transfer s Contract.self_address p.to_ tokens_bought in
  ([ op ], s')

let[@entry] token_to_xtz (p : token_to_xtz) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_now () >= p.deadline then
    failwith error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  let xtz_bought : tz =
    (* error_DIV_by_0 *)
    mutez_of_nat
    @@ p.tokens_sold *^ Nat 997 *^ nat_of_mutez s.xtz_pool
       /^ ((s.token_pool *^ Nat 1000) +^ (p.tokens_sold *^ Nat 997))
  in
  if xtz_bought < p.min_xtz_bought then
    failwith error_XTZ_BOUGHT_MUST_BE_GREATER_THAN_OR_EQUAL_TO_MIN_XTZ_BOUGHT;
  let s' =
    (* error_OVERFLOW *)
    {
      s with
      token_pool = s.token_pool +^ p.tokens_sold;
      xtz_pool = s.xtz_pool -$ xtz_bought;
    }
  in
  let op_token =
    token_transfer s (Global.get_sender ()) Contract.self_address p.tokens_sold
  in
  let op_tez = xtz_transfer p.to_ xtz_bought in
  ([ op_token; op_tez ], s')

let[@entry] default (() : unit) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  let s' =
    (* error_OVERFLOW *)
    { s with xtz_pool = s.xtz_pool +$ Global.get_amount () }
  in
  ([], s')

let[@entry] set_baker (p : set_baker) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  if Global.get_sender () <> s.manager then
    failwith error_ONLY_MANAGER_CAN_SET_BAKER;
  if s.freeze_baker then failwith error_BAKER_PERMANENTLY_FROZEN;
  let s' = { s with freeze_baker = p.freeze_baker } in
  let op = Operation.set_delegate p.baker in
  ([ op ], s')

let[@entry] set_manager (p : address) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  if Global.get_sender () <> s.manager then
    failwith error_ONLY_MANAGER_CAN_SET_MANAGER;
  let s' = { s with manager = p } in
  ([], s')

let[@entry] set_lqt_address (p : address) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  if Global.get_sender () <> s.manager then
    failwith error_ONLY_MANAGER_CAN_SET_LQT_ADRESS;
  if s.lqt_address <> null_address then failwith error_LQT_ADDRESS_ALREADY_SET;
  let s' = { s with lqt_address = p } in
  ([], s')

let[@entry] update_token_pool (() : unit) (s : storage) =
  if Global.get_sender () <> Global.get_source () then
    failwith error_CALL_NOT_FROM_AN_IMPLICIT_ACCOUNT;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  if s.self_is_updating_token_pool then
    failwith error_UNEXPECTED_REENTRANCE_IN_UPDATE_TOKEN_POOL;
  let s' = { s with self_is_updating_token_pool = true } in
  let cfmm_update_token_pool_internal : update_token_pool_internal contract =
    (* This [Option.get] never fails. *)
    Option.get
    @@ Contract.contract' Contract.self_address "update_token_pool_internal"
  in
  let token_balance_of : balance_of contract =
    match Contract.contract' s.token_address "balance_of" with
    | None -> failwith error_INVALID_FA2_TOKEN_CONTRACT_MISSING_BALANCE_OF
    | Some c -> c
  in
  let p =
    ([ (Contract.self_address, s.token_id) ], cfmm_update_token_pool_internal)
  in
  let op = Operation.transfer_tokens p (Tz 0.) token_balance_of in
  ([ op ], s')

let[@entry] update_token_pool_internal (p : update_token_pool_internal)
    (s : storage) =
  if
    (not s.self_is_updating_token_pool)
    || Global.get_sender () <> s.token_address
  then
    failwith
      error_THIS_ENTRYPOINT_MAY_ONLY_BE_CALLED_BY_GETBALANCE_OF_TOKENADDRESS;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  let token_pool : nat =
    match p with
    | [] -> failwith error_INVALID_FA2_BALANCE_RESPONSE
    | (_, x) :: _ -> x
  in
  let s' = { s with token_pool; self_is_updating_token_pool = false } in
  ([], s')

let[@entry] token_to_token (p : token_to_token) (s : storage) =
  if s.self_is_updating_token_pool then
    failwith error_SELF_IS_UPDATING_TOKEN_POOL_MUST_BE_FALSE;
  if Global.get_amount () > Tz 0. then failwith error_AMOUNT_MUST_BE_ZERO;
  if Global.get_now () >= p.deadline then
    failwith error_THE_CURRENT_TIME_MUST_BE_LESS_THAN_THE_DEADLINE;
  let xtz_bought : tz =
    (* error_OVERFLOW *)
    mutez_of_nat
    @@ p.tokens_sold *^ Nat 997 *^ nat_of_mutez s.xtz_pool
       /^ ((s.token_pool *^ Nat 1000) +^ (p.tokens_sold *^ Nat 997))
  in
  let s' =
    (* error_OVERFLOW *)
    {
      s with
      token_pool = s.token_pool +^ p.tokens_sold;
      xtz_pool = s.xtz_pool -$ xtz_bought;
    }
  in
  let op1 =
    token_transfer s (Global.get_sender ()) Contract.self_address p.tokens_sold
  in
  let c2 =
    match Contract.contract' p.output_dexter_contract "xtz_to_token" with
    | None -> failwith error_INVALID_INTERMEDIATE_CONTRACT
    | Some c -> c
  in
  let p2 : xtz_to_token =
    {
      to_ = p.to_;
      min_tokens_bought = p.min_tokens_bought;
      deadline = p.deadline;
    }
  in
  let op2 = Operation.transfer_tokens p2 xtz_bought c2 in
  ([ op1; op2 ], s')
