(** Sorts for the FOL theory used as the assertion language *)

type tyvar = string

type t =
  (* internally used types *)
  | S_var of tyvar
  | S_exception
  (* core data types *)
  | S_string
  | S_nat
  | S_int
  | S_bytes
  | S_bool
  | S_unit
  | S_list of t
  | S_pair of t * t
  | S_option of t
  | S_or of t * t
  | S_set of t
  | S_map of t * t
  | S_big_map of t * t
  | S_lambda of t * t
  (* domain specific data types *)
  | S_timestamp
  | S_mutez
  | S_address
  | S_contract of t
  | S_operation
  | S_key
  | S_key_hash
  | S_signature
  | S_chain_id

(* Other Michelson types but not implemented yet *)
(* | S_never
 * | S_ticket of t
 * | S_bls12_381_g1
 * | S_bls12_381_g2
 * | S_bls12_381_fr
 * | S_sapling_transaction of int
 * | S_sapling_state of int *)

let compare (t1 : t) (t2 : t) = compare t1 t2

(** Pretty printer *)
let rec pp_sort fmt (ty : t) =
  let open Format in
  match ty with
  | S_var v -> fprintf fmt "'%s" v
  | S_exception -> fprintf fmt "exception"
  | S_string -> fprintf fmt "string"
  | S_nat -> fprintf fmt "nat"
  | S_int -> fprintf fmt "int"
  | S_bytes -> fprintf fmt "bytes"
  | S_bool -> fprintf fmt "bool"
  | S_unit -> fprintf fmt "unit"
  | S_list ty -> fprintf fmt "(@[list@ %a@])" pp_sort ty
  | S_pair (ty1, ty2) ->
      fprintf fmt "(@[pair@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_option ty -> fprintf fmt "(@[option@ %a@])" pp_sort ty
  | S_or (ty1, ty2) -> fprintf fmt "(@[or@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_set ty -> fprintf fmt "(@[set@ %a@])" pp_sort ty
  | S_map (ty1, ty2) -> fprintf fmt "(@[map@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_big_map (ty1, ty2) ->
      fprintf fmt "(@[big_map@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_lambda (ty1, ty2) ->
      fprintf fmt "(@[lambda@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_timestamp -> fprintf fmt "timestamp"
  | S_mutez -> fprintf fmt "mutez"
  | S_address -> fprintf fmt "address"
  | S_contract ty -> fprintf fmt "(@[contract@ %a@])" pp_sort ty
  | S_operation -> fprintf fmt "operation"
  | S_key -> fprintf fmt "key"
  | S_key_hash -> fprintf fmt "key_hash"
  | S_signature -> fprintf fmt "signature"
  | S_chain_id -> fprintf fmt "chain_id"

let string_of_sort (ty : t) : string =
  let open Format in
  asprintf "%a"
    (fun ppf ty ->
      (* ignore newlines and indents automatically inserted by pretty printing *)
      pp_set_formatter_out_functions ppf
        {
          (pp_get_formatter_out_functions ppf ()) with
          out_newline = ignore;
          out_indent = ignore;
        };
      pp_sort ppf ty)
    ty

(* let open Format in
 * let buf = Buffer.create 512 in
 * let ppf = formatter_of_buffer buf in
 * pp_set_formatter_out_functions
 *   ppf
 *   {
 *     (pp_get_formatter_out_functions ppf ()) with
 *     out_newline = ignore;
 *     out_indent = ignore;
 *   } ;
 * fprintf ppf "@[%a@]@?" pp_sort ty ;
 * Buffer.contents buf *)

(** [replace_tyvar ty x ty'] replaces the every occurrence of the type
   variable [x] in the sort [ty] with the type [ty']. *)
let replace_tyvar (ty : t) (x : tyvar) (ty' : t) : t =
  let rec aux ty =
    match ty with
    | S_var z when x = z -> ty'
    | S_var _ | S_unit | S_bool | S_int | S_nat | S_string | S_chain_id
    | S_bytes | S_mutez | S_key_hash | S_key | S_signature | S_timestamp
    | S_address | S_operation | S_exception ->
        ty
    | S_option ty -> S_option (aux ty)
    | S_list ty -> S_list (aux ty)
    | S_set ty -> S_set (aux ty)
    | S_contract ty -> S_contract (aux ty)
    | S_or (ty1, ty2) -> S_or (aux ty1, aux ty2)
    | S_pair (ty1, ty2) -> S_pair (aux ty1, aux ty2)
    | S_lambda (ty1, ty2) -> S_lambda (aux ty1, aux ty2)
    | S_map (ty1, ty2) -> S_map (aux ty1, aux ty2)
    | S_big_map (ty1, ty2) -> S_big_map (aux ty1, aux ty2)
  in
  aux ty

let subst_sort (s : (string * t) list) (ty : t) : t =
  List.fold_left (fun ty (x, ty') -> replace_tyvar ty x ty') ty s

module Tyvars = Set.Make (String)

let rec ftv (ty : t) : Tyvars.t =
  match ty with
  | S_var x -> Tyvars.singleton x
  | S_unit | S_bool | S_int | S_nat | S_string | S_chain_id | S_bytes | S_mutez
  | S_key_hash | S_key | S_signature | S_timestamp | S_address | S_operation
  | S_exception ->
      Tyvars.empty
  | S_option ty | S_list ty | S_set ty | S_contract ty -> ftv ty
  | S_or (ty1, ty2)
  | S_pair (ty1, ty2)
  | S_lambda (ty1, ty2)
  | S_map (ty1, ty2)
  | S_big_map (ty1, ty2) ->
      Tyvars.union (ftv ty1) (ftv ty2)
