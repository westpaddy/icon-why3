(** tzw program parser *)

open Why3.Ptree
open Error_monad

type entrypoint_params = {
  epp_step : param;
  epp_param : param list;
  epp_old_s : param;
  epp_new_s : param;
  epp_ops : param;
}

type entrypoint = {
  ep_loc : Why3.Loc.position;
  ep_name : ident;
  ep_params : entrypoint_params;
  ep_body : term;
}

type contract = {
  c_name : ident;
  c_store_ty : type_decl;
  c_entrypoints : entrypoint list;
  c_num_kont : int;
  c_pre : logic_decl;
  c_post : logic_decl;
}

type t = {
  tzw_preambles : decl list;
  tzw_postambles : decl list;
  tzw_knowns : contract list;
  tzw_epp : Sort.t list StringMap.t StringMap.t;
      (** contract name ↦ (entrypoint name ↦ sorts of parameters) *)
  tzw_unknown_pre : logic_decl;
  tzw_unknown_post : logic_decl;
}

val parse_mlw : mlw_file -> (t, Error_monad.error list) result
