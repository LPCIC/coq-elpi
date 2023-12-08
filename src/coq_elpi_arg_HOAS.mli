(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API.RawData
open Coq_elpi_utils

type phase = Interp | Synterp | Both

module Cmd : sig

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term = Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type raw_record_decl = Vernacentries.Preprocessed_Mind_decl.record
type glob_record_decl = Genintern.glob_sign * raw_record_decl
type top_record_decl = Geninterp.interp_sign * glob_record_decl

type raw_indt_decl = Vernacentries.Preprocessed_Mind_decl.inductive
type glob_indt_decl = Genintern.glob_sign * raw_indt_decl
type top_indt_decl = Geninterp.interp_sign * glob_indt_decl

type raw_constant_decl = {
  name : qualified_name;
  atts : Attributes.vernac_flags;
  udecl : Constrexpr.universe_decl_expr option;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
  red : Genredexpr.raw_red_expr option;
}
val pr_raw_constant_decl : Environ.env -> Evd.evar_map -> raw_constant_decl -> Pp.t
type glob_constant_decl = Genintern.glob_sign * raw_constant_decl
type top_constant_decl = Geninterp.interp_sign * glob_constant_decl

type raw_context_decl = Constrexpr.local_binder_expr list
type glob_context_decl = Genintern.glob_sign * raw_context_decl
type top_context_decl = Geninterp.interp_sign * glob_context_decl

type ('a,'b,'c,'d,'e) t =
  | Int : int            -> ('a,'b,'c,'d,'e) t
  | String : string      -> ('a,'b,'c,'d,'e) t
  | Term : 'a            -> ('a,'b,'c,'d,'e) t
  | RecordDecl : 'b      -> ('a,'b,'c,'d,'e) t
  | IndtDecl : 'c        -> ('a,'b,'c,'d,'e) t
  | ConstantDecl : 'd    -> ('a,'b,'c,'d,'e) t
  | Context : 'e         -> ('a,'b,'c,'d,'e) t

type raw  = (raw_term,  raw_record_decl,  raw_indt_decl,  raw_constant_decl,  raw_context_decl)  t
type glob = (glob_term, glob_record_decl, glob_indt_decl, glob_constant_decl, glob_context_decl) t
type top  = (top_term,  top_record_decl,  top_indt_decl,  top_constant_decl,  top_context_decl)  t

val pp_raw : Environ.env -> Evd.evar_map -> raw -> Pp.t
val pp_glob : Environ.env -> Evd.evar_map -> glob -> Pp.t
val pp_top : Environ.env -> Evd.evar_map -> top -> Pp.t

val glob : Genintern.glob_sign -> raw -> glob
val interp : Geninterp.interp_sign -> Environ.env -> Evd.evar_map -> glob -> top
val subst : Mod_subst.substitution -> glob -> glob
 
end

module Tac : sig

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term = Geninterp.interp_sign * Genintern.glob_constr_and_expr

type raw_ltac_term = Constrexpr.constr_expr
type glob_ltac_term = Glob_term.glob_constr
type top_ltac_term = Geninterp.interp_sign * Names.Id.t

type raw_ltac_tactic = Ltac_plugin.Tacexpr.raw_tactic_expr
type glob_ltac_tactic = Ltac_plugin.Tacexpr.glob_tactic_expr
type top_ltac_tactic = Geninterp.Val.t

type ltac_ty = Int | String | Term | List of ltac_ty

type ('a,'f,'t) t =
  | Int : int            -> ('a,'f,'t) t
  | String : string      -> ('a,'f,'t) t
  | Term : 'a            -> ('a,'f,'t) t
  | LTac : ltac_ty * 'f  -> ('a,'f,'t) t
  | LTacTactic : 't  -> ('a,'f,'t) t

type raw =  (raw_term,  raw_ltac_term,  raw_ltac_tactic) t
type glob = (glob_term, glob_ltac_term, glob_ltac_tactic) t
type top =  (top_term,  top_ltac_term,  top_ltac_tactic) t

val subst : Mod_subst.substitution -> glob -> glob
val wit : (raw, glob, top) Genarg.genarg_type

end

val tac : Tac.top_ltac_tactic Elpi.API.Conversion.t
val is_ltac_tactic : Elpi.API.RawOpaqueData.t -> bool
val to_ltac_tactic : Elpi.API.RawOpaqueData.t -> Tac.top_ltac_tactic

(* for tactics *)
val in_elpi_tac :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context ->
  Coq_elpi_HOAS.hyp list ->
  Evd.evar_map ->
  Elpi.API.State.t ->
  Tac.top ->
  Elpi.API.State.t * term list * Elpi.API.Conversion.extra_goals

(* for coercions *)
val in_elpi_tac_econstr :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context ->
  Coq_elpi_HOAS.hyp list ->
  Evd.evar_map ->
  Elpi.API.State.t ->
  EConstr.t ->
  Elpi.API.State.t * term list * Elpi.API.Conversion.extra_goals

(* for commands *)
val in_elpi_cmd :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.empty Coq_elpi_HOAS.coq_context ->
  Elpi.API.State.t ->
  raw:bool ->
  Cmd.top ->
  Elpi.API.State.t * term * Elpi.API.Conversion.extra_goals
val in_elpi_cmd_synterp :
  depth:int -> ?calldepth:int -> 
  Elpi.API.State.t ->
  Cmd.raw ->
  Elpi.API.State.t * term * Elpi.API.Conversion.extra_goals

type coq_arg = Cint of int | Cstr of string | Ctrm of EConstr.t | CLtac1 of Geninterp.Val.t

val in_coq_arg :
  depth:int ->
  Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context ->
  Elpi.API.Data.constraints ->
  Elpi.API.State.t ->
  term ->
    Elpi.API.State.t * coq_arg * Elpi.API.Conversion.extra_goals
