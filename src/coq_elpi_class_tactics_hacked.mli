
open Names
open Evd
open Environ

val takeover : GlobRef.t list ->
  (env ->
   evar_map ->
   int option -> (* depth *)
   bool -> (* unique *)
   best_effort:bool ->
   (evar_map -> Evar.t -> bool) ->
   (bool (*false*) * evar_map) option)
 -> unit