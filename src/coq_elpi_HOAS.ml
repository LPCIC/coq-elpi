(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
open API.Data
module E = API.Extend.Data
module CD = struct
  include API.Extend.CData
  include API.Extend.Data.C
end
module U = API.Extend.Utils
module P = API.Extend.Pp
module CC = API.Extend.Compile
module CS = API.Extend.CustomState
module C = Constr
module EC = EConstr
open Names
module G = GlobRef
open Coq_elpi_utils

let debug = false

(* ************************************************************************ *)
(* ****************** HOAS of Coq terms and goals ************************* *)
(* See also coq-term.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, isname, nameout, name =
  let open CD in
  let { cin; isc; cout } as name  = declare {
    data_name = "Name.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "`%s`" (Pp.string_of_ppcmds (Name.print x)));
    data_eq = (fun _ _ -> true);
    data_hash = (fun _ -> 0);
    data_hconsed = false;
  } in
  cin, isc, cout, name
;;
let in_elpi_name x = E.mkCData (namein x)

let is_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n -> isname n
  | _ -> false

let in_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n when isname n -> nameout n
  | E.CData n when CD.is_string n ->
     let s = CD.to_string n in
     if s = "_" then Name.Anonymous
     else Name.Name (Id.of_string s)
  | E.Discard -> Name.Anonymous
  | (E.UVar _ | E.AppUVar _) -> Name.Anonymous
  | _ -> err Pp.(str"Not a name: " ++ str (P.Raw.show_term t))

let in_coq_annot ~depth t = Context.make_annot (in_coq_name ~depth t) Sorts.Relevant

(* universes *)
let univin, isuniv, univout, univ =
  let open CD in
  let { cin; isc; cout } as univ = declare {
    data_name = "Univ.Universe.t";
    data_pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (Univ.Universe.pr x) in
      let l = string_split_on_char '.' s in
      let s = match List.rev l with
        | x :: y :: _ -> y ^ "." ^ x
        | _ -> s in
      Format.fprintf fmt "«%s»" s);
    data_eq = Univ.Universe.equal;
    data_hash = Univ.Universe.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, univ
;;
let sprop  = E.Constants.from_string "sprop"
let prop   = E.Constants.from_string "prop"
let typc   = E.Constants.from_stringc "typ"
let sortc  = E.Constants.from_stringc "sort"
let in_elpi_sort s =
  E.mkApp
    sortc
    (match s with
    | Sorts.SProp -> sprop
    | Sorts.Prop -> prop
    | Sorts.Set ->
        E.mkApp typc (E.mkCData (univin Univ.type0_univ)) []
    | Sorts.Type u -> E.mkApp typc (E.mkCData (univin u)) [])
    []

let in_elpi_flex_sort t = E.mkApp sortc (E.mkApp typc t []) []

(* constants *)
let grin, isgr, grout, gref =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "GlobRef.t";
    data_pp = (fun fmt x ->
     Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global x)));
    data_eq = Names.GlobRef.equal;
    data_hash = (*G.Ordered.hash;*)Hashtbl.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;
let indtc  = E.Constants.from_stringc "indt"
let indcc  = E.Constants.from_stringc "indc"
let constc = E.Constants.from_stringc "const"
let in_elpi_gr r =
  let open Globnames in
  match r with
  | (VarRef _ | ConstRef _) -> E.mkApp constc (E.mkCData (grin r)) []
  | IndRef _ -> E.mkApp indtc (E.mkCData (grin r)) []
  | ConstructRef _ -> E.mkApp indcc (E.mkCData (grin r)) []


let mpin, ismp, mpout, modpath =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "ModPath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;
let mptyin, istymp, mptyout, modtypath =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "ModTypePath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;

let in_elpi_modpath ~ty mp = E.mkCData (if ty then mptyin mp else mpin mp)
let is_modpath ~depth t =
  match E.look ~depth t with E.CData x -> ismp x | _ -> false
let is_modtypath ~depth t =
  match E.look ~depth t with E.CData x -> istymp x | _ -> false
let in_coq_modpath ~depth t =
  match E.look ~depth t with
  | E.CData x when ismp x -> mpout x
  | E.CData x when istymp x -> mptyout x
  | _ -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ constants (app, lam, ...) ****************************************** *)
(* binders *)
let lamc   = E.Constants.from_stringc "lam"
let in_elpi_lam n s t = E.mkApp lamc (in_elpi_name n) [s;E.mkLam t]

let prodc  = E.Constants.from_stringc "prod"
let in_elpi_prod n s t = E.mkApp prodc (in_elpi_name n) [s;E.mkLam t]

let letc   = E.Constants.from_stringc "let"
let in_elpi_let n b s t = E.mkApp letc (in_elpi_name n) [s;b;E.mkLam t]

(* other *)
let appc   = E.Constants.from_stringc "app"
let in_elpi_app_Arg ~depth hd args =
    match E.look ~depth hd, args with
    | E.Const c, [] -> assert false
    | E.Const c, x :: xs -> E.mkApp c x xs
    | E.App(c,x,xs), _ -> E.mkApp c x (xs@args)
    | _ -> assert false
    
let in_elpi_appl hd (args : E.term list) =
  if args = [] then hd
  else E.mkApp appc (U.list_to_lp_list (hd :: args)) []
let in_elpi_app hd (args : E.term array) =
  in_elpi_appl hd (Array.to_list args)

let matchc = E.Constants.from_stringc "match"
let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let fixc   = E.Constants.from_stringc "fix"
let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

(* implicit *)
let holec   = E.Constants.from_stringc "hole"
let in_elpi_hole = E.mkConst holec

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

let command_mode_cc =
  CC.State.declare ~name:"coq-elpi:command-mode-compiler"
    ~init:(fun () -> true)
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)
let command_mode =
  CS.declare ~name:"coq-elpi:command-mode"
    ~init:(CS.CompilerState (command_mode_cc, fun x -> x))
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)

let command_mode = CS.get command_mode 
let cc_set_command_mode s b = CC.State.set command_mode_cc s b

type state = Compile of CC.State.t | Run of CS.t

module CoqEngine_HOAS : sig 

  type elpi_evar =
    | QueryArg of string * E.constant
    | UnifVar of E.uvar_body * int
  val pp_elpi_evar : Format.formatter -> elpi_evar -> unit
  val show_elpi_evar : elpi_evar -> string

  module ElpiEvarMap : sig
    type t
    val empty : t
    val add : elpi_evar -> Evar.t -> t -> t
    val find : elpi_evar -> t -> Evar.t
    val fold : E.solution -> t -> (depth:int -> E.term -> Evar.t -> 'a -> 'a) -> 'a -> 'a
    val find_value : E.solution -> t -> elpi_evar -> E.term
    val filter : alive:Evar.Set.t -> t -> t

    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

  type coq_engine  = {
   env : Environ.env; (* global env *)
   evd : Evd.evar_map; (* universe constraints *)

   (* Coq's evar -> Elpi's UVar/Arg *)
   coq2elpi : elpi_evar Evar.Map.t;

   (* Elpi's UVar/Arg -> Coq's evar *)
   elpi2coq : ElpiEvarMap.t;

   (* If the query is solve, then one argument is new list of goals *)
   new_goals : elpi_evar option;
  }
  val pp_coq_engine : Format.formatter -> coq_engine -> unit
  val show_coq_engine : coq_engine -> string

  val engine : coq_engine CS.component
  val engine_cc : coq_engine CC.State.component

  val empty_from_env : Environ.env -> coq_engine
  val empty_from_env_evd : Environ.env -> Evd.evar_map -> coq_engine

  val get_engine : state -> coq_engine
  val set_engine : state -> coq_engine -> state

  val cs_get_engine : CS.t -> coq_engine
  val cs_set_engine : CS.t -> coq_engine -> CS.t
  val cc_get_engine : CC.State.t -> coq_engine
  val cc_set_engine : CC.State.t -> coq_engine -> CC.State.t

end = struct

  type elpi_evar =
    | QueryArg of string  * E.constant [@printer (fun fmt (s,_)  -> Format.fprintf fmt "%s" s)]
    | UnifVar of E.uvar_body * int [@printer (fun fmt (b,lvl) -> P.term lvl fmt (E.mkUVar b lvl 0))]
    [@@deriving show]

  module ElpiEvarMap = struct
  
    let pp_solution2ev fmt m =
      CString.Map.bindings m |>
      P.list (fun fmt (s,k) ->
        Format.fprintf fmt "%s :-> %s" s Pp.(string_of_ppcmds (Evar.print k))) " "
        fmt 

    let pp_ref2evk =
      P.list (fun fmt (b,(k,lvl)) ->
        Format.fprintf fmt "%a :-> %s" pp_elpi_evar (UnifVar(b,lvl))
        Pp.(string_of_ppcmds (Evar.print k))) " "

    type t = {
      solution2ev : Evar.t CString.Map.t [@printer pp_solution2ev];
      ref2evk : (E.uvar_body * (Evar.t * int)) list [@printer pp_ref2evk];
    }
    [@@deriving show]

    let empty = { solution2ev = CString.Map.empty; ref2evk = [] }
    let add e k m =
      match e with
      | QueryArg (s,_) ->
          { m with solution2ev = CString.Map.add s k m.solution2ev }
      | UnifVar (b,lvl) ->
          { m with ref2evk = (b, (k,lvl)) :: m.ref2evk }
          
    let find e m =
      match e with
      | QueryArg (s,_) -> CString.Map.find s m.solution2ev
      | UnifVar (b,_) -> fst(List.assq b m.ref2evk)
          
    let filter ~alive { solution2ev; ref2evk } =
      {
        solution2ev = CString.Map.filter (fun _ k -> Evar.Set.mem k alive) solution2ev;
        ref2evk = List.filter (fun (_,(k,_)) -> Evar.Set.mem k alive) ref2evk;
      }

    let fold { E.assignments } { solution2ev; ref2evk} f a =
      CString.Map.fold (fun name k a -> 
        f ~depth:0 (StrMap.find name assignments) k a) solution2ev a |>
      List.fold_right (fun (b,(k,lvl)) a ->
        f ~depth:lvl (E.mkUVar b lvl 0) k a) ref2evk
       
    let find_value { E.assignments } m = function
      | QueryArg (name,_) -> (StrMap.find name assignments)
      | UnifVar (b,_) -> (E.mkUVar b (snd (List.assq b m.ref2evk)) 0)

  end


 type coq_engine = {
   env : Environ.env [@printer (fun _ _ -> ())];
   evd : Evd.evar_map [@printer (fun fmt m ->
     Format.fprintf fmt "%s" Pp.(string_of_ppcmds (Termops.pr_evar_map None (Global.env()) m)))];
   coq2elpi : elpi_evar Evar.Map.t [@printer (fun fmt m ->
     P.list (fun fmt (k,e) -> Format.fprintf fmt "%s :-> %a" Pp.(string_of_ppcmds (Evar.print k)) pp_elpi_evar e) " " fmt (Evar.Map.bindings m)
     )];
   elpi2coq : ElpiEvarMap.t;
   new_goals : elpi_evar option;
 }
 [@@deriving show]

 let empty_from_env_evd env evd =
   {
     env;
     evd;
     coq2elpi = Evar.Map.empty;
     elpi2coq = ElpiEvarMap.empty;
     new_goals = None;
   }

 let empty_from_env env = empty_from_env_evd env (Evd.from_env env)

 let init () = empty_from_env (Global.env ())

  let engine_cc : coq_engine CC.State.component =
   CC.State.declare ~name:"coq-elpi:evmap-compiler-state" ~init ~pp:pp_coq_engine

 let engine : coq_engine CS.component =
   CS.declare ~name:"coq-elpi:evmap-constraint-type" ~pp:pp_coq_engine
     ~init:(CS.CompilerState(engine_cc,fun t -> (*{ t with ev2arg = None }*)t))

 let get_engine = function
   | Run state ->  CS.get engine state
   | Compile state -> CC.State.get engine_cc state

 let set_engine state e =
   match state with
   | Run state -> Run (CS.set engine state e)
   | Compile state -> Compile (CC.State.set engine_cc state e)

let cs_get_engine s = CS.get engine s
let cs_set_engine s = CS.set engine s

let cc_get_engine s = CC.State.get engine_cc s
let cc_set_engine s = CC.State.set engine_cc s


end

open CoqEngine_HOAS

let section_ids env =
    let named_ctx = Environ.named_context env in
    Context.Named.fold_inside
      (fun acc x -> Context.Named.Declaration.get_id x :: acc)
      ~init:[] named_ctx

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : EConstr.t -> elpi ******************************************* *)

let rec pos name cur = function
  | [] -> None
  | Name n :: _ when Names.Id.equal n name -> Some cur
  | Name _ :: xs -> pos name (cur+1) xs
  | Anonymous :: xs -> pos name cur xs


let cc_get_evd s = (CC.State.get engine_cc s).evd
let cs_get_evd s = (CS.get engine s).evd

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"


let cc_get_env state = (CC.State.get engine_cc state).env

let get_evd s = (get_engine s).evd
let get_env s = (get_engine s).env

let declare_evc = E.Constants.from_stringc "declare-evar"

let info_of_evar ~env ~evd ~section k =
  let open Context.Named in
  let { Evd.evar_concl } as info =
    Evarutil.nf_evar_info evd (Evd.find evd k) in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  let ctx = EC.named_context_of_val filtered_hyps in
  let ctx = ctx |> List.filter (fun x ->
    not(CList.mem_f Id.equal (Declaration.get_id x) section)) in
  evar_concl, ctx, Environ.reset_with_named_context filtered_hyps env

(* ******************************************* *)
(*  <---- depth ---->                          *)
(*  proof_ctx |- pis \ t                       *)
(* ******************************************* *)

type coq_proof_ctx_names = Name.t list * int

let declc = E.Constants.from_stringc "decl"
let defc = E.Constants.from_stringc "def"
let evarc = E.Constants.from_stringc "evar"

let mk_elpi_evar name_hint state =
  match state with
  | Run _ as state ->
     let b = E.fresh_uvar_body () in
     state, UnifVar (b,0)
  | Compile state ->
     (* Not sure this is what we always want *)
     let state, name, t = CC.fresh_Arg ~name_hint ~args:[] state in
     (* HACK, fix API in elpi *)
     let c =
       match E.look ~depth:0 t with
       | E.Const c -> c
       | _ -> assert false in
     Compile state, QueryArg (name, c)

let cc_mk_elpi_evar name_hint state =
  let state, ev = mk_elpi_evar name_hint (Compile state) in
  match state with
  | Compile s -> s, ev
  | Run _ -> assert false

let in_elpi_app_evar ev l =
  match ev, l with
  | QueryArg (_,c), [] -> E.mkConst c
  | QueryArg (_,c), x::xs -> E.mkApp c x xs
  | UnifVar (b,lvl), [] -> E.mkUVar b lvl 0
  | UnifVar (b,lvl), l -> E.mkAppUVar b lvl l

let mk_pi_arrow hyp rest =
  E.mkApp E.Constants.pic (E.mkLam (E.mkApp E.Constants.implc hyp [rest])) []

let mk_decl ~depth name ~ty =
  E.mkApp declc E.(mkConst depth) [in_elpi_name name; ty]

let mk_def ~depth name ~bo ~ty ~ctx_len state =
  let state, ev = mk_elpi_evar "norm" state in
  let norm = in_elpi_app_evar ev (CList.init ctx_len E.mkConst) in
  state, E.mkApp defc E.(mkConst depth) [in_elpi_name name; ty; bo; norm]

let cc_mk_def ~depth name ~bo ~ty ~ctx_len state =
  let state, t = mk_def ~depth name ~bo ~ty ~ctx_len (Compile state) in
  match state with
  | Run _ -> assert false
  | Compile state -> state, t

(* Maps a Coq name (bound in the context) to its De Bruijn level
 * The type (and optionally body) is given by the hyps. Each hyp is generated
 * at a depth level, and it may need to be pushed down. Cfr:
 *
 *  pi x\ decl x t => py y\ def y t b => ....
 *  pi x y\ decl x t => def y t b => ....
 *
 * Given that a priori you may not know the size of the context things are
 * generated in the first form, and eventually lifted down. *)
type hyp = { ctx_entry : E.term; depth : int }
type coq2lp_ctx = { coq_name2dbl : int Id.Map.t; hyps : hyp list }

let empty_coq2lp_ctx = { coq_name2dbl = Id.Map.empty; hyps = [] }

let push_coq2lp_ctx ~depth n ctx_entry ctx = {
  coq_name2dbl = Id.Map.add n depth ctx.coq_name2dbl;
  hyps = { ctx_entry ; depth = depth + 1 } :: ctx.hyps
}

let pp_coq2lp_ctx fmt { coq_name2dbl; hyps } =
  Id.Map.iter (fun name d ->
    Format.fprintf fmt "@[%s |-> %a@]" (Id.to_string name)
      (Elpi_API.Extend.Pp.term d) (E.mkConst d))
    coq_name2dbl;
  Format.fprintf fmt "@[<hov>";
  List.iter (fun { ctx_entry; depth } ->
    Format.fprintf fmt "%a@ "
      (Elpi_API.Extend.Pp.term depth) ctx_entry)
    hyps
;;

let rec constr2lp (proof_ctx, proof_ctx_len) ~calldepth ~depth state t =
  assert(depth >= proof_ctx_len);
  let { evd } = get_engine state in
  let gls = ref [] in
  let rec aux ~depth state t = match EC.kind evd t with
    | C.Rel n -> state, E.mkConst (depth - n)
    | C.Var n ->
         state, begin match pos n 0 proof_ctx with
         | Some i -> E.mkConst i
         | None -> in_elpi_gr (G.VarRef n)
         end
    | C.Meta _ -> nYI "constr2lp: Meta"
    | C.Evar (k,args) ->
        (* the evar is created at the depth the conversion is called, not at
          the depth at which it is found *)
         let state, elpi_evar, gsl_t = in_elpi_evar ~calldepth k state in
         gls := gsl_t @ !gls;          
         let section_len = List.length (section_ids (get_engine state).env) in
         let args = Array.sub args 0 (Array.length args - section_len) in
         let state, args = CArray.fold_left_map (aux ~depth) state args in
         state, in_elpi_app_evar elpi_evar (CArray.rev_to_list args)
    | C.Sort s -> state, in_elpi_sort (EC.ESorts.kind evd s)
    | C.Cast (t,_,ty) ->
         let state, t = aux ~depth state t in
         let state, ty = aux ~depth state ty in
         let state, self = aux ~depth:(depth+1) state (EC.mkRel 1) in
         state, in_elpi_let Names.Name.Anonymous t ty self
    | C.Prod(n,s,t) ->
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_prod n.Context.binder_name s t
    | C.Lambda(n,s,t) ->
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_lam n.Context.binder_name s t
    | C.LetIn(n,b,s,t) ->
         let state, b = aux ~depth state b in
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_let n.Context.binder_name b s t
    | C.App(hd,args) ->
         let state, hd = aux ~depth state hd in
         let state, args = CArray.fold_left_map (aux ~depth) state args in
         state, in_elpi_app hd args
    | C.Const(c,i) ->
         check_univ_inst (EC.EInstance.kind evd i);
         let ref = G.ConstRef c in
         if G.equal ref (Coqlib.lib_ref "elpi.hole") then state, in_elpi_hole
         else state, in_elpi_gr (G.ConstRef c)
    | C.Ind(ind,i) ->
         check_univ_inst (EC.EInstance.kind evd i);
         state, in_elpi_gr (G.IndRef ind)
    | C.Construct(construct,i) ->
         check_univ_inst (EC.EInstance.kind evd i);
         state, in_elpi_gr (G.ConstructRef construct)
    | C.Case((*{ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs }*)_,
             rt,t,bs) ->
         let state, t = aux ~depth state t in
         let state, rt = aux ~depth state rt in
         let state, bs = CArray.fold_left_map (aux ~depth) state bs in
         state,
         in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt 
           (Array.to_list bs)
    | C.Fix(([| rarg |],_),([| name |],[| typ |], [| bo |])) ->
         let state, typ = aux ~depth state typ in
         let state, bo = aux ~depth:(depth+1) state bo in
         state, in_elpi_fix name.Context.binder_name rarg typ bo
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | C.Proj _ -> nYI "HOAS for primitive projections"
    | C.Int _ -> nYI "HOAS for primitive machine integers"
  in
  if debug then
    Feedback.msg_debug Pp.(str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pr_sequence Name.print proof_ctx ++
      str " term=" ++Printer.pr_econstr_env (get_env state) (get_evd state) t);
  let state, t = aux ~depth state t in
  if debug then
    Feedback.msg_debug Pp.(str"term2lp (out): " ++
      str (pp2string (P.term depth) t));
  state, t, !gls

and in_elpi_ctx ~calldepth state ctx ?(mk_ctx_item=mk_pi_arrow) kont =
  let open Context.Named.Declaration in
  let gls = ref [] in
  let rec aux ~depth (ctx, ctx_len as ctx_w_len) coq2lp_ctx state = function
    | [] ->
        let coq2lp_ctx = { coq2lp_ctx with hyps = List.rev coq2lp_ctx.hyps } in
        let state, t, gls_t = kont (ctx, ctx_len) coq2lp_ctx ~depth state in
        gls := gls_t @ !gls;
        state, t
    | LocalAssum (Context.{binder_name=coq_name}, ty) :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state ty in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let coq2lp_ctx = push_coq2lp_ctx ~depth coq_name hyp coq2lp_ctx in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux ~depth:(depth+1) ctx_w_len coq2lp_ctx state rest in
        state, mk_ctx_item hyp rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state ty in
        let state, bo, gls_bo = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let state, hyp = mk_def ~depth name ~bo ~ty ~ctx_len state in
        let coq2lp_ctx = push_coq2lp_ctx ~depth coq_name hyp coq2lp_ctx in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux ~depth:(depth+1) ctx_w_len coq2lp_ctx state rest in
        state, mk_ctx_item hyp rest
  in
    let state, t = aux ~depth:calldepth ([],0) empty_coq2lp_ctx state (List.rev ctx) in
    state, t, !gls

and in_elpi_evar_concl evar_concl elpi_evar (_, ctx_len as ctx) ~scope { hyps } ~calldepth ~depth state =
  let state, evar_concl, gls_evar_concl = constr2lp ctx ~calldepth ~depth state evar_concl in
  let args = CList.init scope E.mkConst in
  let hyps = List.map (fun { ctx_entry; depth = from } ->
    U.move ~from ~to_:depth ctx_entry) hyps in
  state, U.list_to_lp_list hyps, (in_elpi_app_evar elpi_evar args), evar_concl, gls_evar_concl

and in_elpi_evar_info ~calldepth ~env ~evd ctx elpi_evar evar_concl state =
  in_elpi_ctx ~calldepth state ctx (fun (ctx, ctx_len) coq2lp_ctx ~depth state ->
    let state, hyps, ev, ty, gls =
      in_elpi_evar_concl evar_concl elpi_evar (ctx,ctx_len) ~scope:ctx_len coq2lp_ctx
        ~calldepth ~depth state in
    state, E.mkApp declare_evc hyps [ev; ty], gls)

and in_elpi_evar ~calldepth k state =
  if debug then Feedback.msg_debug Pp.(str"in_elpi_evar:" ++ Evar.print k);
  let { coq2elpi; elpi2coq; evd; env } as e = get_engine state in
  try
    let elpi_evar = Evar.Map.find k coq2elpi in
    if debug then Feedback.msg_debug Pp.(str"in_elpi_evar: known " ++
      Evar.print k ++ str" as " ++ str(show_elpi_evar elpi_evar));
    state, elpi_evar, []
  with Not_found ->
    let name_hint = Option.cata Names.Id.to_string "G" (Evd.evar_ident k evd) in
    let state, elpi_evar = mk_elpi_evar name_hint state in
    let coq2elpi = Evar.Map.add k elpi_evar coq2elpi in
    let elpi2coq = ElpiEvarMap.add elpi_evar k elpi2coq in
    let state = set_engine state { e with coq2elpi; elpi2coq } in
    if debug then Feedback.msg_debug Pp.(str"in_elpi_evar: unknown " ++ Evar.print k);
    let evar_concl, ctx, _ = info_of_evar ~env ~evd ~section:(section_ids env) k in
    let state, evar_decl, gls = in_elpi_evar_info ~calldepth ~env ~evd ctx elpi_evar evar_concl state in
    if debug then Feedback.msg_debug Pp.(str"in_elpi_evar: new decl " ++
      str(pp2string (P.term calldepth) evar_decl));
    state, elpi_evar, gls @ [evar_decl]
;;
(* CHECK *)

let cc_in_elpi_ctx ~calldepth state ctx ?mk_ctx_item kont =
  let kont c c2lp ~depth s =
    match s with
    | Compile state -> 
        let state, t, gls = kont c c2lp ~depth state in
        Compile state, t, gls
    | Run _ -> assert false in
  let state, t, gls =
    in_elpi_ctx ~calldepth (Compile state) ctx ?mk_ctx_item kont in
  match state with
  | Compile state -> state, t, gls
  | Run _ -> assert false

let cc_in_elpi_evar ~calldepth k state =
  let state, ev, gls = in_elpi_evar ~calldepth k (Compile state) in
  match state with
  | Compile state -> state, ev, gls
  | Run _ -> assert false

let cc_in_elpi_evar_concl evar_concl elpi_evar ctx ~scope hyps ~calldepth ~depth state =
  let state, hyps, ev, ty, gls =
    in_elpi_evar_concl evar_concl elpi_evar ctx ~scope hyps ~calldepth ~depth (Compile state) in
  match state with
  | Compile state -> state, hyps, ev, ty, gls
  | Run _ -> assert false


(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let in_coq_hole () =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "elpi.hole"))

let add_constraints state c = CS.update engine state (fun ({ evd } as x) ->
  { x with evd = Evd.add_universe_constraints evd c })

let new_univ state =
  CS.update_return engine state (fun ({ evd } as x) ->
    let evd, v = Evd.new_univ_level_variable UState.UnivRigid evd in
    let u = Univ.Universe.make v in
    let evd = Evd.add_universe_constraints evd
        (UnivProblem.Set.singleton (UnivProblem.ULe (Univ.type1_univ,u))) in
    { x with evd }, u)

let type_of_global state r = CS.update_return engine state (fun x ->
  let ty, ctx = Typeops.type_of_global_in_context x.env r in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let evd = Evd.merge_context_set Evd.univ_rigid x.evd ctx in
  { x with evd }, EConstr.of_constr ty)

let body_of_constant state c = CS.update_return engine state (fun x ->
  match Global.body_of_constant_body (Environ.lookup_constant c x.env) with
  | Some (bo, ctx) ->
     let inst, ctx = UnivGen.fresh_instance_from ctx None in
     let bo = Vars.subst_instance_constr inst bo in
     let evd = Evd.merge_context_set Evd.univ_rigid x.evd ctx in
     { x with evd }, Some (EConstr.of_constr bo)
  | None -> x, None)

let new_evar info state =
  CS.update_return engine state (fun ({ evd } as x) ->
     let evd, k = Evd.new_evar evd info in
     { x with evd }, k)

let evar_arity k state =
  let { Evd.evar_hyps } = Evd.find (CS.get engine state).evd k in
  List.length (Environ.named_context_of_val evar_hyps)

let minimize_universes sol =
  let state = CS.update engine sol.E.state (fun ({ evd } as x) ->
    { x with evd = Evd.minimize_universes evd }) in
  { sol with E.state }

let is_sort ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[_;_]) -> prodc == s
  | _ -> false

let is_globalc x = x == constc || x == indtc || x == indcc

exception Undeclared_evar of int (*depth*) * E.term

let pp_cst fmt { E.goal = (depth,concl); context } =
  Format.fprintf fmt "%d |> %a |- %a" depth
    (P.list (fun fmt { E.hdepth; E.hsrc } ->
        Format.fprintf fmt "%d:%a" hdepth (P.term hdepth) hsrc) ", ")
      context
     (P.term depth) concl

let find_evar var syntactic_constraints x_depth x =
  let is_evar depth t =
    match E.look ~depth t with
    | E.App(c,x,[t;rx]) when c == evarc ->
          Some(E.look ~depth x,E.look ~depth rx,t)
    | _ -> None in
  try
    CList.find_map (fun ({ E.goal = (depth,concl); context } as cst) ->
      if debug then
        Feedback.msg_debug Pp.(str"lp2term: evar: constraint: " ++
          str(pp2string pp_cst cst)); 
      match is_evar depth concl with
      | Some((E.UVar(r,_,_)|E.AppUVar(r,_,_)),_,ty) when r == var ->
          Some (context, (depth,ty))
      | Some(_,(E.UVar(rx,_,_)|E.AppUVar(rx,_,_)),ty) when rx == var ->
          Some (context, (depth,ty))
      | _ -> None) syntactic_constraints
  with Not_found -> raise (Undeclared_evar(x_depth,x))

exception Undeclared_ctx_entry of int (*depth*) * E.term

let nth_name ~depth l n =
  match List.nth l n with
  | Name id -> id
  | Anonymous -> raise (Undeclared_ctx_entry(depth,E.mkConst n))

let get_id = function Name.Anonymous -> Id.of_string "_" | Name x -> x


let rec of_elpi_ctx syntactic_constraints depth hyps state =

  let mk_fresh =
    let i = ref 0 in
    fun n ->
      incr i;
      Name.mk_name
        (Id.of_string_soft
          (Printf.sprintf "_elpi_renamed_%s_%d_" n !i)) in
  let in_coq_fresh_name ~depth name names =
    match in_coq_name ~depth name with
    | Name.Anonymous -> mk_fresh "Anonymous"
    | Name.Name id as x when List.mem x names ->
        mk_fresh (Id.to_string id)
    | x -> x in

  let aux names depth state t =
    lp2constr ~tolerate_undef_evar:false syntactic_constraints names ~depth state t in

  let of_elpi_ctx_entry (names,n_names as proof_ctx) ~depth e state =
    match e with
    | `Decl(name,ty) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty = aux proof_ctx depth state ty in
        state, name, Context.Named.Declaration.LocalAssum(Context.make_annot id Sorts.Relevant,ty)
    | `Def(name,ty,bo) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty = aux proof_ctx depth state ty in
        let state, bo = aux proof_ctx depth state bo in
        state, name, Context.Named.Declaration.LocalDef(Context.make_annot id Sorts.Relevant,bo,ty)
  in

  let select_ctx_entries { E.hdepth = depth; E.hsrc = t } =
    let isConst t = match E.look ~depth t with E.Const _ -> true | _ -> false in
    let destConst t = match E.look ~depth t with E.Const x -> x | _ -> assert false in
    match E.look ~depth t with
    | E.App(c,v,[name;ty]) when c == declc && isConst v ->
       Some (destConst v, depth, `Decl(name,ty))
    | E.App(c,v,[name;ty;bo;_]) when c == defc && isConst v ->
       Some (destConst v, depth, `Def (name,ty,bo))
    | _ ->
        if debug then            
          Feedback.msg_debug Pp.(str "skip entry" ++
            str(pp2string (P.term depth) t));
        None
  in
  let ctx_hyps = CList.map_filter select_ctx_entries hyps in
  let dbl2ctx =
    List.fold_right (fun (i,d,e) m ->
      if Int.Map.mem i m
      then err Pp.(str "Duplicate context entry for " ++
                   str(pp2string (P.term d) (E.mkConst i)))
      else Int.Map.add i (d,e) m)
    ctx_hyps Int.Map.empty in
  
  let rec ctx_entries ctx (n,n_no as proof_ctx) to_restrict state i =
    if i = depth then state, ctx, proof_ctx, to_restrict
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries ctx (n@[Anonymous],n_no+1) (i::to_restrict) state (i+1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        let state, name, e = of_elpi_ctx_entry proof_ctx ~depth:d e state in
        ctx_entries (e::ctx) (n@[name],n_no+1) to_restrict state (i+1)
  in
    ctx_entries [] ([],0) [] state 0

(* ***************************************************************** *)
(* <-- depth -->                                                     *)
(* names |- pis |- t                                                 *)
(*   |        \- lp fresh constans                                   *)
(*   \- proof_ctx                                                    *)
(* ***************************************************************** *)

and lp2constr ~tolerate_undef_evar syntactic_constraints (names,n_names as ctx) ~depth state t =
  let aux = lp2constr ~tolerate_undef_evar syntactic_constraints ctx in
  let aux_lam ~depth s t = match E.look ~depth t with
  | E.Lam t -> aux ~depth:(depth+1) s t
  | E.UVar(r,d,ano) -> aux ~depth:(depth+1) s (E.mkUVar r d (ano+1))
  | E.AppUVar(r,d,args) ->
       aux ~depth:(depth+1) s (E.mkAppUVar r d (List.map (U.move ~from:depth ~to_:(depth+1)) args @ [E.mkConst depth]))
  | _ -> err Pp.(str"HOAS: expecting a lambda, got: " ++
           str(pp2string (P.term depth) t)) in
  match E.look ~depth t with
  | E.App(s,p,[]) when sortc == s && p == prop -> state, EC.mkProp
  | E.App(s,ty,[]) when sortc == s ->
      begin match E.look ~depth ty with
      | E.App(ty,c,[]) when typc == ty ->
          begin match E.look ~depth c with
          | E.CData x when isuniv x -> state, EC.mkType (univout x)
          | E.UVar _ | E.AppUVar _ | E.Discard ->
             let state, t = new_univ state in
             state, EC.mkType t
          | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
          end
      | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
      end
 (* constants *)
  | E.App(c,d,[]) when (indtc == c || indcc == c || constc == c) ->
     begin match E.look ~depth d with
     | E.CData gr when isgr gr ->
         begin match grout gr with
         | G.VarRef x       when constc == c -> state, EC.mkVar x
         | G.ConstRef x     when constc == c -> state, EC.mkConst x
         | G.ConstructRef x when indcc == c -> state, EC.mkConstruct x
         | G.IndRef x       when indtc == c -> state, EC.mkInd x
         | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
        end
     | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
     end
 (* binders *)
  | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
      let name = in_coq_annot ~depth name in
      let state, s = aux ~depth state s in
      let state, t = aux_lam ~depth state t in
      if lamc == c then state, EC.mkLambda (name,s,t)
      else state, EC.mkProd (name,s,t)
  | E.App(c,name,[s;b;t]) when letc == c ->
      let name = in_coq_annot ~depth name in
      let state,s = aux ~depth state s in
      let state,b = aux ~depth state b in
      let state,t = aux_lam ~depth state t in
      state, EC.mkLetIn (name,b,s,t)
      
  | E.Const n ->
                  
     if n == holec then 
       state, in_coq_hole ()
     else if n >= 0 then
       if n < n_names then state, EC.mkVar(nth_name ~depth names n)
       else if n < depth then state, EC.mkRel(depth - n)
       else 
         err Pp.(str"wrong bound variable (BUG):" ++ str (E.Constants.show n))
     else
        err Pp.(str"wrong constant:" ++ str (E.Constants.show n))
 (* app *)
  | E.App(c,x,[]) when appc == c ->
       (match U.lp_list_to_list ~depth x with
       | x :: xs -> 
          let state,x = aux ~depth state x in
          let state,xs = CList.fold_left_map (aux ~depth) state xs in
          state, EC.mkApp (x,Array.of_list xs)
       | _ -> assert false) (* TODO *)
  
  (* match *)
  | E.App(c,t,[rt;bs]) when matchc == c ->
      let state, t = aux ~depth state t in
      let state, rt = aux ~depth state rt in
      let state, bt =
        CList.fold_left_map (aux ~depth) state (U.lp_list_to_list ~depth bs) in
      let ind =
        (* XXX fixme reduction *)
        let { evd } = cs_get_engine state in
        let rec aux t o = match EC.kind evd t with
          | C.Lambda(_,s,t) -> aux t (Some s)
          | _ -> match o with
            | None -> assert false (* wrong shape of rt XXX *)
            | Some t ->
               match safe_destApp evd t with
               | C.Ind i, _ -> fst i
               | _ -> assert false (* wrong shape of rt XXX *)
        in
          aux rt None in
      let ci =
        Inductiveops.make_case_info (CS.get engine state).env ind Sorts.Relevant C.RegularStyle in
      state, EC.mkCase (ci,rt,t,Array.of_list bt)
 (* fix *)
  | E.App(c,name,[rno;ty;bo]) when fixc == c ->
      let name = in_coq_annot ~depth name in
      let state, ty = aux ~depth state ty in
      let state, bo = aux_lam ~depth state bo in
      let rno =
        match E.look ~depth rno with
        | E.CData n when CD.is_int n -> CD.to_int n
        | _ -> err Pp.(str"Not an int: " ++ str (P.Raw.show_term rno)) in
      state, EC.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|]))
  
  (* evar *)
  | (E.UVar (r,lvl,_) | E.AppUVar (r,lvl,_)) as x ->
      let args =
        match x with
        | E.UVar (_,vardepth,ano) ->
             CList.init (vardepth+ano) E.mkConst
        | E.AppUVar (_,vardepth,args) ->
             CList.init vardepth E.mkConst @ args
        | _ -> assert false in
      let elpi_evar = UnifVar (r,lvl) in
      if debug then
        Feedback.msg_debug Pp.(str"lp2term: evar: " ++
          str (pp2string (P.term depth) (E.kool x)));
      begin try
        let ext_key = ElpiEvarMap.find elpi_evar (cs_get_engine state).elpi2coq in

        if debug then
          Feedback.msg_debug Pp.(str"lp2term: evar: already in Coq: " ++
          Evar.print ext_key);

        let state, args = CList.fold_left_map (aux ~depth) state args in
        let args = List.rev args in
        let section_args =
          CList.rev_map EC.mkVar (section_ids (cs_get_engine state).env) in
        let arity = evar_arity ext_key state in
        let ev =
          let all_args = args @ section_args in
          let nargs = List.length all_args in
          if nargs > arity then
            let args1, args2 = CList.chop (nargs - arity) all_args in
            EC.mkApp(EC.mkEvar (ext_key,Array.of_list args2),
                       CArray.rev_of_list args1)
          else EC.mkEvar (ext_key,Array.of_list (args @ section_args)) in
        state, ev
      with Not_found ->
        let context, ty =
          try find_evar r syntactic_constraints depth t 
          with Undeclared_evar _ when tolerate_undef_evar ->
            [], (0, in_elpi_sort Sorts.prop)
        in
        let state, k = declare_evar ~tolerate_undef_evar syntactic_constraints context ty state in
        let state =
          CS.update engine state (fun ({ elpi2coq; coq2elpi } as e) ->
            let elpi2coq = ElpiEvarMap.add elpi_evar k elpi2coq in
            let coq2elpi = Evar.Map.add k elpi_evar coq2elpi in
            { e with elpi2coq; coq2elpi }) in
        if debug then Feedback.msg_debug Pp.(str"lp2term: evar: declared new: " ++
          Evar.print k ++ str" = " ++ str(show_elpi_evar elpi_evar));
        let x =
          (* eta contraction in elpi *)
          let missing = List.length context - List.length args in
          if missing <= 0 then t else 
            match x with
            | E.UVar (r,vardepth,ano) -> E.mkUVar r vardepth (ano+missing)
            | E.AppUVar (r,vardepth,xs) ->
                 let ano = List.length args in
                 let extra = CList.init missing (fun i -> E.mkConst(i+ano)) in
                 E.mkAppUVar r vardepth (xs @ extra)
            | _ -> assert false  
          in
        if debug then Feedback.msg_debug Pp.(str"lp2term: evar: instance: " ++
           str (pp2string (P.term depth) t) ++ str"  ->  " ++
           str (pp2string (P.term depth) x));
        aux ~depth state x
      end

  (* errors *)
  | E.Lam _ ->
       err Pp.(str "out of place lambda: "++
               str (pp2string P.(term depth) t))
  | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))

  (* evar info read back *)

and declare_evar ~tolerate_undef_evar syntactic_constraints ctx (depth_concl,concl) state =
  let state, named_ctx, (names,n_names), to_restrict = (* TODO: honor restrict *)
    of_elpi_ctx syntactic_constraints depth_concl ctx state in
  if debug then
    Feedback.msg_debug Pp.(str"lp2term: evar: new: " ++ int depth_concl ++ str" |> " ++
      pr_sequence Name.print names ++ str" |- " ++
      str(pp2string (P.term depth_concl) concl));
  let state, ty = lp2constr ~tolerate_undef_evar syntactic_constraints (names,n_names) ~depth:depth_concl state concl in
  let named_ctx =
    named_ctx @ EC.named_context (CS.get engine state).env in
  if debug then
    Feedback.msg_debug Pp.(str"lp2term: evar: new: " ++
     let { evd; env } = cs_get_engine state in
     Printer.pr_named_context env evd (Obj.magic named_ctx) ++ str " |- " ++
     Printer.pr_econstr_env (EConstr.push_named_context named_ctx env) evd ty);
  let info = Evd.make_evar (EC.val_of_named_context named_ctx) ty in
  let state, k = new_evar info state in
  if debug then
    Feedback.msg_debug Pp.(str"lp2term: evar: new info: " ++
      Evar.print k ++ str " info= " ++
        let { evd; env } = cs_get_engine state in
        Termops.pr_evar_info env evd info);
  state, k
;;

let lp2constr ~tolerate_undef_evar syntactic_constraints proof_ctx ~depth state t =
  try
    if debug then
      Feedback.msg_debug Pp.(str"lp2term: depth=" ++ int depth ++
        str " ctx=" ++ pr_sequence Name.print (fst proof_ctx) ++
        str " term=" ++ str (pp2string (P.term depth) t));
    let state, t = lp2constr ~tolerate_undef_evar syntactic_constraints proof_ctx ~depth state t in
    if debug then
      Feedback.msg_debug Pp.(str"lp2term: out=" ++ 
        (Printer.pr_econstr_env (cs_get_engine state).env
                                (cs_get_engine state).evd t) ++ str "elpi2coq=" ++ str(ElpiEvarMap.show (cs_get_engine state).elpi2coq));
    state, t
  with
  | Undeclared_evar(x_depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the unification variable " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth fmt t) ",")
          syntactic_constraints))
  | Undeclared_ctx_entry(x_depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the name " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the context:" ++
      prlist_with_sep spc Names.Name.print (fst proof_ctx))

let of_elpi_ctx syntactic_constraints depth hyps state =
  try
    of_elpi_ctx syntactic_constraints depth hyps state
  with
  | Undeclared_evar(x_depth,x) ->
    err Pp.(str"The hypothetical context "++
      str(pp2string P.(list (fun fmt { E.hdepth; hsrc } ->
             term hdepth fmt hsrc) ",") hyps) ++
      str" contains the unification variable " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth fmt t) ",")
          syntactic_constraints))
  | Undeclared_ctx_entry(x_depth,x) ->
      err Pp.(str"The hypothetical context "++
      str(pp2string P.(list (fun fmt { E.hdepth; hsrc } ->
             term hdepth fmt hsrc) ",") hyps) ++
      str" contains the name " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the context")



(* ********************************* }}} ********************************** *)


(*
let cs_get_solution2ev state = (CS.get engine state).solution2ev
*)
let cc_push_env state name =
  let open Context.Rel.Declaration in
  CC.State.update engine_cc state (fun ({ env } as x) ->
     { x with env = Environ.push_rel (LocalAssum(name,C.mkProp)) env })
let cc_pop_env state =
  CC.State.update engine_cc state (fun ({ env } as x) ->
     { x with env = Environ.pop_rel_context 1 env })

let get_global_env_evd state =
  let { env; evd } = CS.get engine state in
  Environ.push_context_set (Evd.universe_context_set evd) env, evd


let set_evd state evd = CS.update engine state (fun x -> { x with evd })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env state =
  let env = Global.env () in
  CS.update engine state (fun _ -> CoqEngine_HOAS.empty_from_env env)



let solvec = E.Constants.from_stringc "solve"
let goalc = E.Constants.from_stringc "goal"
let nablac = E.Constants.from_stringc "nabla"
let goal_namec = E.Constants.from_stringc "goal-name"

let mk_goal hyps ev ty attrs =
  E.mkApp goalc hyps [ev;ty; U.list_to_lp_list attrs]

let in_elpi_solve ?goal_name ~hyps ~ev ~ty ~args ~new_goals =
  let name = match goal_name with None -> Anonymous | Some x -> Name x in
  let name = E.mkApp goal_namec (in_elpi_name name) [] in
  E.mkApp solvec args [E.mkCons (mk_goal hyps ev ty [name]) E.mkNil; new_goals]

let goal2query env evd goal loc ?main args ~in_elpi_arg ~depth:calldepth state =
  if not (Evd.is_undefined evd goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));

  let state = cc_set_command_mode state false in (* tactic mode *)

  let state = cc_set_engine state (empty_from_env_evd env evd) in

  let state, elpi_goal_evar, evar_decls = cc_in_elpi_evar ~calldepth goal state in

  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~evd ~section:(section_ids env) goal in
  let goal_name = Evd.evar_ident goal evd in

  let state, query, gls =
    cc_in_elpi_ctx ~calldepth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp E.Constants.pic (E.mkLam t) [])
     (fun (ctx, ctx_len) coq2lp_ctx ~depth state ->
      match main with
      | None ->
          let state, hyps, ev, goal_ty, gls =
            cc_in_elpi_evar_concl evar_concl elpi_goal_evar
              (ctx, ctx_len) ~scope:ctx_len coq2lp_ctx ~calldepth ~depth state in

          let state, new_goals = cc_mk_elpi_evar "NewGoals" state in
          let state =
            let engine = cc_get_engine state in
            cc_set_engine state { engine with new_goals = Some new_goals } in
          let new_goals = in_elpi_app_evar new_goals (CList.init ctx_len E.mkConst) in
            
          let state, args =
            CList.fold_left_map (in_elpi_arg ~depth goal_env coq2lp_ctx evd) state args in
          let args = U.list_to_lp_list args in
          let q = in_elpi_solve ?goal_name ~hyps ~ev ~ty:goal_ty ~args ~new_goals in
          state, q, gls
      | Some text ->
          let state, q = CC.lp ~depth state loc text in
          state, q, []) in
  let evarmap_query =
    match evar_decls @ gls @ [query] with
    | [] -> assert false
    | [g] -> g
    | x :: xs -> E.mkApp E.Constants.andc x xs in
  
  if debug then
    Feedback.msg_debug Pp.(str"engine: " ++
      str (show_coq_engine (cc_get_engine state)));

  state, (loc, evarmap_query)

let eat_n_lambdas ~depth t upto =
  let open E in
  let rec aux n t =
    if n = upto then t
    else match look ~depth:n t with
      | Lam t -> aux (n+1) t
      | UVar(r,d,a) -> aux (n+1) (mkUVar r d (a+1))
      | AppUVar(r,d,a) -> aux (n+1) (mkAppUVar r d (a@[mkConst n]))
      | _ -> assert false
  in
    aux depth t

let rec get_goal_ref depth t =
  match E.look ~depth t with
  | E.App(c,_,[ev;_;_]) when c == goalc ->
     begin match E.look ~depth ev with
     | (E.UVar(r,lvl,_)|E.AppUVar(r,lvl,_)) -> UnifVar(r,lvl)
     | _ -> err Pp.(str"Not a variable " ++ str(pp2string (P.term depth) ev))
     end
  | E.App(c,g,[]) when c == nablac ->
     begin match E.look ~depth g with
     | E.Lam g -> get_goal_ref (depth+1) g
     | _ -> err Pp.(str"Not a lambda " ++ str(pp2string (P.term depth) g))
     end
  | _ -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) t))

let no_list_given = function
  | E.Discard | E.UVar _ | E.AppUVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let cs_show_engine state = show_coq_engine (cs_get_engine state)

let elpi_solution_to_coq_solution ({ E.assignments; state; constraints } as sol) =
  let { elpi2coq; evd; env } as e = cs_get_engine state in
  
  if debug then
    Feedback.msg_debug Pp.(str"engine in:\n" ++ str (show_coq_engine e));

  let syntactic_constraints = E.constraints constraints in
  let state, unassigned, changed =
    ElpiEvarMap.fold sol elpi2coq (fun ~depth t k (state, unassigned, changed) ->
      match E.look ~depth t with
      | E.UVar(b,lvl,_) | E.AppUVar(b,lvl,_) when (
            let { elpi2coq } = cs_get_engine state in
            try
              let k1 = ElpiEvarMap.find (UnifVar(b,lvl)) elpi2coq in
              Evar.equal k k1
            with
            | Not_found -> false) -> (state, Evar.Set.add k unassigned, changed)
      | _ ->
(* TODO: return a boolean to know if something changed *)
       let _, ctx, _ = info_of_evar ~env ~evd ~section:(section_ids env) k in

       let names, n_names = 
         Context.Named.fold_inside
           (fun (acc,n) x ->
              Name (Context.Named.Declaration.get_id x) :: acc, n+1)
           ~init:([],0) ctx in

      if debug then
        Feedback.msg_debug Pp.(str"solution for "++ Evar.print k ++ str" in ctx=" ++
          pr_sequence Name.print names ++ str" at depth=" ++ int n_names ++ str"<-"++ int depth ++
          str " id term=" ++ str(pp2string (P.term depth) t));

       let t = eat_n_lambdas ~depth t n_names in
      if debug then
        Feedback.msg_debug Pp.(str"lambda-less solution for "++ Evar.print k ++ str" in ctx=" ++
          pr_sequence Name.print names ++ str" at depth=" ++ int n_names ++
          str " is term=" ++ str(pp2string (P.term n_names) t));

       let state, t =
         lp2constr ~tolerate_undef_evar:false
           syntactic_constraints (names, n_names) ~depth:n_names state t in

       let { evd; env } as e = cs_get_engine state in
       
       if debug then
         Feedback.msg_debug Pp.(str"solution for "++ Evar.print k ++ str" is constr=" ++
           Printer.pr_econstr_env env evd t);

       let evd = Evd.define k t evd in

       let unassigned = Evar.Set.union unassigned (Evarutil.undefined_evars_of_term evd t) in
       (* since the order in which we add is not topological*)
       let unassigned = Evar.Set.remove k unassigned in

       cs_set_engine state { e with evd }, unassigned, true)
     (state, Evar.Set.empty, false)
  in
    
    let state = CS.update engine state
      (fun { env; evd; coq2elpi; elpi2coq; new_goals } ->
        { env; evd;
          elpi2coq = ElpiEvarMap.filter ~alive:unassigned elpi2coq;
          coq2elpi = Evar.Map.filter (fun k _ -> Evar.Set.mem k unassigned) coq2elpi;
          new_goals; }
      ) in


  if debug then
    Feedback.msg_debug Pp.(str"engine out:\n" ++ str (cs_show_engine state));

  { sol with E.state }, unassigned, changed
  

let get_declared_goals all_goals ({ E.assignments; state; constraints } as sol) =
   let { elpi2coq; new_goals } = cs_get_engine state in
   match new_goals with
   | None -> all_goals , [] 
   | Some arg_name ->
       let t = ElpiEvarMap.find_value sol elpi2coq arg_name in
       let l, depth = skip_lams ~depth:0 0 t in
       if no_list_given l then all_goals, []
       else
         let l = U.lp_list_to_list ~depth (E.kool l) in
         let declared = List.map (get_goal_ref depth) l in
         let declared = declared |> List.map (fun x ->
           try ElpiEvarMap.find x elpi2coq
           with Not_found ->
              CErrors.anomaly Pp.(str (show_elpi_evar x) ++ str " not part of elpi2coq:\n"++
              str(ElpiEvarMap.show elpi2coq))) in
         let declared_set =
           List.fold_right Evar.Set.add declared Evar.Set.empty in
         declared,
         List.filter (fun x -> not(Evar.Set.mem x declared_set)) all_goals
   (*i
   let evd = (cs_get_engine state).evd in
   (* Purge *)
   let state = cs_set_engine state (empty_from_env_evd env evd) in
   declared_goals, shelved_goals
*)

let tclSOLUTION2EVD solution =
  let solution, undefined_evars, _ = elpi_solution_to_coq_solution solution in
  let declared_goals, shelved_goals =
    get_declared_goals (Evar.Set.elements undefined_evars) solution in
  let open Proofview.Unsafe in
  let open Tacticals.New in
  tclTHENLIST [
    tclEVARS (cs_get_engine solution.E.state).evd;
    tclSETGOALS @@ List.map Proofview.with_empty_state declared_goals;
    Proofview.shelve_goals shelved_goals
  ]


(* {{{ elpi -> Entries.mutual_inductive_entry **************************** *)

(* documentation of the Coq API
 
  Coq < Inductive foo (A : Type) (a : A) : A -> Prop := K : foo A a a.

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
   mind_entry_params =
    [(a, Entries.LocalAssumEntry _UNBOUND_REL_1);
     (A, Entries.LocalAssumEntry Type@{Top.1})];
   mind_entry_inds =
    [{Entries.mind_entry_typename = foo;
      mind_entry_arity = _UNBOUND_REL_2 -> Prop; mind_entry_template = false;
      mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1 _UNBOUND_REL_1]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry Top.1 |= ;
   mind_entry_private = None}

  Coq < Inductive bar (n m : nat) : Prop := K (_ : bar n (S m)).

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
   mind_entry_params =
    [(m, Entries.LocalAssumEntry nat); (n, Entries.LocalAssumEntry nat)];
   mind_entry_inds =
    [{Entries.mind_entry_typename = bar; mind_entry_arity = Prop;
      mind_entry_template = false; mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 (S _UNBOUND_REL_1) ->
        _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry ;
   mind_entry_private = None}
*
*)

let parameterc = E.Constants.from_stringc "parameter"
let constructorc = E.Constants.from_stringc "constructor"
let inductivec = E.Constants.from_stringc "inductive"
let coinductivec = E.Constants.from_stringc "coinductive"
let recordc = E.Constants.from_stringc "record"
let fieldc = E.Constants.from_stringc "field"
let end_recordc = E.Constants.from_stringc "end-record"

type record_field_spec = { name : string; is_coercion : bool }

let force_name =
  let n = ref 0 in      
  function
  | Name.Name x -> x
  | _ ->
     incr n; Id.of_string (Printf.sprintf "_missing_parameter_name_%d_" !n)

let force_name_ctx =
  let open Context in
  let open Rel.Declaration in
  List.map (function
    | LocalAssum(n,t) -> LocalAssum (map_annot (fun n -> Name (force_name n)) n, t)
    | LocalDef(n,b,ty) -> LocalDef(map_annot (fun n -> Name (force_name n)) n, b, ty))
;;

let lp2inductive_entry ~depth _hyps sol t =
  let open E in let open Entries in
  let hyps = [] in
let lp2constr ~tolerate_undef_evar ~depth hyps solution t =
  let state, t =
    lp2constr ~tolerate_undef_evar (E.constraints solution.E.constraints)
      ([],0) ~depth solution.E.state t in
  state, t
  in

  (* turns a prefix of the arity (corresponding to the non-uniform parameters)
   * into a context *)
  let decompose_nu_arity evd arity nupno msg =
    let ctx, rest = EC.decompose_prod_assum evd arity in
    let n = Context.Rel.length ctx in
    if n < nupno then err Pp.(int nupno ++
      str" non uniform parameters declared, but only " ++ int n ++
      str " products found in " ++ str msg);
    let unpctx = CList.lastn nupno ctx in
    let ctx = CList.firstn (n - nupno) ctx in
    let nuparams = force_name_ctx unpctx in
    nuparams, EC.it_mkProd_or_LetIn rest ctx in

  (* To check if all constructors share the same context of non-uniform
   * parameters *)
  let rec cmp_nu_ctx evd k ~arity_nuparams:c1 c2 =
    let open Context.Rel.Declaration in
    match c1, c2 with
    | [], [] -> ()
    | LocalAssum (n1, t1) :: c1, LocalAssum (n2, t2) :: c2 ->
        if not (EC.eq_constr_nounivs evd (EC.Vars.lift 1 t1) t2) && 
           not (EC.isEvar evd t2) then
          err Pp.(str"in constructor " ++ Id.print k ++
            str" the type of " ++
            str"non uniform argument " ++ Name.print n2.Context.binder_name ++
            str" is different from the type declared in the inductive"++
            str" type arity as " ++ Name.print n1.Context.binder_name);
      cmp_nu_ctx evd k ~arity_nuparams:c1 c2
    | (LocalDef _ :: _, _) | (_, LocalDef _ :: _) ->
        err Pp.(str "let-in not supported here")
    | _ -> assert false in

  let aux_construtors depth params nupno arity itname finiteness sol ks =

    let params = force_name_ctx params in
    let paramno = List.length params in

    (* decode constructors' types *)
    let sol, names_ktypes =
      CList.fold_left_map (fun sol t ->
        match look ~depth t with
        | App(c,name,[ty]) when c == constructorc ->
            begin match look ~depth name with
            | CData name when CD.is_string name ->
              let name = Id.of_string (CD.to_string name) in
              let state, ty = lp2constr ~tolerate_undef_evar:false ~depth hyps sol ty in
              { sol with E.state }, (name, ty)
            | _ -> err Pp.(str"@gref expected: "  ++
                 str (pp2string P.(term depth) name))
            end
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth) t)))
      sol ks in
    let knames, ktypes = List.split names_ktypes in 

    let env, evd = get_global_env_evd sol.E.state in

    (* Handling of non-uniform parameters *)
    let arity, nuparams, ktypes =
      if nupno = 0 then arity, [], ktypes
      else
        let nuparams, arity =
          decompose_nu_arity evd arity nupno "inductive type arity" in
        let replace_nup name t =
          let cur_nuparams, t =
            decompose_nu_arity evd t nupno
              (" constructor " ^ Id.to_string name) in
          cmp_nu_ctx evd name ~arity_nuparams:nuparams cur_nuparams;
          t
         in
        let ktypes = List.map2 replace_nup knames ktypes in
        arity, nuparams, ktypes in

    (* Relocation to match Coq's API.
     * From
     *  Params, Ind, NuParams |- ktys
     * To
     *  Ind, Params, NuParams |- ktys
     *)
    let ktypes = ktypes |> List.map (fun t ->
      let subst = CList.init (nupno + paramno + 1) (fun i ->
        if i < nupno then EC.mkRel (i+1)
        else if i = nupno then
          let ind = EC.mkRel (nupno + paramno + 1) in
          if paramno = 0 then ind
          else
            let ps =
              CArray.init paramno (fun i -> EC.mkRel (nupno + paramno - i)) in
            EC.mkApp (ind,ps)
        else EC.mkRel i) in
      EC.Vars.substl subst t
    ) in

    let params = nuparams @ params in

    let sol = minimize_universes sol in
    let ktypes = List.map (EC.to_constr evd) ktypes in
    let open Context.Rel.Declaration in
    let params = List.map (function
      | LocalAssum (x, t) -> LocalAssum(x, EC.to_constr evd t)
      | LocalDef (x, t, b) -> LocalDef(x, EC.to_constr evd t, EC.to_constr evd b))
      params in
    let arity = EC.to_constr evd arity in
    let used =
      List.fold_left (fun acc t ->
          Univ.LSet.union acc
            (EConstr.universes_of_constr evd (EConstr.of_constr t)))
        (EConstr.universes_of_constr evd (EConstr.of_constr arity)) ktypes in
    let used =
      List.fold_left (fun acc -> function
        | (LocalDef(_,t,b)) ->
          Univ.LSet.union acc
           (Univ.LSet.union
            (EConstr.universes_of_constr evd (EConstr.of_constr t))
            (EConstr.universes_of_constr evd (EConstr.of_constr b)))
        | (LocalAssum(_,t)) ->
          Univ.LSet.union acc
            (EConstr.universes_of_constr evd (EConstr.of_constr t)))
        used params in
    let evd = Evd.restrict_universe_context evd used in
    
    let oe = {
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_template = false;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes } in
    sol, {
      mind_entry_record = None;
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes =
        Monomorphic_entry (Evd.universe_context_set evd);
      mind_entry_variance = None;
      mind_entry_private = None; }
  in
  let rec aux_fields depth ind fields =
    match E.look ~depth fields with
    | App(c,coercion,[n; ty; fields]) when c == fieldc ->
      begin match E.look ~depth n, E.look ~depth fields with
      | CData name, Lam fields when CD.is_string name ->
        let open API.Extend.BuiltInPredicate in
        (* HACK for tt, we should not use = but rather [unspec bool] that is
           not in this file ... *)
        let _, tt, _ = Elpi_builtin.bool.embed ~depth hyps sol true in
        let fs, tf = aux_fields (depth+1) ind fields in
        let name = CD.to_string name in
        { name; is_coercion = coercion = tt } :: fs,
          in_elpi_prod (in_coq_name ~depth n) ty tf
      | _ -> err Pp.(str"field/end-record expected: "++
                   str (pp2string P.(term depth) fields))
      end
    | Const c when c == end_recordc -> [], ind
    | _ ->  err Pp.(str"field/end-record expected: "++ 
                 str (pp2string P.(term depth) fields))
  in

  let rec aux_decl depth params sol t =
    match E.look ~depth t with
    | App(c,name,[ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_annot ~depth name in
        let state, ty = lp2constr ~tolerate_undef_evar:false ~depth hyps sol ty in
        let open Context.Rel.Declaration in
        aux_lam depth (LocalAssum(name,ty) :: params) { sol with E.state } decl
    | App(c,name,[nupno;arity;ks])
      when (c == inductivec || c == coinductivec) ->
      begin match E.look ~depth name, E.look ~depth nupno  with
      | CData name, CData nupno when CD.is_string name && CD.is_int nupno ->
        let name = Id.of_string (CD.to_string name) in
        let nupno = CD.to_int nupno in
        let fin =
          if c == inductivec then Declarations.Finite
          else Declarations.CoFinite in
        let state, arity = lp2constr ~tolerate_undef_evar:false ~depth hyps sol arity in
        begin match E.look ~depth ks with
        | Lam t -> 
            let ks = U.lp_list_to_list ~depth:(depth+1) t in
            let sol, idecl = 
              aux_construtors (depth+1) params nupno arity name fin
                { sol with E.state } ks in
            sol.E.state, (idecl, None)
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) ks))
        end
      | _ -> err Pp.(str"@id and int expected, got: "++ 
                 str (pp2string P.(term depth) name) ++ str " " ++
                 str (pp2string P.(term depth) nupno))
      end
    | App(c,name,[arity;kn;fields]) when c == recordc ->
      begin match E.look ~depth name, E.look ~depth kn with
      | CData name, CData kname when CD.is_string name && CD.is_string kname ->
        let state, arity = lp2constr ~tolerate_undef_evar:false ~depth hyps sol arity in
        let name = Id.of_string (CD.to_string name) in
        let fields = U.move ~from:depth ~to_:(depth+1) fields in
        (* We simulate the missing binders for the inductive *)
        let ind = E.mkConst depth in
        let depth = depth + 1 in
        let fields_names_coercions, kty = aux_fields depth ind fields in
        let k = [mkApp constructorc kn [kty]] in
        let sol, idecl =
          aux_construtors depth params 0 arity name Declarations.Finite
            { sol with E.state } k in
        sol.E.state, (idecl, Some fields_names_coercions)
      | _ -> err Pp.(str"@id expected, got: "++ 
                 str (pp2string P.(term depth) name))
      end
    | _ -> err Pp.(str"(co)inductive/record expected: "++ 
                 str (pp2string P.(term depth) t))
  and aux_lam depth params sol t =
    match E.look ~depth t with
    | Lam t -> aux_decl (depth+1) params sol t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) t))
                    
  in
    aux_decl depth [] sol t

(* ********************************* }}} ********************************** *)
(* ****************************** API ********************************** *)

let get_current_env_evd ~depth hyps solution =
(* TODO: cahe longer env in coq_engine for later reuse, use == on hyps+depth? *)
  let solution, _, changed = elpi_solution_to_coq_solution solution in

  let syntatic_constraints = E.constraints solution.E.constraints in
(* TODO  let state = in_coq_solution solution in *)
  let state = solution.E.state in
  let state, named_ctx, proof_context, _to_restrict =
    of_elpi_ctx syntatic_constraints depth hyps state in

  let { env; evd } = CS.get engine state in
(*
  Feedback.msg_debug Pp.(str "ctx: " ++
    Printer.pr_named_context env evd (Obj.magic named_ctx));
*)

  let env = EC.push_named_context named_ctx env in
(*
  let state = CS.set engine lp2c_state.state { state with env } in
  let env, evd = get_global_env_evd state in
*)
  state, env, evd, proof_context


let cc_constr2lp ~coq_proof_ctx_names ~depth state t =
  let state = Compile state in
  match constr2lp coq_proof_ctx_names ~calldepth:depth ~depth state t with
  | Compile state, t, gls -> state, mkApp (E.mkConst E.Constants.andc) (t :: gls)
  | Run _, _, _ -> assert false

let constr2lp ~depth hyps solution t =
(* let state, _, _, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in *)
  
  let state, _, coq_proof_ctx_names, _ =
    of_elpi_ctx (E.constraints solution.E.constraints) depth hyps solution.E.state in

  let state = Run state in
  match constr2lp coq_proof_ctx_names ~calldepth:depth ~depth state t with
  | Run state, t, gls -> state, t, gls
  | Compile _, _, _ -> assert false

let lp2constr ~tolerate_undef_evar ~depth hyps solution  t =
  let state, _, _, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in
  let state, t =
    lp2constr ~tolerate_undef_evar (E.constraints solution.E.constraints) coq_proof_ctx_names ~depth state t in
  state, t



(* {{{  Declarations.module_body -> elpi ********************************** *)

let rec in_elpi_module_item path (name, item) = match item with
  | Declarations.SFBconst _ ->
      let c = Constant.make2 path name in
      [in_elpi_gr (Globnames.ConstRef c)]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      let i = (MutInd.make2 path name, 0) in
      [in_elpi_gr (Globnames.IndRef i)]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_module mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_module : 'a.'a Declarations.generic_module_body -> E.term list =
  fun { Declarations.
  mod_mp;             (* Names.module_path *)
  mod_expr;           (* Declarations.module_implementation *)
  mod_type;           (* Declarations.module_signature *)
  mod_type_alg;       (* Declarations.module_expression option *)
  mod_constraints;    (* Univ.ContextSet.t *)
  mod_delta;          (* Mod_subst.delta_resolver *)
  mod_retroknowledge; (* Retroknowledge.action list *)
} ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map (in_elpi_module_item mod_mp) contents)

let rec in_elpi_modty_item (name, item) = match item with
  | Declarations.SFBconst _ ->
      [ Label.to_string name ]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [ Label.to_string name ]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_modty mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_modty : 'a.'a Declarations.generic_module_body -> string list =
  fun { Declarations.mod_type; (* Declarations.modty_signature *) } ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map in_elpi_modty_item contents)

let in_elpi_module (x : Declarations.module_body) = in_elpi_module x

let in_elpi_module_type (x : Declarations.module_type_body) = in_elpi_modty x

(* ********************************* }}} ********************************** *)

(* vim:set foldmethod=marker: *)
