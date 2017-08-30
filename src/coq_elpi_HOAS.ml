(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module G = Globnames
module E = Elpi_API.Extend.Data
module CD = struct
  include Elpi_API.Extend.CData
  include Elpi_API.Extend.Data.C
end
module R = Elpi_API.Execute
module U = Elpi_API.Extend.Utils
module P = Elpi_API.Extend.Pp
module C = Constr
open Names

(* ************************************************************************ *)
(* ******************** HOAS of Coq terms ********************************* *)
(* See also coq-term.elpi                                                   *)

open Coq_elpi_utils

(* names *)
let namein, isname, nameout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Name.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Nameops.pr_name x)));
    data_eq = (fun _ _ -> true);
    data_hash = (fun _ -> 0);
  } in
  cin, isc, cout
;;
let in_elpi_name x = E.CData (namein x)

(* universes *)
let univin, isuniv, univout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Univ.Universe.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Univ.Universe.pr x)));
    data_eq = Univ.Universe.equal;
    data_hash = Univ.Universe.hash;
  } in
  cin, isc, cout
;;
let prop   = E.Constants.from_string "prop"
let typc   = E.Constants.from_stringc "typ"
let sortc  = E.Constants.from_stringc "sort"
let in_elpi_sort s =
  E.App(sortc,
    (match s with
    | Sorts.Prop Sorts.Null -> prop
    | Sorts.Prop Sorts.Pos -> E.App(typc,E.CData (univin Univ.type0_univ),[])
    | Sorts.Type u -> E.App(typc,E.CData (univin u),[])), [])
let in_elpi_flex_sort t = E.App(sortc, E.App(typc, t, []), [])

(* constants *)
let grin, isgr, grout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Globnames.global_reference";
    data_pp = (fun fmt x ->
     Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Printer.pr_global x)));
    data_eq = G.eq_gr;
    data_hash = G.RefOrdered.hash;
  } in
  cin, isc, cout
;;
let indtc  = E.Constants.from_stringc "indt"
let indcc  = E.Constants.from_stringc "indc"
let constc = E.Constants.from_stringc "const"
let in_elpi_gr r =
  let open Globnames in
  match r with
  | (VarRef _ | ConstRef _) -> E.App(constc,E.CData (grin r),[])
  | IndRef _ -> E.App(indtc,E.CData (grin r),[])
  | ConstructRef _ -> E.App(indcc,E.CData (grin r),[])

(* binders *)
let lamc   = E.Constants.from_stringc "lam"
let in_elpi_lam n s t = E.App(lamc,in_elpi_name n,[s;E.Lam t])

let prodc  = E.Constants.from_stringc "prod"
let in_elpi_prod n s t = E.App(prodc,in_elpi_name n,[s;E.Lam t])

let letc   = E.Constants.from_stringc "let"
let in_elpi_let n b s t = E.App(letc,in_elpi_name n,[s;b;E.Lam t])

(* other *)
let appc   = E.Constants.from_stringc "app"
let in_elpi_app_Arg hd args =
    match hd, args with
    | E.Const c, [] -> assert false
    | E.Const c, x :: xs -> E.App(c,x,xs)
    | E.App(c,x,xs), _ -> E.App(c,x,xs@args)
    | _ -> assert false
    

let in_elpi_appl hd (args : E.term list) =
  if args = [] then hd
  else E.App(appc,U.list_to_lp_list (hd :: args),[])
let in_elpi_app hd (args : E.term array) =
  in_elpi_appl hd (Array.to_list args)

let matchc = E.Constants.from_stringc "match"
let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.App(matchc,t, [rt; U.list_to_lp_list bs])

let fixc   = E.Constants.from_stringc "fix"
let in_elpi_fix name rno ty bo =
  E.App(fixc,in_elpi_name name,[CD.of_int rno; ty; E.Lam bo])

(* implicit *)
let hole   = E.Constants.from_string "hole"
let in_elpi_implicit = hole

(* axiom *)
let axiom = E.Constants.from_string "axiom"
let in_elpi_axiom = axiom

(* bool *)
let tt = E.Constants.from_string "tt"
let ff = E.Constants.from_string "ff"
let in_elpi_tt = tt
let in_elpi_ff = ff

(* ******************** HOAS : Constr.t -> elpi *****************************)

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"
;;

let constr2lp ~depth t =
  let rec aux ctx t = match C.kind t with
    | C.Rel n -> E.Constants.of_dbl (ctx - n)
    | C.Var n -> in_elpi_gr (G.VarRef n)
    | C.Meta _ -> nYI "HOAS for Meta"
    | C.Evar _ -> nYI "HOAS for Evar"
    | C.Sort s -> in_elpi_sort s
    | C.Cast (t,_,ty) ->
         let t = aux ctx t in
         let ty = aux ctx ty in
         let self = aux (ctx+1) (Constr.mkRel 1) in
         in_elpi_let Names.Name.Anonymous t ty self
    | C.Prod(n,s,t) ->
         let s = aux ctx s in
         let t = aux (ctx+1) t in
         in_elpi_prod n s t
    | C.Lambda(n,s,t) ->
         let s = aux ctx s in
         let t = aux (ctx+1) t in
         in_elpi_lam n s t
    | C.LetIn(n,b,s,t) ->
         let b = aux ctx b in
         let s = aux ctx s in
         let t = aux (ctx+1) t in
         in_elpi_let n b s t
    | C.App(hd,args) ->
         let hd = aux ctx hd in
         let args = Array.map (aux ctx) args in
         in_elpi_app hd args
    | C.Const(c,i) ->
         check_univ_inst i;
         in_elpi_gr (G.ConstRef c)
    | C.Ind(ind,i) ->
         check_univ_inst i;
         in_elpi_gr (G.IndRef ind)
    | C.Construct(construct,i) ->
         check_univ_inst i;
         in_elpi_gr (G.ConstructRef construct)
    | C.Case((*{ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs }*)_,
             rt,t,bs) ->
         let t = aux ctx t in
         let rt = aux ctx rt in
         let bs = Array.(to_list (map (aux ctx) bs)) in
         in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
    | C.Fix(([| rarg |],_),([| name |],[| typ |], [| bo |])) ->
         let typ = aux ctx typ in
         in_elpi_fix name rarg typ (aux (ctx+1) bo)
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | C.Proj _ -> nYI "HOAS for primitive projections"
  in
    aux depth t
;;

(* ********************** HOAS : lp -> Constr.t ************************** *)

let in_coq_name = function
  | E.CData n when isname n -> nameout n
  | E.CData n when CD.is_string n ->
      let s = CD.to_string n in
      if s = "_" then Name.Anonymous else Name.Name (Id.of_string s)
  | (E.UVar (r,_,_) | E.AppUVar(r,_,_))
    when r.E.contents == E.Constants.dummy ->
      Name.Anonymous
  | _ -> err Pp.(str"Not a name")

let new_univ u =
  let u, v = UState.new_univ_variable UState.UnivRigid None u in
  u, Univ.Universe.make v

let is_sort ~depth x =
  match kind depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match kind depth x with
  | E.App(s,_,[_;_]) -> prodc == s
  | _ -> false

let is_globalc x = x == constc || x == indtc || x == indcc

let lp2constr u t =
  let rec aux depth u t = match kind depth t with

    | E.App(s,p,[]) when sortc == s && p == prop -> u, C.mkProp
    | E.App(s,E.App(t,c,[]),[]) when sortc == s && typc == t ->
        begin match kind depth c with
        | E.CData x when isuniv x -> u, C.mkType (univout x)
        | E.UVar _ | E.AppUVar _ ->
           let u, t = new_univ u in
           u, C.mkType t
        | _ -> assert false
        end

    (* constants *)
    | E.App(c,E.CData gr,[]) when indtc == c && isgr gr ->
       let gr = grout gr in
       if not (G.isIndRef gr) then
         err Pp.(str"not an inductive type: " ++ Printer.pr_global gr);
       u, C.mkInd (G.destIndRef gr)
    | E.App(c,E.CData gr,[]) when indcc == c && isgr gr ->
       let gr = grout gr in
       if not (G.isConstructRef gr) then
         err Pp.(str"not a constructor: " ++ Printer.pr_global gr);
       u, C.mkConstruct (G.destConstructRef gr)
    | E.App(c,E.CData gr,[]) when constc == c && isgr gr ->
       begin match grout gr with
       | G.VarRef v -> u, C.mkVar v
       | G.ConstRef v -> u, C.mkConst v
       | x -> err Pp.(str"not a constant: " ++ Printer.pr_global x)
       end

    (* binders *)
    | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
        let name = in_coq_name name in
        let u, s = aux depth u s in
        let u, t = aux_lam depth u t in
        if lamc == c then u, C.mkLambda (name,s,t) else u, C.mkProd (name,s,t)
    | E.App(c,name,[s;b;t]) when letc == c ->
        let name = in_coq_name name in
        let u,s = aux depth u s in
        let u,b = aux depth u b in
        let u,t = aux_lam depth u t in
        u, C.mkLetIn (name,b,s,t)
        
    | E.Const n as c ->
       if c == hole then u, C.mkMeta 0
       else if n >= 0 then
         if n < depth then u, C.mkRel(depth - n)
         else 
           err Pp.(str"wrong bound variable (BUG):" ++ str (E.Constants.show n))
       else
          err Pp.(str"wrong constant:" ++ str (E.Constants.show n))

    (* app *)
    | E.App(c,x,[]) when appc == c ->
         (match U.lp_list_to_list depth x with
         | x :: xs -> 
            let u,x = aux depth u x in
            let u,xs = CList.fold_map (aux depth) u xs in
            u, C.mkApp (x,Array.of_list xs)
         | _ -> assert false) (* TODO *)
    
    (* match *)
    | E.App(c,t,[rt;bs]) when matchc == c ->
        let u, t = aux depth u t in
        let u, rt = aux depth u rt in
        let u, bt = CList.fold_map (aux depth) u (U.lp_list_to_list depth bs) in
        let ind =
          (* XXX fixme reduction *)
          let rec aux t o = match C.kind t with
            | C.Lambda(_,s,t) -> aux t (Some s)
            | _ -> match o with
              | None -> assert false (* wrong shape of rt XXX *)
              | Some t ->
                 match safe_destApp t with
                 | C.Ind i, _ -> fst i
                 | _ -> assert false (* wrong shape of rt XXX *)
          in
            aux rt None in
        let ci =
          Inductiveops.make_case_info (Global.env()) ind C.RegularStyle in
        u, C.mkCase (ci,rt,t,Array.of_list bt)

    (* fix *)
    | E.App(c,name,[rno;ty;bo]) when fixc == c ->
        let name = in_coq_name name in
        let u, ty = aux depth u ty in
        let u, bo = aux_lam depth u bo in
        let rno =
          match kind depth rno with
          | E.CData n when CD.is_int n -> CD.to_int n
          | _ -> err Pp.(str"Not an int: " ++ str (P.Raw.show_term rno)) in
        u, C.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|]))

    (* errors *)
    | (E.UVar _ | E.AppUVar _) as x -> err Pp.(str"unresolved UVar" ++ str (pp2string P.(term depth [] 0 [||]) x))
    | E.Lam _ as x -> err Pp.(str "out of place lambda: "++ str (pp2string P.(term depth [] 0 [||]) x))
    | x -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term x))

  and aux_lam depth u t = match kind depth t with
    | E.Lam t -> aux (depth+1) u t
    | _ -> err Pp.(str"not a lambda")
  in
    aux 0 u t

