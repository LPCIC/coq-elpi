let init ~paths =  Elpi_parser.init ~paths

let program_ast = Summary.ref ~name:"elpi-decls" []

let load_files s =
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true s in
  program_ast := !program_ast @ new_ast

let load_string s =
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc s;
  close_out oc;
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true [fname] in
  Sys.remove fname;
  program_ast := !program_ast @ new_ast

let exec query =
  let program = Elpi_runtime.program_of_ast !program_ast in
  let query_ast = Elpi_parser.parse_goal query in
  let query = Elpi_runtime.query_of_ast program query_ast in
  let fails = Elpi_runtime.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

module G = Globnames
module E = Elpi_runtime
module C = Constr
open Names

let nYI s =
  CErrors.user_err ~hdr:"elpi" Pp.(str"Not Yet Implemented: " ++ str s)

(* ******************** HOAS of Coq terms ********************************* *)

let grin, isgr, grout =
  let open Elpi_util.CData in
  let { cin; isc; cout } = declare {
      data_name = "Globnames.global_reference";
      data_pp = (fun fmt x ->
        Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Printer.pr_global x)));
      data_eq = G.eq_gr;
      data_hash = G.RefOrdered.hash;
  } in
  cin, isc, cout
let univin, isuniv, univout =
  let open Elpi_util.CData in
  let { cin; isc; cout } = declare {
      data_name = "Univ.Universe.t";
      data_pp = (fun fmt x ->
        Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Univ.Universe.pr x)));
      data_eq = Univ.Universe.equal;
      data_hash = Univ.Universe.hash;
  } in
  cin, isc, cout
let namein, isname, nameout =
  let open Elpi_util.CData in
  let { cin; isc; cout } = declare {
      data_name = "Name.t";
      data_pp = (fun fmt x ->
        Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Nameops.pr_name x)));
      data_eq = Name.equal;
      data_hash = Name.hash;
  } in
  cin, isc, cout

let prop   = E.Constants.from_string "prop"
let typc   = E.Constants.from_stringc "typ"
let sortc  = E.Constants.from_stringc "sort"

let prodc  = E.Constants.from_stringc "prod"
let lamc   = E.Constants.from_stringc "lam"
let letc   = E.Constants.from_stringc "let"

let appc   = E.Constants.from_stringc "app"

let constc = E.Constants.from_stringc "const"
let indtc  = E.Constants.from_stringc "indt"
let indcc  = E.Constants.from_stringc "indc"

let matchc = E.Constants.from_stringc "match"
let fixc   = E.Constants.from_stringc "fix"

let hole   = E.Constants.from_string "hole"

let in_elpi_name x = E.CData (namein x)
let in_elpi_gr r =
  let open Globnames in
  match r with
  | (VarRef _ | ConstRef _) -> E.App(constc,E.CData (grin r),[])
  | IndRef _ -> E.App(indtc,E.CData (grin r),[])
  | ConstructRef _ -> E.App(indcc,E.CData (grin r),[])

let in_elpi_sort s =
  E.App(sortc,
    (match s with
    | Sorts.Prop _ -> prop
    | Sorts.Type u -> E.App(typc,E.CData (univin u),[])), [])
let in_elpi_prod n s t = E.App(prodc,in_elpi_name n,[s;E.Lam t])
let in_elpi_lambda n s t = E.App(lamc,in_elpi_name n,[s;E.Lam t])
let in_elpi_letin n b s t = E.App(letc,in_elpi_name n,[s;b;E.Lam t])
let in_elpi_app hd args = E.App(appc,E.list_to_lp_list (hd ::Array.to_list args),[])
let in_elpi_appl hd args = E.App(appc,E.list_to_lp_list (hd :: args),[])
let in_elpi_match ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs t rt bs =
  E.App(matchc,t, [rt; E.list_to_lp_list (Array.to_list bs)])
let in_elpi_fix name rno bo =
  E.App(fixc,in_elpi_name name,[E.CD.of_int rno; E.Lam bo])
let in_elpi_implicit = hole

(* TODO: universe polymorphism *)
let check_univ_inst univ_inst = assert(Univ.Instance.is_empty univ_inst)

let constr2lp t =
  let rec aux ctx t = match C.kind t with
    | C.Rel n -> E.Constants.of_dbl (List.length ctx - n)
    | C.Var n -> in_elpi_gr (G.VarRef n)
    | C.Meta _ -> assert false
    | C.Evar _ -> assert false
    | C.Sort s -> in_elpi_sort s
    | C.Cast _ -> assert false
    | C.Prod(n,s,t) ->
         let s = aux ctx s in
         let ctx = Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_prod n s t
    | C.Lambda(n,s,t) ->
         let s = aux ctx s in
         let ctx = Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_lambda n s t
    | C.LetIn(n,b,s,t) ->
         let b = aux ctx b in
         let s = aux ctx s in
         let ctx = Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_letin n b s t
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
    | C.Case({ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs },
             rt,t,bs) ->
         let t = aux ctx t in
         let rt = aux ctx rt in
         let bs = Array.map (aux ctx) bs in
         in_elpi_match ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs t rt bs
    | C.Fix(([| rarg |],_),([| name |],[| _typ |], [| bo |])) ->
                    (* XXX typ *)
         in_elpi_fix name rarg (aux (name :: ctx) bo)
    | C.Fix((rargs,fno),(names,types,bodies)) -> nYI "HOAS for mutual fix"
    | C.CoFix(fno,(names,types,bodies)) -> nYI "HOAS for cofix"
    | C.Proj(p,t) -> nYI "HOAS for primitive projections"
  in
    aux [] t

(* ******* and back ********* *)

module Util = struct
  open Elpi_runtime
  let rec deref_head on_arg depth = function
    | UVar ({ contents = g }, from, args) when g != Constants.dummy ->
       deref_head on_arg depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != Constants.dummy ->
       deref_head on_arg depth (deref_appuv ~from ~to_:depth args t)
    | App(c,x,xs) when not on_arg ->
        App(c,deref_head true depth x,List.map (deref_head true depth) xs)
    | x -> x
  let kind d x = deref_head false d x
end

let in_coq_name = function
  | E.CData n when isname n -> nameout n
  | E.CData n when E.CD.is_string n -> 
       Name.Name (Id.of_string (E.CD.to_string n))
  | _ -> Name.Anonymous

let safe_destApp t =
  match C.kind t with
  | C.App(hd,args) -> C.kind hd, args
  | x -> x, [||]

let in_coq t =
  let rec aux depth t = match Util.kind depth t with
    | E.App(c,E.CData gr,[]) when indtc == c && isgr gr ->
                    (* TODO: check it is really an indt *)
         C.mkInd (G.destIndRef (grout gr))
    | E.App(c,E.CData gr,[]) when indcc == c && isgr gr ->
                    (* TODO: check it is really an indt *)
         C.mkConstruct (G.destConstructRef (grout gr))
    | E.App(c,E.CData gr,[]) when constc == c && isgr gr ->
         begin match grout gr with
         | G.VarRef v -> C.mkVar v
         | G.ConstRef v -> C.mkConst v
         | _ -> assert false
         end

    | E.App(c,t,[rt;bs]) when matchc == c ->
        let t = aux depth t in
        let rt = aux depth rt in
        let bt = List.map (aux depth) (E.lp_list_to_list depth bs) in
        let ind =
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
        let ci = Inductiveops.make_case_info (Global.env()) ind C.RegularStyle in
        C.mkCase (ci,t,rt,Array.of_list bt)

    | E.App(c,x,[]) when appc == c ->
         (match E.lp_list_to_list depth x with
         | x :: xs -> C.mkApp (aux depth x, Array.of_list (List.map (aux depth) xs))
         | _ -> assert false) (* TODO *)

    | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
        let name = in_coq_name name in
        let s = aux depth s in
        let t = aux depth t in
        if lamc == c then C.mkLambda (name,s,t) else C.mkProd (name,s,t)
    | E.App(c,name,[s;b;t]) when letc == c ->
        let name = in_coq_name name in
        let s = aux depth s in
        let b = aux depth b in
        let t = aux depth t in
        C.mkLetIn (name,b,s,t)
        

    | E.Const n ->
         if n >= 0 && n < depth then C.mkRel(depth - n) else assert false

    | E.Lam t -> aux (depth+1) t

    | E.App(c,n,[rno;bo]) when fixc == c -> nYI "readback fix (missing ty)"

    | _ -> nYI "readback"
  in
    aux 0 t

(* ***************** {{ quotation }} for Glob_terms ************************ *)

open Glob_term

let is_coq_string = ref (fun _ -> assert false)
let get_coq_string = ref (fun _ -> assert false)

let env = "elpi-coq:env"
let get_env, set_env =
  Elpi_util.ExtState.declare_extension env (fun () -> Global.env (), [])
;;
let push_env name depth (env, ctx) =
  Environ.(push_rel (Context.Rel.Declaration.LocalAssum(name,C.mkProp)) env),
  (name, depth) :: ctx
;;

let mkGHole =
  GHole(Loc.ghost,Evar_kinds.InternalHole,Misctypes.IntroAnonymous,None)

let glob_intros ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     match ov with
     | None -> GLambda(Loc.ghost,name,Decl_kinds.Explicit,ty,bo)
     | Some v -> GLetIn(Loc.ghost,name,v,(*ty,*)bo))
   ctx bo
;;

let rec gterm2lp depth state = function
  | GRef(_,gr,_ul) -> state, in_elpi_gr gr
  | GVar(_,id) ->
      let _, ctx = get_env state in
      if not (List.mem_assoc (Names.Name.Name id) ctx) then
        CErrors.anomaly Pp.(str"Unknown Coq global " ++ Names.Id.print id);
      state, E.Constants.of_dbl (List.assoc (Names.Name.Name id) ctx)
  | GSort(_, Misctypes.GProp) -> assert false
  | GSort(_, Misctypes.GSet) -> assert false
  | GSort(_, Misctypes.GType uname_loc_list) -> assert false

  | GProd(_,name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_prod name s t
  | GLambda(_,name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_lambda name s t
  | GLetIn(_,name,bo (*, oty*), t) ->
      let state, bo = gterm2lp depth state bo in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_letin name bo in_elpi_implicit t

  | GHole(_,_,_,Some arg) when !is_coq_string arg ->
      E.Quotations.lp ~depth state (!get_coq_string arg)
  | GHole _ -> state, in_elpi_implicit

  | GCast(_,t,c_ty) -> nYI "(glob)HOAS for GCast"
  | GEvar(_,_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"

  | GApp(_,hd,args) ->
      let state, hd = gterm2lp depth state hd in
      let state, args = Elpi_util.map_acc (gterm2lp depth) state args in
      state, in_elpi_appl hd args
  
  | GCases(_,_, oty, [ t, (name, oind) ], bs) ->
      let ind, oty =
        match oind, oty with
        | Some(_,ind,_args), _ -> ind, oty
        | None, _ ->
            match bs with
            | (_,_,[PatCstr(_,(ind,_),_,_)],_) :: _ -> ind, oty
            | _ -> assert false in
      let { C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs } =
        Inductiveops.make_case_info (Global.env()) ind C.RegularStyle in
      let { Declarations.mind_packets }, { Declarations.mind_consnames } =
        Inductive.lookup_mind_specif (Global.env()) ind in
      let no_constructors = Array.length mind_consnames in
      assert(Array.length mind_packets = 1);
      let state, t = gterm2lp depth state t in
      let state, rt =
        match oty with
        | None -> state, in_elpi_implicit
        | Some ty -> nYI ... assert false in
      let bs =
        List.map (fun (_,fv,pat,bo) ->
          match pat with
          | [PatCstr(_,(indc,cno as k),cargs,Name.Anonymous)] ->
               assert(Names.eq_ind indc ind);
               let cargs = List.map (function
                 | PatVar(_,n) -> n
                 | _ -> assert false) cargs in
               `Case(k,cargs,bo)
          | [PatVar(_,Name.Anonymous)] ->
               `Def bo
          | _ -> assert false) bs in
      let def,bs = List.partition (function `Def _ -> true | _ -> false) bs in
      assert(List.length def <= 1);
      let bs = CList.init no_constructors (fun i ->
        let cno = i + 1 in
        try CList.find_map (function
             | `Case((_,n as k),fv,bo) when n = cno -> Some (k,fv,bo)
             | `Case _ -> None
             | `Def _ -> assert false) bs
        with Not_found ->
          match bs with
          | [] ->
             CErrors.user_err ~hdr:"elpi"
               Pp.(str"Missing constructor " ++ Id.print mind_consnames.(i))
          | [`Def bo] ->
             let missing_k = ind,cno in
             let k_args = Inductiveops.constructor_nallargs missing_k in
             missing_k, CList.make k_args Name.Anonymous, bo
          | _ -> assert false) in
      let state, bs = Elpi_util.map_acc (fun state (k,ctx,bo) ->
        let env = get_env state in
        let bo =
          List.fold_right (fun name bo ->
            GLambda(Loc.ghost,name,Decl_kinds.Explicit,mkGHole,bo))
            ctx bo in
        let state, bo = gterm2lp depth state bo in
        let state = set_env state (fun _ -> env) in
        state, bo) state bs in
      let bs = Array.of_list bs in
      state, in_elpi_match ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs t rt bs
  | GCases _ -> assert false             
  | GLetTuple _ -> assert false
  | GIf  _ -> assert false

  | GRec(_,GFix([|Some rno,GStructRec|],0),[|name|],[|tctx|],[|_ty|],[|bo|]) ->
      let bo = glob_intros tctx bo in
      let name = Name.Name name in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, bo = gterm2lp (depth+1) state bo in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_fix name rno bo
  | GRec _ -> assert false

let () = E.Quotations.set_default_quotation (fun ~depth state src ->
  Printf.eprintf "Q:%s\n" src;
  let ce = Pcoq.parse_string Pcoq.Constr.lconstr src in
  try gterm2lp depth state (Constrintern.intern_constr (fst (get_env state)) ce)
  with E.Constants.UnknownGlobal s ->
    CErrors.user_err ~hdr:"elpi" Pp.(str"Unknown elpi global name "++str s)
)


(* ***************** $custom Coq predicates  ***************************** *)

let type_err api args expected =
 CErrors.user_err ~hdr:"elpi"
   Pp.(str api ++ str"got" ++ prlist str (List.map E.show_term args) ++ str"expects" ++ str expected)

let () =
  let open Elpi_util in

  (* Print (debugging) *)  
  Elpi_runtime.register_custom "$say" (fun ~depth ~env _ args ->
      let b = Buffer.create 80 in
      let fmt = Format.formatter_of_buffer b in
      Format.fprintf fmt "@[<hov 1>%a@]@\n%!"
        Elpi_runtime.Pp.(pplist (uppterm depth [] 0 env) " ") args;
    Feedback.msg_info (Pp.str (Buffer.contents b));
    []);

  (* Nametab access *)  
  Elpi_runtime.register_custom "$locate" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [E.CData c;ret] when E.cstring.Elpi_util.CData.isc c ->
        let qualid =
          Libnames.qualid_of_string (Elpi_ast.Func.show (E.cstring.Elpi_util.CData.cout c)) in
        let gr =
          try 
             match Nametab.locate_extended qualid with
             | G.TrueGlobal gr -> gr
             | G.SynDef sd -> 
                match Syntax_def.search_syntactic_definition sd with
                | _, Notation_term.NRef gr -> gr
                | _ -> assert false (* too complex *)
          with Not_found -> CErrors.user_err ~hdr:"elpi" Pp.(str "Not found: " ++ Libnames.pr_qualid qualid) in
        [E.App (E.Constants.eqc, in_elpi_gr gr, [ret])]
    | _ -> assert false);

  (* Kernel's environment access *)  
  E.register_custom "$coq-env-const" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [E.CData gr; ret_ty; ret_bo] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let ty, _u = Global.type_of_global_in_context (Global.env()) gr in
             let bo = Option.get (Global.body_of_constant c) in
             [E.App (E.Constants.eqc, constr2lp ty, [ret_ty]);
              E.App (E.Constants.eqc, constr2lp bo, [ret_bo]); ]
        | _ -> assert false end
    | _ -> type_err "$coq-env-const" args "reference");

  (* Kernel's type checker *)  
  E.register_custom "$coq-typecheck" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [t;ret] ->
        let t = in_coq t in
        let j = Safe_typing.typing (Global.safe_env ()) t in
        let ty = constr2lp (Safe_typing.j_type j) in
        [E.App (E.Constants.eqc, ty, [ret])]
    | _ -> assert false)
  
;;


