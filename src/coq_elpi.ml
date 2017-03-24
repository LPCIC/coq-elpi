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

let grin, isgr, grout =
  let open Elpi_util.CData in
  let { cin; isc; cout } = declare {
      data_name = "Globnames.global_reference";
      data_pp = (fun fmt x ->
        Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Printer.pr_global x)));
      data_eq = Globnames.eq_gr;
      data_hash = Globnames.RefOrdered.hash;
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
      data_name = "Names.Name.t";
      data_pp = (fun fmt x ->
        Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Nameops.pr_name x)));
      data_eq = Names.Name.equal;
      data_hash = Names.Name.hash;
  } in
  cin, isc, cout

module E = Elpi_runtime
module C = Constr

(* TODO: export shortcut *)
let _,prop = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "prop"))
let typc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "typ"))
let sortc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "sort"))
let prodc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "prod"))
let lamc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "lam"))
let letc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "let"))
let appc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "app"))
let constc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "const"))
let indtc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "indt"))
let indcc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "indc"))
let matchc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "match"))
let fixc,_ = E.Constants.(funct_of_ast (Elpi_ast.Func.from_string "fix"))

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
let in_elpi_prod n s t = E.App(prodc,E.CData(namein n),[s;E.Lam t])
let in_elpi_lambda n s t = E.App(lamc,E.CData(namein n),[s;E.Lam t])
let in_elpi_letin n b s t = E.App(letc,E.CData(namein n),[s;b;E.Lam t])
let in_elpi_app hd args = E.App(appc,E.list_to_lp_list (hd ::Array.to_list args),[])
let in_elpi_match ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs t rt bs =
  E.App(matchc,t, [rt; E.list_to_lp_list (Array.to_list bs)])
let in_elpi_fix name rno bo =
  E.App(fixc,E.CData(namein name),[E.CData (E.cint.cin rno); E.Lam bo])


(* TODO: universe polymorphism *)
let check_univ_inst univ_inst = assert(Univ.Instance.is_empty univ_inst)

let in_elpi t =
  let rec aux ctx t = match C.kind t with
    | C.Rel n -> E.Constants.of_dbl (List.length ctx - n)
    | C.Var n -> in_elpi_gr (Globnames.VarRef n)
    | C.Meta _ -> assert false
    | C.Evar _ -> assert false
    | C.Sort s -> in_elpi_sort s
    | C.Cast _ -> assert false
    | C.Prod(n,s,t) ->
         let s = aux ctx s in
         let ctx = Names.Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_prod n s t
    | C.Lambda(n,s,t) ->
         let s = aux ctx s in
         let ctx = Names.Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_lambda n s t
    | C.LetIn(n,b,s,t) ->
         let b = aux ctx b in
         let s = aux ctx s in
         let ctx = Names.Name.Anonymous :: ctx in
         let t = aux ctx t in
         in_elpi_letin n b s t
    | C.App(hd,args) ->
         let hd = aux ctx hd in
         let args = Array.map (aux ctx) args in
         in_elpi_app hd args
    | C.Const(c,i) ->
         check_univ_inst i;
         in_elpi_gr (Globnames.ConstRef c)
    | C.Ind(ind,i) ->
         check_univ_inst i;
         in_elpi_gr (Globnames.IndRef ind)
    | C.Construct(construct,i) ->
         check_univ_inst i;
         in_elpi_gr (Globnames.ConstructRef construct)
    | C.Case({ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs },
             rt,t,bs) ->
         let t = aux ctx t in
         let rt = aux ctx rt in
         let bs = Array.map (aux ctx) bs in
         in_elpi_match ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs t rt bs
    | C.Fix(([| rarg |],_),([| name |],[| _typ |], [| bo |])) ->
                    (* XXX typ *)
         in_elpi_fix name rarg (aux (name :: ctx) bo)
    | C.Fix((rargs,fno),(names,types,bodies)) ->
         assert false
    | C.CoFix(fno,(names,types,bodies)) ->
         assert false
    | C.Proj(p,t) ->
         assert false
  in
    aux [] t

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

let in_name = function
  | E.CData n when isname n -> nameout n
  | E.CData n when E.cstring.isc n -> 
              Names.Name.Name (Names.Id.of_string
                    (Elpi_ast.Func.show 
                     (E.cstring.cout n)))
  | _ -> Names.Name.Anonymous

let safe_destApp t =
  match C.kind t with
  | C.App(hd,args) -> C.kind hd, args
  | x -> x, [||]

let in_coq t =
  let rec aux depth t = match Util.kind depth t with
    | E.App(c,E.CData gr,[]) when indtc == c && isgr gr ->
                    (* TODO: check it is really an indt *)
         C.mkInd (Globnames.destIndRef (grout gr))
    | E.App(c,E.CData gr,[]) when indcc == c && isgr gr ->
                    (* TODO: check it is really an indt *)
         C.mkConstruct (Globnames.destConstructRef (grout gr))
    | E.App(c,E.CData gr,[]) when constc == c && isgr gr ->
         begin match grout gr with
         | Globnames.VarRef v -> C.mkVar v
         | Globnames.ConstRef v -> C.mkConst v
         | _ -> assert false
         end

    | E.App(c,t,[rt;bs]) when matchc == c ->
        let t = aux depth t in
        let rt = aux depth rt in
        let bt = List.map (aux depth) (E.lp_list_to_list bs) in
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
         (match E.lp_list_to_list x with
         | x :: xs -> C.mkApp (aux depth x, Array.of_list (List.map (aux depth) xs))
         | _ -> assert false) (* TODO *)

    | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
        let name = in_name name in
        let s = aux depth s in
        let t = aux depth t in
        if lamc == c then C.mkLambda (name,s,t) else C.mkProd (name,s,t)
    | E.App(c,name,[s;b;t]) when letc == c ->
        let name = in_name name in
        let s = aux depth s in
        let b = aux depth b in
        let t = aux depth t in
        C.mkLetIn (name,b,s,t)
        

    | E.Const n ->
         if n >= 0 && n < depth then C.mkRel(depth - n) else assert false

    | E.Lam t -> aux (depth+1) t
    | _ -> assert false
  in
    aux 0 t

let type_err api args expected =
 CErrors.user_err ~hdr:"elpi"
   Pp.(str api ++ str"got" ++ prlist str (List.map E.show_term args) ++ str"expects" ++ str expected)
(* Custom predicates *)
let () =
  let open Elpi_util in
  Elpi_runtime.register_custom "$say" (fun ~depth ~env _ args ->
      let b = Buffer.create 80 in
      let fmt = Format.formatter_of_buffer b in
      Format.fprintf fmt "@[<hov 1>%a@]@\n%!"
        Elpi_runtime.Pp.(pplist (uppterm depth [] 0 env) " ") args;
    Feedback.msg_info (Pp.str (Buffer.contents b));
    []);
  Elpi_runtime.register_custom "$locate" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [E.CData c;ret] when E.cstring.Elpi_util.CData.isc c ->
        let qualid =
          Libnames.qualid_of_string (Elpi_ast.Func.show (E.cstring.Elpi_util.CData.cout c)) in
        let gr =
          try 
             match Nametab.locate_extended qualid with
             | Globnames.TrueGlobal gr -> gr
             | Globnames.SynDef sd -> 
                match Syntax_def.search_syntactic_definition sd with
                | _, Notation_term.NRef gr -> gr
                | _ -> assert false (* too complex *)
          with Not_found -> CErrors.user_err ~hdr:"elpi" Pp.(str "Not found: " ++ Libnames.pr_qualid qualid) in
        [E.App (E.Constants.eqc, in_elpi_gr gr, [ret])]
    | _ -> assert false);
  E.register_custom "$coq-env-const" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [E.CData gr; ret_ty; ret_bo] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | Globnames.ConstRef c ->
             let ty, _u = Global.type_of_global_in_context (Global.env()) gr in
             let bo = Option.get (Global.body_of_constant c) in
             [App (E.Constants.eqc, in_elpi ty, [ret_ty]);
              App (E.Constants.eqc, in_elpi bo, [ret_bo]); ]
        | _ -> assert false end
    | _ -> type_err "$coq-env-const" args "reference");
  E.register_custom "$coq-typecheck" (fun ~depth ~env _ args ->
    match List.map (Util.kind depth) args with
    | [t;ret] ->
        let t = in_coq t in
        let j = Safe_typing.typing (Global.safe_env ()) t in
        let ty = in_elpi (Safe_typing.j_type j) in
        [App (E.Constants.eqc, ty, [ret])]
    | _ -> assert false)
  
;;


