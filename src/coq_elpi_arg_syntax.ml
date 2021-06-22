let __coq_plugin_name = "elpi_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 7 "src/coq_elpi_arg_syntax.mlg"
 

open Ltac_plugin

open Pcoq.Constr
open Pcoq.Prim

module EA = Coq_elpi_arg_HOAS
module U = Coq_elpi_utils

(* Arguments ************************************************************* *)
let pr_elpi_string _ _ _ (s : Elpi.API.Ast.Loc.t * string) = Pp.str (snd s)

let trim_loc loc =
  let open Loc in
  { loc with bp = loc.bp + 1; ep = loc.ep - 1 }

let idents_of loc s =
  let s = String.sub s 1 (String.length s - 2) in
  let l = Str.(split (regexp "[\t \n]+") s) in
  List.iter (fun x -> if not (CLexer.is_ident x) then raise Stream.Failure) l;
  Coq_elpi_utils.of_coq_loc (trim_loc loc), l

let rec strip_curly loc s =
  if s.[0] = '\123' then strip_curly (trim_loc loc) String.(sub s 1 (length s - 2))
  else Coq_elpi_utils.of_coq_loc loc, s
let rec strip_round loc s =
  if s.[0] = '(' then strip_round (trim_loc loc) String.(sub s 1 (length s - 2))
  else Coq_elpi_utils.of_coq_loc loc, s
let rec strip_square loc s =
  if s.[0] = '[' then strip_square (trim_loc loc) String.(sub s 1 (length s - 2))
  else Coq_elpi_utils.of_coq_loc loc, s



let (wit_elpi_string, elpi_string) = Tacentries.argument_extend ~name:"elpi_string" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "xxxxxxxx"))))
                                                                (fun _ loc ->
                                                                
# 43 "src/coq_elpi_arg_syntax.mlg"
                      (Elpi.API.Ast.Loc.initial "dummy", "") 
                                                                ))]);
                                     Tacentries.arg_tag = None;
                                     Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                     Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                     Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 42 "src/coq_elpi_arg_syntax.mlg"
                                         pr_elpi_string 
                                                              ), (fun env sigma -> 
                                                              
# 42 "src/coq_elpi_arg_syntax.mlg"
                                         pr_elpi_string 
                                                              ), (fun env sigma -> 
                                                              
# 42 "src/coq_elpi_arg_syntax.mlg"
                                         pr_elpi_string 
                                                              ));
                                     }
let _ = (wit_elpi_string, elpi_string)

let _ = let () =
        Pcoq.grammar_extend elpi_string
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                (fun s loc -> 
# 53 "src/coq_elpi_arg_syntax.mlg"
                   
    Coq_elpi_utils.of_coq_loc loc, s
  
                                              );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                               ((Pcoq.Symbol.token (Tok.PQUOTATION "lp:"))))
                               (fun s loc -> 
# 47 "src/coq_elpi_arg_syntax.mlg"
                            
    if s.[0] = '\123' then strip_curly loc s
    else if s.[0] = '(' then strip_round loc s
    else if s.[0] = '[' then strip_square loc s
    else Coq_elpi_utils.of_coq_loc loc, s
  
                                             )])]}
        in ()


# 59 "src/coq_elpi_arg_syntax.mlg"
 
let pr_fp _ _ _ (_,x) = U.pr_qualified_name x
let pp_elpi_loc _ _ _ (l : Loc.t) = Pp.mt ()

let the_qname = ref ""
let any_qname loc_fun strm =
  let re = Str.regexp "[A-Za-z][A-Za-z0-9]*\\(\\.?[A-Za-z][A-Za-z0-9]*\\)*" in
  match Stream.peek strm with
  | Some (Tok.KEYWORD sym) when Str.string_match re sym 0 ->
      let pos = Stream.count strm in
      Stream.junk strm;
      let _, ep = Loc.unloc (loc_fun pos) in
      begin match Stream.peek strm with
      | Some (Tok.IDENT id) ->
          let bp, _ = Loc.unloc (loc_fun (pos+1)) in
          if Int.equal ep bp then
            (Stream.junk strm; the_qname := sym ^ id)
          else
            the_qname := sym
      | _ -> the_qname := sym
      end
  | _ -> raise Stream.Failure
let any_qname = Pcoq.Entry.of_parser "any_qname" any_qname



let (wit_qualified_name, qualified_name) = Tacentries.argument_extend ~name:"qualified_name" 
                                           {
                                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                    []);
                                           Tacentries.arg_tag = None;
                                           Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                           Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                           Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                           Tacentries.arg_printer = ((fun env sigma -> 
                                                                    
# 85 "src/coq_elpi_arg_syntax.mlg"
                                            pr_fp 
                                                                    ), (fun env sigma -> 
                                                                    
# 85 "src/coq_elpi_arg_syntax.mlg"
                                            pr_fp 
                                                                    ), (fun env sigma -> 
                                                                    
# 85 "src/coq_elpi_arg_syntax.mlg"
                                            pr_fp 
                                                                    ));
                                           }
let _ = (wit_qualified_name, qualified_name)

let _ = let () =
        Pcoq.grammar_extend qualified_name
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm any_qname)))
                                (fun _ loc -> 
# 91 "src/coq_elpi_arg_syntax.mlg"
                     loc, Str.split_delim (Str.regexp_string ".") !the_qname 
                                              );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                               (fun _ loc -> 
# 90 "src/coq_elpi_arg_syntax.mlg"
               loc, [] 
                                             );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                               ((Pcoq.Symbol.list0 (Pcoq.Symbol.token (Tok.PFIELD (None))))))
                               (fun s i loc -> 
# 89 "src/coq_elpi_arg_syntax.mlg"
                                      loc, i :: s 
                                               )])]}
        in ()

let (wit_elpi_loc, elpi_loc) = Tacentries.argument_extend ~name:"elpi_loc" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 97 "src/coq_elpi_arg_syntax.mlg"
           loc 
                                                                    ))]);
                               Tacentries.arg_tag = None;
                               Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                               Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                               Tacentries.arg_interp = Tacentries.ArgInterpRet;
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 96 "src/coq_elpi_arg_syntax.mlg"
             pp_elpi_loc 
                                                        ), (fun env sigma -> 
                                                        
# 96 "src/coq_elpi_arg_syntax.mlg"
             pp_elpi_loc 
                                                        ), (fun env sigma -> 
                                                        
# 96 "src/coq_elpi_arg_syntax.mlg"
             pp_elpi_loc 
                                                        ));
                               }
let _ = (wit_elpi_loc, elpi_loc)


# 100 "src/coq_elpi_arg_syntax.mlg"
 

let record_fields = Pcoq.Entry.create "elpi:record_fields"
let telescope = Pcoq.Entry.create "elpi:telescope"
let colon_sort = Pcoq.Entry.create "elpi:colon_sort"
let colon_constr = Pcoq.Entry.create "elpi:colon_constr"
let pipe_telescope = Pcoq.Entry.create "elpi:pipe_telescope"
let inductive_constructors = Pcoq.Entry.create "elpi:inductive_constructors"

let any_attribute : Attributes.vernac_flags Attributes.attribute =
  Attributes.make_attribute (fun x -> [],x)
let skip_attribute : (Str.regexp list option * Str.regexp list option) Attributes.attribute =
  let open Attributes.Notations in
  let o2l = function None -> [] | Some l -> l in
  Attributes.attribute_of_list
    ["skip",
      fun old -> function
      | Attributes.VernacFlagLeaf (Attributes.FlagString rex) -> Str.regexp rex :: o2l old
      | _ -> CErrors.user_err (Pp.str "Syntax error, use #[skip=\"rex\"]")]
  ++
  Attributes.attribute_of_list
   ["only",
      fun old -> function
      | Attributes.VernacFlagLeaf (Attributes.FlagString rex) -> Str.regexp rex :: o2l old
      | _ -> CErrors.user_err (Pp.str "Syntax error, use #[only=\"rex\"]")]

let coq_kwd_or_symbol = Pcoq.Entry.create "elpi:kwd_or_symbol"

let opt2list = function None -> [] | Some l -> l

let the_kwd = ref ""
let any_kwd _ strm =
  match Stream.peek strm with
  | Some (Tok.KEYWORD sym) when sym <> "." -> Stream.junk strm; the_kwd := sym
  | _ -> raise Stream.Failure
let any_kwd = Pcoq.Entry.of_parser "any_symbols_or_kwd" any_kwd


let pr_attributes _ _ _ atts =
  Pp.(prlist_with_sep (fun () -> str ",") Attributes.pr_vernac_flag atts)

let wit_elpi_ftactic_arg = EA.wit_elpi_ftactic_arg



let _ = let constructor = Pcoq.Entry.make "constructor"
        and constructor_type = Pcoq.Entry.make "constructor_type"
        in
        let () =
        Pcoq.grammar_extend record_fields
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make (Pcoq.Rule.stop)
                                (fun loc -> 
# 151 "src/coq_elpi_arg_syntax.mlg"
             [] 
                                            );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                               ((Pcoq.Symbol.nterm G_vernac.record_field)))
                               (fun f loc -> 
# 150 "src/coq_elpi_arg_syntax.mlg"
                                       [f] 
                                             );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm G_vernac.record_field)))
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                               ((Pcoq.Symbol.nterm record_fields)))
                               (fun fs _ f loc -> 
# 149 "src/coq_elpi_arg_syntax.mlg"
                                                                f :: fs 
                                                  )])]}
        in let () =
        Pcoq.grammar_extend inductive_constructors
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm identref)))
                                                                ((Pcoq.Symbol.nterm constructor_type)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constructor)) ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))) false)))
                                (fun l _ c id loc -> 
# 157 "src/coq_elpi_arg_syntax.mlg"
                                                                                      c id :: l 
                                                     );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                               ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constructor)) ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))) false)))
                               (fun l _ loc -> 
# 156 "src/coq_elpi_arg_syntax.mlg"
                                                l 
                                               )])]}
        in let () =
        Pcoq.grammar_extend constructor
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm identref)))
                                                ((Pcoq.Symbol.nterm constructor_type)))
                                (fun c id loc -> 
# 161 "src/coq_elpi_arg_syntax.mlg"
                                                 c id 
                                                 )])]}
        in let () =
        Pcoq.grammar_extend constructor_type
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm binders)))
                                                ((Pcoq.Symbol.rules [Pcoq.Rules.make 
                                                                    (Pcoq.Rule.stop)
                                                                    (fun
                                                                    loc -> 
                                                                    
# 167 "src/coq_elpi_arg_syntax.mlg"
                  fun l id -> id,Constrexpr_ops.mkProdCN ~loc l (CAst.make ~loc @@ Constrexpr.CHole (None, Namegen.IntroAnonymous, None)) 
                                                                    );
                                                                    Pcoq.Rules.make 
                                                                    (Pcoq.Rule.next_norec 
                                                                    (Pcoq.Rule.next_norec 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                    ((Pcoq.Symbol.nterm lconstr)))
                                                                    (fun c _
                                                                    loc -> 
                                                                    
# 166 "src/coq_elpi_arg_syntax.mlg"
                                   fun l id -> id,Constrexpr_ops.mkProdCN ~loc l c 
                                                                    )])))
                                (fun t l loc -> 
# 168 "src/coq_elpi_arg_syntax.mlg"
             t l 
                                                )])]}
        in let () =
        Pcoq.grammar_extend pipe_telescope
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                ((Pcoq.Symbol.nterm binders)))
                                (fun bl _ loc -> 
# 173 "src/coq_elpi_arg_syntax.mlg"
                               bl 
                                                 )])]}
        in let () =
        Pcoq.grammar_extend telescope
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm binders)))
                                (fun bl loc -> 
# 176 "src/coq_elpi_arg_syntax.mlg"
                          bl 
                                               )])]}
        in let () =
        Pcoq.grammar_extend colon_sort
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                ((Pcoq.Symbol.nterm sort)))
                                (fun s _ loc -> 
# 179 "src/coq_elpi_arg_syntax.mlg"
                           s 
                                                )])]}
        in let () =
        Pcoq.grammar_extend colon_constr
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                ((Pcoq.Symbol.nterm lconstr)))
                                (fun s _ loc -> 
# 182 "src/coq_elpi_arg_syntax.mlg"
                              s 
                                                )])]}
        in let () =
        Pcoq.grammar_extend coq_kwd_or_symbol
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm any_kwd)))
                                (fun _ loc -> 
# 185 "src/coq_elpi_arg_syntax.mlg"
                     !the_kwd 
                                              )])]}
        in ()

let (wit_elpi_arg, elpi_arg) = Tacentries.argument_extend ~name:"elpi_arg" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm coq_kwd_or_symbol)))
                                                          (fun x loc -> 
# 215 "src/coq_elpi_arg_syntax.mlg"
                                EA.String x 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                         (fun _ t _ loc -> 
# 213 "src/coq_elpi_arg_syntax.mlg"
                              EA.Term t 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Context"))))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         (fun ty _ loc -> 
# 212 "src/coq_elpi_arg_syntax.mlg"
                                   EA.Context ty 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Axiom"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.nterm colon_constr)))
                                                         (fun t typ name _
                                                         loc -> 
# 210 "src/coq_elpi_arg_syntax.mlg"
                                                                      
      EA.ConstantDecl { EA.name = snd name; typ = (typ,Some t); body = None } 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Definition"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_constr))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun b _ t typ name
                                                         _ loc -> 
# 208 "src/coq_elpi_arg_syntax.mlg"
                                                                                               
      EA.ConstantDecl { EA.name = snd name; typ = (typ,t); body = Some b } 
                                                                  ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Class"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_sort))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ident))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.nterm record_fields)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         (fun _ fs _ k _ s ps
                                                         name _ loc -> 
                                                         
# 206 "src/coq_elpi_arg_syntax.mlg"
                                                                                                                   
      EA.RecordDecl { EA.name = snd name; sort = s; parameters = ps; constructor = k; fields = fs } 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Record"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_sort))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ident))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.nterm record_fields)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         (fun _ fs _ k _ s ps
                                                         name _ loc -> 
                                                         
# 204 "src/coq_elpi_arg_syntax.mlg"
                                                                                                                    
      EA.RecordDecl { EA.name = snd name; sort = s; parameters = ps; constructor = k; fields = fs } 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Variant"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm pipe_telescope))))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_constr))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.nterm inductive_constructors)))
                                                         (fun cs _ s nups ps
                                                         name _ loc -> 
                                                         
# 202 "src/coq_elpi_arg_syntax.mlg"
                                                                                                                                    
      EA.IndtDecl { EA.finiteness = Vernacexpr.Variant; name = snd name; arity = s; parameters = ps; non_uniform_parameters = opt2list nups; constructors = cs } 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "CoInductive"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm pipe_telescope))))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_constr))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.nterm inductive_constructors)))
                                                         (fun cs _ s nups ps
                                                         name _ loc -> 
                                                         
# 200 "src/coq_elpi_arg_syntax.mlg"
                                                                                                                                        
      EA.IndtDecl { EA.finiteness = Vernacexpr.CoInductive; name = snd name; arity = s; parameters = ps; non_uniform_parameters = opt2list nups; constructors = cs } 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "Inductive"))))
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         ((Pcoq.Symbol.nterm telescope)))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm pipe_telescope))))
                                                         ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm colon_constr))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                         ((Pcoq.Symbol.nterm inductive_constructors)))
                                                         (fun cs _ s nups ps
                                                         name _ loc -> 
                                                         
# 198 "src/coq_elpi_arg_syntax.mlg"
                                                                                                                                      
      EA.IndtDecl { EA.finiteness = Vernacexpr.Inductive_kw; name = snd name; arity = s; parameters = ps; non_uniform_parameters = opt2list nups; constructors = cs } 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm string)))
                                                         (fun s loc -> 
# 197 "src/coq_elpi_arg_syntax.mlg"
                     EA.String s 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm integer)))
                                                         (fun n loc -> 
# 196 "src/coq_elpi_arg_syntax.mlg"
                      EA.Int n 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm qualified_name)))
                                                         (fun s loc -> 
# 195 "src/coq_elpi_arg_syntax.mlg"
                             EA.String (String.concat "." (snd s)) 
                                                                    ))]);
                               Tacentries.arg_tag = None;
                               Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                       
# 191 "src/coq_elpi_arg_syntax.mlg"
                EA.glob_arg 
                                                       ));
                               Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                      
# 192 "src/coq_elpi_arg_syntax.mlg"
                 EA.subst_arg 
                                                      );
                               Tacentries.arg_interp = Tacentries.ArgInterpLegacy (
                                                       
# 190 "src/coq_elpi_arg_syntax.mlg"
                 EA.interp_arg 
                                                       );
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 193 "src/coq_elpi_arg_syntax.mlg"
                 fun _ _ _ -> EA.pp_raw_arg env sigma 
                                                        ), (fun env sigma -> 
                                                        
# 194 "src/coq_elpi_arg_syntax.mlg"
                  fun _ _ _ -> EA.pp_glob_arg env sigma 
                                                        ), (fun env sigma -> 
                                                        
# 189 "src/coq_elpi_arg_syntax.mlg"
             fun _ _ _ -> EA.pp_top_arg env sigma 
                                                        ));
                               }
let _ = (wit_elpi_arg, elpi_arg)

let (wit_elpi_tactic_arg, elpi_tactic_arg) = Tacentries.argument_extend ~name:"elpi_tactic_arg" 
                                             {
                                             Tacentries.arg_parsing = 
                                             Vernacextend.Arg_rules (
                                             [(Pcoq.Production.make
                                               (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "ltac_term_list"))))
                                                               ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                               ((Pcoq.Symbol.nterm ident)))
                                                               ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                               (fun _ t _ _ _ loc -> 
# 229 "src/coq_elpi_arg_syntax.mlg"
                                                 EA.LTac(EA.List EA.Term,(CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None))) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "ltac_term"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ _ _ loc -> 
# 228 "src/coq_elpi_arg_syntax.mlg"
                                            EA.LTac(EA.Term, CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None)) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "ltac_int_list"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ _ _ loc -> 
# 227 "src/coq_elpi_arg_syntax.mlg"
                                                EA.LTac(EA.List EA.Int, (CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None))) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "ltac_int"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ _ _ loc -> 
# 226 "src/coq_elpi_arg_syntax.mlg"
                                           EA.LTac(EA.Int, (CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None))) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "ltac_string_list"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ _ _ loc -> 
# 225 "src/coq_elpi_arg_syntax.mlg"
                                                   EA.LTac(EA.List EA.String, (CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None))) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "ltac_string"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ _ _ loc -> 
# 224 "src/coq_elpi_arg_syntax.mlg"
                                              EA.LTac(EA.String, (CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string t,None))) 
                                                                    ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.nterm lconstr)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                              (fun _ t _ loc -> 
# 223 "src/coq_elpi_arg_syntax.mlg"
                              EA.Term t 
                                                                ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm string)))
                                              (fun s loc -> 
# 222 "src/coq_elpi_arg_syntax.mlg"
                     EA.String s 
                                                            ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm integer)))
                                              (fun n loc -> 
# 221 "src/coq_elpi_arg_syntax.mlg"
                      EA.Int n 
                                                            ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm qualified_name)))
                                              (fun s loc -> 
# 220 "src/coq_elpi_arg_syntax.mlg"
                             EA.String (String.concat "." (snd s)) 
                                                            ))]);
                                             Tacentries.arg_tag = Some
                                                                  (Geninterp.val_tag (Genarg.topwit wit_elpi_ftactic_arg));
                                             Tacentries.arg_intern = 
                                             Tacentries.ArgInternWit (wit_elpi_ftactic_arg);
                                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_elpi_ftactic_arg);
                                             Tacentries.arg_interp = 
                                             Tacentries.ArgInterpWit (wit_elpi_ftactic_arg);
                                             Tacentries.arg_printer = 
                                             ((fun env sigma -> 
# 0 ""
fun _ _ _ _ -> Pp.str "missing printer"
                                             ), (fun env sigma -> 
# 0 ""
fun _ _ _ _ -> Pp.str "missing printer"
                                             ), (fun env sigma -> 
# 0 ""
fun _ _ _ _ -> Pp.str "missing printer"
                                             ));
                                             }
let _ = (wit_elpi_tactic_arg, elpi_tactic_arg)

let (wit_attributes, attributes) = Tacentries.argument_extend ~name:"attributes" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            []);
                                   Tacentries.arg_tag = None;
                                   Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                   Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                   Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 233 "src/coq_elpi_arg_syntax.mlg"
               pr_attributes 
                                                            ), (fun env sigma -> 
                                                            
# 233 "src/coq_elpi_arg_syntax.mlg"
               pr_attributes 
                                                            ), (fun env sigma -> 
                                                            
# 233 "src/coq_elpi_arg_syntax.mlg"
               pr_attributes 
                                                            ));
                                   }
let _ = (wit_attributes, attributes)

let _ = let my_attribute_list = Pcoq.Entry.make "my_attribute_list"
        and my_attribute = Pcoq.Entry.make "my_attribute"
        and my_attr_value = Pcoq.Entry.make "my_attr_value"
        in
        let () =
        Pcoq.grammar_extend my_attribute_list
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm my_attribute)) ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))) false)))
                                (fun a loc -> 
# 237 "src/coq_elpi_arg_syntax.mlg"
                                            a 
                                              )])]}
        in let () =
        Pcoq.grammar_extend my_attribute
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("using"))))))
                                                ((Pcoq.Symbol.nterm my_attr_value)))
                                (fun v _ loc -> 
# 243 "src/coq_elpi_arg_syntax.mlg"
                                               "using", v 
                                                );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ident)))
                                               ((Pcoq.Symbol.nterm my_attr_value)))
                               (fun v k loc -> 
# 241 "src/coq_elpi_arg_syntax.mlg"
                                           Names.Id.to_string k, v 
                                               )])]}
        in let () =
        Pcoq.grammar_extend my_attr_value
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make (Pcoq.Rule.stop)
                                (fun loc -> 
# 250 "src/coq_elpi_arg_syntax.mlg"
             Attributes.VernacFlagEmpty 
                                            );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                               ((Pcoq.Symbol.nterm my_attribute_list)))
                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                               (fun _ a _ loc -> 
# 249 "src/coq_elpi_arg_syntax.mlg"
                                               Attributes.VernacFlagList a 
                                                 );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                               ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                               (fun v _ loc -> 
# 248 "src/coq_elpi_arg_syntax.mlg"
                             Attributes.VernacFlagLeaf (Attributes.FlagIdent v) 
                                               );
                               Pcoq.Production.make
                               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                               ((Pcoq.Symbol.nterm string)))
                               (fun v _ loc -> 
# 247 "src/coq_elpi_arg_syntax.mlg"
                              Attributes.VernacFlagLeaf (Attributes.FlagString v) 
                                               )])]}
        in let () =
        Pcoq.grammar_extend attributes
        { Pcoq.pos=None; data=[(None, None,
                               [Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm my_attribute)) ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))) false)))
                                (fun atts loc -> 
# 254 "src/coq_elpi_arg_syntax.mlg"
                                                         atts 
                                                 )])]}
        in ()

let (wit_ltac_attributes, ltac_attributes) = Tacentries.argument_extend ~name:"ltac_attributes" 
                                             {
                                             Tacentries.arg_parsing = 
                                             Vernacextend.Arg_rules (
                                             [(Pcoq.Production.make
                                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ident)))
                                               (fun v loc -> 
# 268 "src/coq_elpi_arg_syntax.mlg"
                    (CAst.make ~loc @@ Constrexpr.CRef (Libnames.qualid_of_string ~loc @@ Names.Id.to_string v,None)) 
                                                             ))]);
                                             Tacentries.arg_tag = None;
                                             Tacentries.arg_intern = 
                                             Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                             
# 264 "src/coq_elpi_arg_syntax.mlg"
                  fun gsig t -> fst @@ Ltac_plugin.Tacintern.intern_constr gsig t 
                                             ));
                                             Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                                    
# 265 "src/coq_elpi_arg_syntax.mlg"
                   Detyping.subst_glob_constr (Global.env()) 
                                                                    );
                                             Tacentries.arg_interp = 
                                             Tacentries.ArgInterpLegacy (
# 259 "src/coq_elpi_arg_syntax.mlg"
                   fun ist evd x -> match DAst.get x with
      | Glob_term.GVar id ->
          evd.Evd.sigma,
          Ltac_plugin.Tacinterp.interp_ltac_var (Ltac_plugin.Tacinterp.Value.cast (Genarg.topwit wit_attributes)) ist None (CAst.make id)
      | _ -> assert false 
                                             );
                                             Tacentries.arg_printer = 
                                             ((fun env sigma -> 
# 266 "src/coq_elpi_arg_syntax.mlg"
                   fun _ _ _ -> Ppconstr.pr_constr_expr env sigma 
                                             ), (fun env sigma -> 
# 267 "src/coq_elpi_arg_syntax.mlg"
                    fun _ _ _ -> Printer.pr_glob_constr_env env sigma 
                                             ), (fun env sigma -> 
# 258 "src/coq_elpi_arg_syntax.mlg"
               pr_attributes 
                                             ));
                                             }
let _ = (wit_ltac_attributes, ltac_attributes)

