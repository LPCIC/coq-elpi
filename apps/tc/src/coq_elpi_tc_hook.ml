let _ = Mltop.add_known_module "coq-elpi-tc.plugin"

# 3 "src/coq_elpi_tc_hook.mlg"
 
open Stdarg
open Elpi_plugin
open Coq_elpi_arg_syntax
open Coq_elpi_class_tactics_hacked

module M = Coq_elpi_vernacular



let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-elpi-tc.plugin") ~command:"ElpiTypeclasses" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                     Vernacextend.TyTerminal ("Override", 
                                     Vernacextend.TyTerminal ("TC", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                                                    Vernacextend.TyTerminal ("All", 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body p
         atts = Vernacextend.vtdefault (fun () -> 
# 15 "src/coq_elpi_tc_hook.mlg"
                                                                                   
     let () = ignore_unknown_attributes atts in
     takeover false [] (snd p) 
                ) in fun p
         ?loc ~atts () -> coqpp_body p (Attributes.parse any_attribute atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                    Vernacextend.TyTerminal ("Override", 
                                    Vernacextend.TyTerminal ("TC", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                                                   Vernacextend.TyTerminal ("None", 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body p
         atts = Vernacextend.vtdefault (fun () -> 
# 18 "src/coq_elpi_tc_hook.mlg"
                                                                                    
     let () = ignore_unknown_attributes atts in
     takeover true [] (snd p) 
                ) in fun p
         ?loc ~atts () -> coqpp_body p (Attributes.parse any_attribute atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                    Vernacextend.TyTerminal ("Override", 
                                    Vernacextend.TyTerminal ("TC", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                                                   Vernacextend.TyTerminal ("Only", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body p cs
         atts = Vernacextend.vtdefault (fun () -> 
# 23 "src/coq_elpi_tc_hook.mlg"
                                                                                                          
     let () = ignore_unknown_attributes atts in
     takeover false cs (snd p) 
                ) in fun p
         cs ?loc ~atts () -> coqpp_body p cs
         (Attributes.parse any_attribute atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                    Vernacextend.TyTerminal ("Override", 
                                    Vernacextend.TyTerminal ("TC", Vernacextend.TyTerminal ("+", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body cs
         atts = Vernacextend.vtdefault (fun () -> 
# 26 "src/coq_elpi_tc_hook.mlg"
                                                                                  
     let () = ignore_unknown_attributes atts in
     takeover_add cs 
                ) in fun cs
         ?loc ~atts () -> coqpp_body cs
         (Attributes.parse any_attribute atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                    Vernacextend.TyTerminal ("Override", 
                                    Vernacextend.TyTerminal ("TC", Vernacextend.TyTerminal ("-", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body cs
         atts = Vernacextend.vtdefault (fun () -> 
# 29 "src/coq_elpi_tc_hook.mlg"
                                                                                  
     let () = ignore_unknown_attributes atts in
     takeover_rm cs 
                ) in fun cs
         ?loc ~atts () -> coqpp_body cs
         (Attributes.parse any_attribute atts)), None))]

