# Original Coq lexer implementation Copyright 2006-2019 by the Pygments team.
# Modifications Copyright (c) 2019-2022 Clement Pit-Claudel.
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""
Pygments lexers for the coq-elpi manual: Elpi, Coq, and Coq-with-embedded-Elpi
(``lp:{{ ... }}`` quotations).

This module vendors two independent lexers rather than depending on the
``alectryon`` package at build time:

- ``CoqLexer`` below is Alectryon's own Coq lexer
  (``alectryon/pygments_lexer.py``), copied verbatim (state names
  ``_basic``/``_vernac``/``_keywords``/``_other``); it is materially more
  complete than Pygments' stock ``pygments.lexers.theorem.RocqLexer`` and is
  what coq-elpi's own ``CoqElpiLexer`` was already written against.
- ``ElpiLexer`` is coq-elpi's own from-scratch Elpi lexer (previously living
  in ``etc/alectryon_elpi.py``), also copied verbatim.

``CoqElpiLexer`` combines the two, adding recognition of ``lp:{{ ... }}``
quotations inside Coq source. Registered into Sphinx via
``sphinx.highlighting.lexers`` in ``conf.py`` -- see that file.
"""

from pygments.filter import apply_filters
from pygments.lexer import (
    RegexLexer, default, words, bygroups, include, inherit, using,
)
from pygments.regexopt import regex_opt, regex_opt_inner
from pygments.token import (
    Text, Comment, Operator, Keyword, Name, String, Number, Punctuation,
)

# == Coq lexer (vendored from alectryon/pygments_lexer.py) ==================


class CoqLexer(RegexLexer):
    """
    For the `Coq <http://coq.inria.fr/>`_ theorem prover.

    .. versionadded:: 1.5
    """

    name = 'Coq'
    aliases = ['coq']
    filenames = ['*.v']
    mimetypes = ['text/x-coq']

    # This is auto-generated from Coq's Manual
    kwds = {
        'cmd': ['Abort All', 'About', 'Add', 'Add LoadPath', 'Add ML Path',
                'Add Rec LoadPath', 'Add Rec ML Path', 'Add Relation',
                'Add Setoid', 'Admit Obligations', 'Admitted', 'Arguments',
                'As', 'Back', 'BackTo', 'Backtrack', 'Bind Scope', 'Cd',
                'Check', 'Close Scope', 'Compute', 'Create HintDb',
                'Cumulative', 'Declare Custom Entry', 'Declare Instance',
                'Declare Left Step', 'Declare ML Module', 'Declare Reduction',
                'Declare Right Step', 'Declare Scope', 'Defined',
                'Delimit Scope', 'Drop', 'Eval', 'Existential', 'Export',
                'Export Set', 'Export Unset', 'Extract Constant',
                'Extract Inductive', 'Extract Inlined Constant', 'Extraction',
                'Extraction Blacklist', 'Extraction Implicit',
                'Extraction Inline', 'Extraction Language Haskell',
                'Extraction Language OCaml', 'Extraction Language Scheme',
                'Extraction Library', 'Extraction NoInline',
                'Extraction TestCompile', 'Fail', 'Focus', 'From',
                'Generalizable All Variables', 'Generalizable No Variables',
                'Global', 'Goal', 'Grab Existential Variables', 'Guarded',
                'Hint', 'Hint Constants Opaque', 'Hint Constants Transparent',
                'Hint Constructors', 'Hint Cut', 'Hint Extern',
                'Hint Immediate', 'Hint Mode', 'Hint Opaque', 'Hint Resolve',
                'Hint Rewrite', 'Hint Transparent', 'Hint Unfold',
                'Hint Variables Opaque', 'Hint Variables Transparent',
                'Hint View for apply', 'Hint View for move', 'Immediate',
                'Import', 'Include', 'Induction for', 'Infix', 'Info', 'Inline',
                'Inspect', 'Load', 'Load Verbose', 'Local',
                'Locate', 'Locate File', 'Locate Library',
                'Locate Ltac', 'Locate Module', 'Locate Term', 'Ltac2',
                'Ltac2 Eval', 'Ltac2 Notation', 'Ltac2 Set', 'Ltac2 Type',
                'Ltac2 Type rec', 'Ltac2 mutable', 'Ltac2 mutable rec',
                'Ltac2 rec', 'Minimality for', 'Module Export', 'Module Import',
                'Monomorphic', 'Next Obligation', 'NonCumulative',
                'Obligation Tactic', 'Obligation num', 'Obligations', 'Opaque',
                'Open Scope', 'Optimize Heap', 'Optimize Proof', 'Polymorphic',
                'Preterm', 'Print', 'Print All', 'Print All Dependencies',
                'Print Assumptions', 'Print Canonical Projections',
                'Print Classes', 'Print Coercion Paths', 'Print Coercions',
                'Print Extraction Blacklist', 'Print Extraction Inline',
                'Print Firstorder Solver', 'Print Grammar',
                'Print Grammar constr', 'Print Grammar pattern',
                'Print Grammar tactic', 'Print Graph', 'Print Hint',
                'Print HintDb', 'Print Implicit', 'Print Instances',
                'Print Libraries', 'Print LoadPath', 'Print Ltac',
                'Print Ltac Signatures', 'Print ML Modules', 'Print ML Path',
                'Print Module', 'Print Module Type',
                'Print Opaque Dependencies', 'Print Options',
                'Print Rewrite HintDb', 'Print Scope', 'Print Scopes',
                'Print Section', 'Print Sorted Universes', 'Print Strategies',
                'Print Strategy', 'Print Table', 'Print Tables', 'Print Term',
                'Print Transparent Dependencies', 'Print Universes',
                'Print Universes Subgraph', 'Print Visibility',
                'Program Definition', 'Program Fixpoint', 'Program Instance',
                'Program Lemma', 'Proof', 'Proof using All', 'Proof using Type',
                'Proof with', 'Pwd', 'Qed', 'Quit', 'Recursive Extraction',
                'Recursive Extraction Library', 'Redirect', 'Register',
                'Register Inline', 'Remove', 'Remove Hints', 'Remove LoadPath',
                'Require', 'Require Export', 'Require Import', 'Reserved Infix',
                'Reserved Notation', 'Reset Extraction Blacklist',
                'Reset Extraction Inline', 'Reset Initial',
                'Reset Ltac Profile', 'Resolve', 'Restart', 'Search',
                'Search in', 'SearchAbout', 'SearchHead', 'SearchPattern',
                'SearchRewrite', 'Separate Extraction', 'Show',
                'Show Conjectures', 'Show Existentials', 'Show Intro',
                'Show Intros', 'Show Ltac Profile', 'Show Match',
                'Show Obligation Tactic', 'Show Proof', 'Show Script',
                'Show Universes', 'Solve All Obligations',
                'Solve All Obligations with', 'Solve Obligations',
                'Solve Obligations with', 'Sort', 'Strategy', 'SuchThat',
                'Tactic Notation', 'Test', 'Time', 'Timeout', 'Transparent',
                'Typeclasses Opaque', 'Typeclasses Transparent',
                'Typeclasses eauto', 'Undelimit Scope', 'Undo', 'Unfocus',
                'Unfocused', 'Unset', 'Unshelve', 'abstract after', 'and',
                'as ident', 'as pattern', 'as strict pattern', 'at level',
                'at next level', 'bfs', 'bigint', 'binder', 'clear implicits',
                'clear scopes', 'closed binder', 'constr at level',
                'constr at next level', 'custom', 'custom at level',
                'custom at next level', 'debug', 'default implicits', 'dfs',
                'discriminated', 'extra scopes', 'format', 'from', 'global',
                'ident', 'in custom', 'inside', 'left associativity', 'measure',
                'no associativity', 'only parsing', 'only printing', 'outside',
                'pattern at level', 'right associativity', 'strict pattern',
                'strict pattern at level', 'warning after', 'wf', 'where',
                'with Induction for', 'with signature'],
        'decls': ['Class', 'CoFixpoint', 'CoInductive', 'Corollary',
                  'Definition', 'Example', 'Fact', 'Fixpoint', 'Inductive',
                  'Instance', 'Lemma', 'Let', 'Proposition', 'Record', 'Remark',
                  'Structure', 'Theorem', 'Variant'],
        'expects_binders': ['Add Parametric Morphism', 'Axiom', 'Axioms',
                            'Conjecture', 'Conjectures', 'Context',
                            'Hypotheses', 'Hypothesis', 'Implicit Types',
                            'Parameter', 'Parameters', 'Variable',
                            'Variables'],
        'expects_name': ['Abort', 'Add Field', 'Add Morphism', 'Add Ring',
                         'Admit Obligations of', 'Canonical',
                         'Canonical Structure', 'Coercion', 'Collection',
                         'Combined Scheme', 'Constraint', 'Declare Module',
                         'Derive', 'Derive Dependent Inversion',
                         'Derive Dependent Inversion_clear', 'Derive Inversion',
                         'Derive Inversion_clear', 'End', 'Existing Class',
                         'Existing Instance', 'Function', 'Functional Scheme',
                         'Generalizable Variable', 'Generalizable Variables',
                         'Identity Coercion', 'Implicit Type', 'Let CoFixpoint',
                         'Let Fixpoint', 'Ltac', 'Module', 'Module Type',
                         'Next Obligation of', 'Notation', 'Numeral Notation',
                         'Obligation num of', 'Obligations of',
                         'Prenex Implicits', 'Preterm of', 'Primitive',
                         'Proof using', 'Reset', 'Save', 'Scheme',
                         'Scheme Equality for', 'Scheme Induction for',
                         'Section', 'Solve Obligations of', 'String Notation',
                         'SubClass', 'Universe'],
        'flag': ['Allow StrictProp', 'Asymmetric Patterns',
                 'Auto Template Polymorphism', 'Boolean Equality Schemes',
                 'Bracketing Last Introduction Pattern',
                 'Case Analysis Schemes', 'Congruence Verbose',
                 'Contextual Implicit', 'Coqtop Exit On Error',
                 'Cumulativity Weak Constraints', 'Debug Auto', 'Debug Cbv',
                 'Debug Eauto', 'Debug RAKAM', 'Debug SsrMatching',
                 'Debug Ssreflect', 'Debug Tactic Unification', 'Debug Trivial',
                 'Debug Unification', 'Decidable Equality Schemes',
                 'Elaboration StrictProp Cumulativity', 'Elimination Schemes',
                 'Extraction AutoInline', 'Extraction Conservative Types',
                 'Extraction KeepSingleton', 'Extraction Optimize',
                 'Extraction SafeImplicits', 'Extraction TypeExpand',
                 'Fast Name Printing', 'Hide Obligations', 'Implicit Arguments',
                 'Info Auto', 'Info Eauto', 'Info Trivial',
                 'Intuition Negation Unfolding', 'Keep Proof Equalities',
                 'Keyed Unification', 'Ltac Backtrace', 'Ltac Batch Debug',
                 'Ltac Debug', 'Ltac Profiling', 'Ltac2 Backtrace',
                 'Mangle Names', 'Maximal Implicit Insertion',
                 'NativeCompute Profiling', 'Nested Proofs Allowed',
                 'Nonrecursive Elimination Schemes', 'Omega Action',
                 'Omega System', 'Omega UseLocalDefs', 'Parsing Explicit',
                 'Polymorphic Inductive Cumulativity', 'Primitive Projections',
                 'Printing All', 'Printing Allow Match Default Clause',
                 'Printing Coercions', 'Printing Compact Contexts',
                 'Printing Dependent Evars Line',
                 'Printing Existential Instances',
                 'Printing Factorizable Match Patterns', 'Printing Implicit',
                 'Printing Implicit Defensive', 'Printing Matching',
                 'Printing Notations',
                 'Printing Primitive Projection Parameters',
                 'Printing Projections', 'Printing Records', 'Printing Synth',
                 'Printing Unfocused', 'Printing Universes',
                 'Printing Wildcard', 'Private Polymorphic Universes',
                 'Program Cases', 'Program Generalized Coercion',
                 'Program Mode', 'Refine Instance Mode', 'Regular Subst Tactic',
                 'Reversible Pattern Implicit', 'Rewriting Schemes',
                 'Search Output Name Only', 'Short Module Printing',
                 'Shrink Obligations', 'Silent', 'Simplex',
                 'Solve Unification Constraints', 'SsrHave NoTCResolution',
                 'SsrIdents', 'SsrOldRewriteGoalsOrder', 'SsrRewrite',
                 'Stable Omega', 'Strict Implicit',
                 'Strict Universe Declaration', 'Strongly Strict Implicit',
                 'Structural Injection', 'Suggest Proof Using',
                 'Transparent Obligations',
                 'Typeclass Resolution For Conversion', 'Typeclasses Debug',
                 'Typeclasses Dependency Order',
                 'Typeclasses Filtered Unification',
                 'Typeclasses Iterative Deepening', 'Typeclasses Limit Intros',
                 'Typeclasses Strict Resolution',
                 'Typeclasses Unique Instances', 'Typeclasses Unique Solutions',
                 'Uniform Inductive Parameters',
                 'Universal Lemma Under Conjunction',
                 'Universe Minimization ToSet', 'Universe Polymorphism'],
        'gallina-constants': ['False', 'Funclass', 'Prop', 'SProp', 'Set',
                              'Sortclass', 'True', 'Type'],
        'gallina-keywords': ['as', 'cofix', 'else', 'end', 'exists', 'exists2',
                             'fix', 'for', 'forall', 'fun', 'if', 'in', 'is',
                             "isn't", 'let', 'let cofix', 'let fix', 'ltac2',
                             'match', 'return', 'struct', 'then', 'with'],
        'ltac-builtins': ['abstract', 'all', 'assert_fails', 'assert_succeeds',
                          'constr', 'context', 'do', 'eval', 'exactly_once',
                          'fail', 'first', 'fresh', 'gfail', 'guard', 'idtac',
                          'ltac', 'numgoals', 'once', 'only', 'par', 'progress',
                          'repeat', 'solve', 'time', 'timeout', 'try',
                          'type of', 'type_term', 'uconstr'],
        'ltac-keywords': ['lazy_match!', 'lazy_match! goal with',
                          'lazy_match! reverse goal with', 'lazymatch',
                          'lazymatch goal with', 'lazymatch reverse goal with',
                          'let rec', 'match goal with',
                          'match reverse goal with', 'match!',
                          'match! goal with', 'match! reverse goal with',
                          'multi_match!', 'multi_match! goal with',
                          'multi_match! reverse goal with', 'multimatch',
                          'multimatch goal with',
                          'multimatch reverse goal with', 'tryif'],
        'opt': ['Bullet Behavior "None"', 'Bullet Behavior "Strict Subproofs"',
                'Default Goal Selector', 'Default Proof Using',
                'Default Timeout', 'Diffs "off"', 'Diffs "on"',
                'Diffs "removed"', 'Extraction File Comment', 'Extraction Flag',
                'Firstorder Depth', 'Firstorder Solver', 'Hyps Limit',
                'Info Level', 'Loose Hint Behavior "Lax"',
                'Loose Hint Behavior "Strict"', 'Loose Hint Behavior "Warn"',
                'Mangle Names Prefix', 'NativeCompute Profile Filename',
                'Printing Depth', 'Printing Width',
                'Typeclasses Debug Verbosity', 'Typeclasses Depth',
                'Warnings'],
        'table': ['Printing Coercion', 'Printing Constructor', 'Printing If',
                  'Printing Let', 'Printing Record', 'Search Blacklist'],
        'tacn': ['absurd', 'admit', 'after', 'apply', 'assert', 'at',
                 'at bottom', 'at top', 'auto', 'auto using', 'auto with',
                 'autoapply', 'autorewrite with', 'autounfold with', 'before',
                 'btauto', 'by rewrite over', 'case', 'case_eq', 'cbn', 'cbv',
                 'change', 'change_no_check', 'classical_left',
                 'classical_right', 'clear', 'clear dependent', 'clearbody',
                 'compare', 'compute', 'congr', 'congruence n',
                 'congruence with', 'constr_eq', 'constr_eq_strict',
                 'constructor', 'conv_tactic in', 'convert_concl_no_check',
                 'cut', 'cutrewrite', 'cycle', 'd_item', 'debug auto',
                 'debug trivial', 'decompose', 'decompose record',
                 'decompose sum', 'dependent destruction',
                 'dependent induction', 'dependent inversion',
                 'dependent inversion_clear', 'dependent rewrite', 'destruct',
                 'dintuition', 'discrR', 'double induction', 'eapply',
                 'eassert', 'eauto', 'eauto using', 'eauto with', 'ecase',
                 'econstructor', 'edestruct', 'ediscriminate', 'eelim',
                 'eenough', 'eexists', 'einduction', 'einjection',
                 'einjection as', 'eintros', 'eleft', 'elim', 'elimtype',
                 'enough', 'epose', 'epose proof', 'eqn', 'eremember',
                 'erewrite', 'eright', 'eset', 'esimplify_eq', 'esplit',
                 'etransitivity', 'evar', 'exfalso', 'f_equal',
                 'field_simplify', 'field_simplify in', 'field_simplify_eq',
                 'field_simplify_eq in', 'finish_timing', 'first last',
                 'firstorder', 'firstorder using', 'firstorder with', 'fold',
                 'fresh component', 'function induction',
                 'functional induction', 'functional inversion', 'gen have',
                 'generalize', 'generalize dependent', 'generalizing',
                 'generally have', 'give_up', 'has_evar', 'have', 'have suff',
                 'hnf', 'induction', 'info_auto', 'info_auto using',
                 'info_auto with', 'info_eauto', 'info_eauto using',
                 'info_eauto with', 'info_trivial', 'info_trivial using',
                 'info_trivial with', 'injection', 'injection as',
                 'instantiate', 'into', 'intro', 'intro after',
                 'intro at bottom', 'intro at top', 'intro before', 'intros',
                 'intros until', 'intuition', 'inversion', 'inversion_clear',
                 'inversion_sigma', 'is_evar', 'is_var', 'lapply', 'last',
                 'last first', 'lazy', 'left', 'left with', 'move',
                 'native_compute', 'notypeclasses refine', 'now_show',
                 'optimize_heap', 'over', 'pattern', 'pose', 'pose cofix',
                 'pose fix', 'pose proof', 'red', 'refine', 'remember',
                 'rename', 'replace', 'reset ltac profile', 'restart_timer',
                 'revert', 'revert dependent', 'revgoals', 'rewrite',
                 'rewrite_strat', 'right', 'right with', 'ring_simplify', 'set',
                 'setoid_replace', 'setoid_rewrite', 'setoid_symmetry',
                 'setoid_symmetry in', 'setoid_transitivity', 'shelve',
                 'shelve_unifiable', 'show ltac profile', 'simpl',
                 'simple apply', 'simple destruct', 'simple eapply',
                 'simple induction', 'simple inversion',
                 'simple notypeclasses refine', 'simple refine', 'simplify_eq',
                 'solve_constraints', 'specialize', 'split', 'split with',
                 'split_Rabs', 'split_Rmult', 'start ltac profiling', 'stepl',
                 'stepr', 'stop ltac profiling', 'subst', 'suff', 'suff have',
                 'suffices', 'suffices have', 'swap', 'symmetry', 'symmetry in',
                 'tags', 'time_constr', 'transitivity', 'transparent_abstract',
                 'trivial', 'trivial using', 'trivial with',
                 'typeclasses eauto', 'typeclasses eauto with', 'under',
                 'unfold', 'unify', 'unlock', 'unshelve', 'using',
                 'using relation', 'value of', 'vm_compute', 'without loss',
                 'without loss suff', 'wlog', 'wlog suff'],
        'tacn-solve': ['assumption', 'by', 'congruence', 'contradict',
                       'contradiction', 'decide equality', 'discriminate',
                       'done', 'dtauto', 'eassumption', 'easy', 'eexact',
                       'exact', 'exact_no_check', 'field', 'lia', 'lra',
                       'native_cast_no_check', 'nia', 'now', 'nra', 'nsatz',
                       'omega', 'psatz', 'reflexivity', 'ring', 'rtauto',
                       'setoid_reflexivity', 'tauto', 'vm_cast_no_check']
    }

    TOKEN_TYPES = {
        'cmd': Keyword.Namespace,
        'gallina-constants': Keyword.Type,
        'gallina-keywords': Keyword,
        'ltac-builtins': Keyword.Pseudo,
        'ltac-keywords': Keyword,
        'tacn': Name.Builtin,
        'tacn-solve': Name.Builtin.Pseudo,
    }

    # This is auto-generated from Coq's source code
    identstart = ('A-Z_a-z\xa0ªµºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶ-ͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆ'
                  'ՙա-ևא-תװ-ײؠ-يٮ-ٯٱ-ۓەۥ-ۦۮ-ۯۺ-ۼۿܐܒ-ܯݍ-ޥޱߊ-ߪߴ-ߵߺࠀ-ࠕࠚࠤࠨࡀ-ࡘࢠ-ࢴࢶ'
                  '-ࢽऄ-हऽॐक़-ॡॱ-ঀঅ-ঌএ-ঐও-নপ-রলশ-হঽৎড়-ঢ়য়-ৡৰ-ৱਅ-ਊਏ-ਐਓ-ਨਪ-ਰਲ-ਲ਼ਵ-ਸ਼'
                  'ਸ-ਹਖ਼-ੜਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલ-ળવ-હઽૐૠ-ૡૹଅ-ଌଏ-ଐଓ-ନପ-ରଲ-ଳଵ-ହଽଡ଼-ଢ଼ୟ-'
                  'ୡୱஃஅ-ஊஎ-ஐஒ-கங-சஜஞ-டண-தந-பம-ஹௐఅ-ఌఎ-ఐఒ-నప-హఽౘ-ౚౠ-ౡಀಅ-ಌಎ-ಐಒ-ನ'
                  'ಪ-ಳವ-ಹಽೞೠ-ೡೱ-ೲഅ-ഌഎ-ഐഒ-ഺഽൎൔ-ൖൟ-ൡൺ-ൿඅ-ඖක-නඳ-රලව-ෆก-ะา-ำเ-ๆກ-'
                  'ຂຄງ-ຈຊຍດ-ທນ-ຟມ-ຣລວສ-ຫອ-ະາ-ຳຽເ-ໄໆໜ-ໟༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿၐ-ၕၚ-ၝၡၥ-'
                  'ၦၮ-ၰၵ-ႁႎႠ-ჅჇჍა-ჺჼ-ቈቊ-ቍቐ-ቖቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ'
                  '-ፚᎀ-ᎏᎠ-Ᏽᏸ-ᏽᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛱ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗៜᠠ-ᡷᢀ-ᢄᢇ-ᢨ'
                  'ᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᦰ-ᧉᨀ-ᨖᨠ-ᩔᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮ-ᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᲀ-ᲈᳩ-ᳬᳮ-'
                  'ᳱᳵ-ᳶᴀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙὛὝὟ-ώᾀ-ᾴᾶ-ᾼιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱⁿₐ-ₜ'
                  'ℂℇℊ-ℓℕℙ-ℝℤΩℨK-ℭℯ-ℹℼ-ℿⅅ-ⅉⅎↃ-ↄⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲ-ⳳⴀ-ⴥⴧⴭⴰ-ⵧⵯⶀ-ⶖⶠ-ⶦ'
                  'ⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞⸯ々-〆〱-〵〻-〼ぁ-ゖゝ-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵'
                  '一-鿕ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪ-ꘫꙀ-ꙮꙿ-ꚝꚠ-ꛥꜗ-ꜟꜢ-ꞈꞋ-ꞮꞰ-ꞷꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ'
                  '-ꣷꣻꣽꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺꩾ-ꪯꪱꪵ-ꪶꪹ-ꪽꫀꫂꫛ-ꫝꫠ-ꫪꫲ'
                  '-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭥꭰ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִײַ-ﬨשׁ-זּטּ-לּמּ'
                  'נּ-סּףּ-פּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ𐀀-𐀋𐀍-𐀦𐀨-𐀺𐀼'
                  '-𐀽𐀿-𐁍𐁐-𐁝𐂀-𐃺𐊀-𐊜𐊠-𐋐𐌀-𐌟𐌰-𐍀𐍂-𐍉𐍐-𐍵𐎀-𐎝𐎠-𐏃𐏈-𐏏𐐀-𐒝𐒰-𐓓𐓘-𐓻𐔀-𐔧𐔰-𐕣𐘀-𐜶𐝀-'
                  '𐝕𐝠-𐝧𐠀-𐠅𐠈𐠊-𐠵𐠷-𐠸𐠼𐠿-𐡕𐡠-𐡶𐢀-𐢞𐣠-𐣲𐣴-𐣵𐤀-𐤕𐤠-𐤹𐦀-𐦷𐦾-𐦿𐨀𐨐-𐨓𐨕-𐨗𐨙-𐨳𐩠-𐩼𐪀-𐪜'
                  '𐫀-𐫇𐫉-𐫤𐬀-𐬵𐭀-𐭕𐭠-𐭲𐮀-𐮑𐰀-𐱈𐲀-𐲲𐳀-𐳲𑀃-𑀷𑂃-𑂯𑃐-𑃨𑄃-𑄦𑅐-𑅲𑅶𑆃-𑆲𑇁-𑇄𑇚𑇜𑈀-𑈑𑈓-𑈫𑊀'
                  '-𑊆𑊈𑊊-𑊍𑊏-𑊝𑊟-𑊨𑊰-𑋞𑌅-𑌌𑌏-𑌐𑌓-𑌨𑌪-𑌰𑌲-𑌳𑌵-𑌹𑌽𑍐𑍝-𑍡𑐀-𑐴𑑇-𑑊𑒀-𑒯𑓄-𑓅𑓇𑖀-𑖮𑗘-𑗛𑘀'
                  '-𑘯𑙄𑚀-𑚪𑜀-𑜙𑢠-𑣟𑣿𑫀-𑫸𑰀-𑰈𑰊-𑰮𑱀𑱲-𑲏𒀀-𒎙𒒀-𒕃𓀀-𓐮𔐀-𔙆𖠀-𖨸𖩀-𖩞𖫐-𖫭𖬀-𖬯𖭀-𖭃𖭣-𖭷𖭽-'
                  '𖮏𖼀-𖽄𖽐𖾓-𖾟𖿠𗀀-𘟬𘠀-𘫲𛀀-𛀁𛰀-𛱪𛱰-𛱼𛲀-𛲈𛲐-𛲙𝐀-𝑔𝑖-𝒜𝒞-𝒟𝒢𝒥-𝒦𝒩-𝒬𝒮-𝒹𝒻𝒽-𝓃𝓅-𝔅𝔇-'
                  '𝔊𝔍-𝔔𝔖-𝔜𝔞-𝔹𝔻-𝔾𝕀-𝕄𝕆𝕊-𝕐𝕒-𝚥𝚨-𝛀𝛂-𝛚𝛜-𝛺𝛼-𝜔𝜖-𝜴𝜶-𝝎𝝐-𝝮𝝰-𝞈𝞊-𝞨𝞪-𝟂𝟄-𝟋𞠀-'
                  '𞣄𞤀-𞥃𞸀-𞸃𞸅-𞸟𞸡-𞸢𞸤𞸧𞸩-𞸲𞸴-𞸷𞸹𞸻𞹂𞹇𞹉𞹋𞹍-𞹏𞹑-𞹒𞹔𞹗𞹙𞹛𞹝𞹟𞹡-𞹢𞹤𞹧-𞹪𞹬-𞹲𞹴-𞹷𞹹-𞹼𞹾𞺀-'
                  '𞺉𞺋-𞺛𞺡-𞺣𞺥-𞺩𞺫-𞺻𠀀-𪛖𪜀-𫜴𫝀-𫠝𫠠-𬺡丽-𪘀')
    identpart = (identstart +
                 "'0-9¼-¾٠-٩۰-۹߀-߉०-९০-৯৴-৹੦-੯૦-૯୦-୯୲-୷௦-௲౦-౯౸-౾೦-೯൘-൞൦-൸෦-෯๐"
                 '-๙໐-໙༠-༳၀-၉႐-႙፩-፼ᛮ-ᛰ០-៩៰-៹᠐-᠙᥆-᥏᧐-᧚᪀-᪉᪐-᪙᭐-᭙᮰-᮹᱀-᱉᱐-᱙₀-₉⅐-ↂ'
                 'ↅ-↉①-⒛⓪-⓿❶-➓⳽〇〡-〩〸-〺㆒-㆕㈠-㈩㉈-㉏㉑-㉟㊀-㊉㊱-㊿꘠-꘩ꛦ-ꛯ꠰-꠵꣐-꣙꤀-꤉꧐-꧙꧰-꧹'
                 '꩐-꩙꯰-꯹０-９𐄇-𐄳𐅀-𐅸𐆊-𐆋𐋡-𐋻𐌠-𐌣𐍁𐍊𐏑-𐏕𐒠-𐒩𐡘-𐡟𐡹-𐡿𐢧-𐢯𐣻-𐣿𐤖-𐤛𐦼-𐦽𐧀-𐧏𐧒-𐧿𐩀-𐩇'
                 '𐩽-𐩾𐪝-𐪟𐫫-𐫯𐭘-𐭟𐭸-𐭿𐮩-𐮯𐳺-𐳿𐹠-𐹾𑁒-𑁯𑃰-𑃹𑄶-𑄿𑇐-𑇙𑇡-𑇴𑋰-𑋹𑑐-𑑙𑓐-𑓙𑙐-𑙙𑛀-𑛉𑜰-𑜻𑣠-'
                 '𑣲𑱐-𑱬𒐀-𒑮𖩠-𖩩𖭐-𖭙𖭛-𖭡𝍠-𝍱𝟎-𝟿𞣇-𞣏𞥐-𞥙🄀-🄌')
    symbol = (identpart + # https://github.com/HoTT/Coq-HoTT/pull/1836
              '!-&(-/:-@[-\\^`{-~¡-©«-¬®-´¶-¹»¿×÷˂-˅˒-˟˥-˫˭˯-˿͵;΄-΅·϶҂՚-՟։-֊֍-'
              '֏־׀׃׆׳-״؆-؏؛؞-؟٪-٭۔۞۩۽-۾܀-܍߶-߹࠰-࠾࡞।-॥॰৲-৳৺-৻૰-૱୰௳-௺౿൏൹෴฿๏๚-๛༁-'
              '༗༚-༟༴༶༸༺-༽྅྾-࿅࿇-࿌࿎-࿚၊-၏႞-႟჻፠-፨᎐-᎙᐀᙭-᙮᚛-᚜᛫-᛭᜵-᜶។-៖៘-៛᠀-᠊᥀᥄-᥅᧞-᧿'
              '᨞-᨟᪠-᪦᪨-᪭᭚-᭪᭴-᭼᯼-᯿᰻-᰿᱾-᱿᳀-᳇᳓᾽᾿-῁῍-῏῝-῟῭-`´-῾‐-‧‰-⁞⁰⁴-⁾₊-₎₠-₾℀-'
              '℁℃-℆℈-℉℔№-℘℞-℣℥℧℩℮℺-℻⅀-⅄⅊-⅍⅏↊-↋←-⏾␀-␦⑀-⑊⒜-ⓩ─-❵➔-⭳⭶-⮕⮘-⮹⮽-⯈⯊-⯑⯬'
              '-⯯⳥-⳪⳹-⳼⳾-⳿⵰⸀-⸮⸰-⹄⺀-⺙⺛-⻳⼀-⿕⿰-⿻、-〄〈-〠〰〶-〷〽-〿゛-゜゠・㆐-㆑㆖-㆟㇀-㇣㈀-㈞㈪-'
              '㉇㉐㉠-㉿㊊-㊰㋀-㋾㌀-㏿䷀-䷿꒐-꓆꓾-꓿꘍-꘏꙳꙾꛲-꛷꜀-꜖꜠-꜡꞉-꞊꠨-꠫꠶-꠹꡴-꡷꣎-꣏꣸-꣺꣼꤮-꤯꥟꧁-'
              '꧍꧞-꧟꩜-꩟꩷-꩹꫞-꫟꫰-꫱꭛꯫﬩﮲-﯁﴾-﴿﷼-﷽︐-︙︰-﹒﹔-﹦﹨-﹫！-／：-＠［-｀｛-･￠-￦￨-￮￼-�𐄀'
              '-𐄂𐄷-𐄿𐅹-𐆉𐆌-𐆎𐆐-𐆛𐆠𐇐-𐇼𐎟𐏐𐕯𐡗𐡷-𐡸𐤟𐤿𐩐-𐩘𐩿𐫈𐫰-𐫶𐬹-𐬿𐮙-𐮜𑁇-𑁍𑂻-𑂼𑂾-𑃁𑅀-𑅃𑅴-𑅵𑇅-𑇉𑇍𑇛𑇝'
              '-𑇟𑈸-𑈽𑊩𑑋-𑑏𑑛𑑝𑓆𑗁-𑗗𑙁-𑙃𑙠-𑙬𑜼-𑜿𑱁-𑱅𑱰-𑱱𒑰-𒑴𖩮-𖩯𖫵𖬷-𖬿𖭄-𖭅𛲜𛲟𝀀-𝃵𝄀-𝄦𝄩-𝅘𝅥𝅲𝅪-𝅬𝆃-𝆄𝆌-'
              '𝆩𝆮-𝇨𝈀-𝉁𝉅𝌀-𝍖𝛁𝛛𝛻𝜕𝜵𝝏𝝯𝞉𝞩𝟃𝠀-𝧿𝨷-𝨺𝩭-𝩴𝩶-𝪃𝪅-𝪋𞥞-𞥟𞻰-𞻱🀀-🀫🀰-🂓🂠-🂮🂱-🂿🃁-🃏🃑-🃵🄐-'
              '🄮🄰-🅫🅰-🆬🇦-🈂🈐-🈻🉀-🉈🉐-🉑🌀-🛒🛠-🛬🛰-🛶🜀-🝳🞀-🟔🠀-🠋🠐-🡇🡐-🡙🡠-🢇🢐-🢭🤐-🤞🤠-🤧🤰🤳-🤾🥀-🥋'
              '🥐-🥞🦀-🦑🧀')

    symbol += '⃐-⃰' # Combining symbols
    # The tweaks below can be removed on the next update of the manual
    kwds['decls'].append("Equations")
    kwds['tacn-solve'].remove("omega")

    local_global = regex_opt_inner(("Local", "Global", "Export"), '(?:')
    set_unset_test = regex_opt_inner(("Set", "Unset", "Test"), '(?:')
    add_remove_test = regex_opt_inner(("Add", "Remove", "Test"), '(?:')

    opts = regex_opt(kwds['flag'] + kwds['opt'])
    opts_re = r"\b(?:{} )?(?:{} ){}\b".format(local_global, set_unset_test, opts)
    tables = regex_opt(kwds['table'])
    tables_re = r"\b(?:{} ){}\b".format(add_remove_test, tables)

    decls = regex_opt_inner(kwds['decls'], '(?:')
    decls_re = r"\b(?:{} )?(?:Program )?{}\b".format(local_global, decls)
    expects_name = regex_opt_inner(kwds['expects_name'], '(?:')
    expects_name_re = r"\b(?:{} )?{}\b".format(local_global, expects_name)
    expects_binders = regex_opt(kwds['expects_binders'])
    expects_binders_re = r"\b(?:{} )?{}\b".format(local_global, expects_binders)
    let_binder_re = regex_opt(["let", "let rec", "let fix", "let cofix"])
    cmd = kwds['cmd'] + kwds['decls'] + kwds['expects_name'] + kwds['expects_binders']

    name_re = r"[{}][{}]*".format(identstart, identpart)
    evar_re = r"[?]{}".format(name_re)

    not_identpart = r"\b(?![{}])".format(identpart)
    ws = lambda w, suffix=not_identpart: words(w, prefix=r'\b', suffix=suffix)

    comment = lambda token: [
        (r'[^(*)]+', token),
        (r'\(\*', token, '#push'),
        (r'\*\)', token, '#pop'),
        (r'[(*)]', token),
    ]
    binders = lambda regex, name_re: [
        (regex, Operator, '#pop'),
        (":", Operator, '#pop'),
        (name_re, Name.Variable),
        (r"'\s*" + name_re, Name.Variable), # single constructor
        (r"'\s*\(", Operator, ('in parens')), # pattern matching
        (r"'\s*\{", Operator, ('in curly')), # pattern matching
        (r"\(", Operator, ('in parens', 'type annot')),
        (r"\{", Operator, ('in curly', 'type annot')),
        include('_basic'),
        default('#pop'),
    ]

    # Names starting with '_' are not real states; they are just intended to be
    # included into other states.
    tokens = {
        'root': [
            include('_basic'),
            include('_vernac'),
            include('_keywords'),
            include('_other'),
        ],

        '_gallina': [
            include('_basic'),
            include('_keywords'),
            include('_other'),
        ],

        '_basic': [
            (r'\s+', Text),
            (r'\(\*[|*]', String.Doc, 'docstring'),
            (r'\(\*', Comment, 'comment'),
            (r'"', String.Double, 'string'),

            (r'\d[\d_]*', Number.Integer),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),
        ],
        'docstring': comment(String.Doc),
        'comment': comment(Comment),
        'string': [
            (r'[^"]+', String.Double),
            (r'""', String.Double),
            (r'"', String.Double, '#pop'),
        ],

        '_vernac': [
            (r"({})(\s+)({})".format(decls_re, name_re),
             bygroups(Keyword.Namespace, Text, Name.Function),
             'binders'),
            (expects_binders_re,
             Keyword.Namespace,
             'binders'),
            (r"({})(\s+)({})".format(expects_name_re, name_re),
             bygroups(Keyword.Namespace, Text, Name.Function)),
            (opts_re, Keyword.Namespace),
            (tables_re, Keyword.Namespace),
            (ws(cmd), TOKEN_TYPES['cmd']),
        ],
        'binders': binders(r":=|[.]", name_re),

        '_keywords': [
            (r"\bforall\b|\bexists\b|∀|∃", Keyword, 'quantifier args'),
            (r"\bfun\b|λ", Keyword, 'fun args'),
            (let_binder_re, Keyword, 'let args'),
            (ws(kwds['ltac-keywords']), TOKEN_TYPES['ltac-keywords']),
            (ws(kwds['ltac-builtins']), TOKEN_TYPES['ltac-builtins']),
            (ws(kwds['gallina-keywords']), TOKEN_TYPES['gallina-keywords']),
            (ws(kwds['gallina-constants']), TOKEN_TYPES['gallina-constants']),
            (ws(kwds['tacn-solve']), TOKEN_TYPES['tacn-solve']),
            (ws(kwds['tacn']), TOKEN_TYPES['tacn']),
        ],
        'quantifier args': binders(",", name_re),
        'fun args': binders("=>", name_re),
        'let args': binders(":=", name_re),
        'in parens': [
            (r"\(", Operator, '#push'),
            (r"\)", Operator, '#pop'),
            include('_gallina'),
        ],
        'in curly': [
            (r"\{", Operator, '#push'),
            (r"\}", Operator, '#pop'),
            include('_gallina'),
        ],
        'type annot': [
            (':', Operator, '#pop'),
            (",", Text), # let (a, b) := …
            (name_re, Name.Variable),
            include('_basic'),
            default("#pop"),
        ],

        # The symbol regexp below consumes symbol chars one by one.  Without
        # this, expressions like ``("x", y)`` would be incorrectly parsed as
        # ``("``, ``x``, and ``", y)``, with the first ``"`` coalesced with the
        # preceding ``(`` and the second ``"`` lexed as a string opener.
        # Clients can reconstitute multi-character symbols later (e.g. before
        # running other filters) using a ``TokenMergeFilter``.
        '_other': [
            (name_re, Name),
            (evar_re, Name.Label),
            # ['] is not a symbol character according to the grammar, but it has
            # so many uses (plus notations) that handling all of them properly
            # is just too complicated.  Bail out and recognize it here.
            (r"['{}]".format(symbol), Operator),
        ],
    }


# == Elpi lexer (vendored from etc/alectryon_elpi.py) ========================


class ElpiLexer(RegexLexer):
    """
    Lexer for the Elpi programming language.
    """

    name = 'Elpi'
    url = 'http://github.com/LPCIC/elpi'
    aliases = ['elpi']
    filenames = ['*.elpi']
    mimetypes = ['text/x-elpi']
    version_added = '2.11'

    lcase_re = r"[a-z]"
    ucase_re = r"[A-Z]"
    digit_re = r"[0-9]"
    schar2_re = r"([+*^?/<>`'@#~=&!])"
    schar_re = rf"({schar2_re}|-|\$|_)"
    idchar_re = rf"({lcase_re}|{ucase_re}|{digit_re}|{schar_re})"
    idcharstarns_re = rf"({idchar_re}*(\.({lcase_re}|{ucase_re}){idchar_re}*)*)"
    symbchar_re = rf"({lcase_re}|{ucase_re}|{digit_re}|{schar_re}|:)"
    constant_re = rf"({ucase_re}{idchar_re}*|{lcase_re}{idcharstarns_re}|{schar2_re}{symbchar_re}*|_{idchar_re}+)"
    symbol_re = r"(,|<=>|-->|:-|:>|;|\?-|->|&|=>|\bas\b|\buvar\b|<|=<|=|==|>=|>|\bi<|\bi=<|\bi>=|\bi>|\bis\b|\br<|\br=<|\br>=|\br>|\bs<|\bs=<|\bs>=|\bs>|@|::|\[\]|`->|`:|`:=|\^|-|\+|\bi-|\bi\+|r-|r\+|/|\*|\bdiv\b|\bi\*|\bmod\b|\br\*|~|\bi~|\br~)"
    const_sym_re = rf"({constant_re}|{symbol_re}|\({symbol_re}\))"
    # "builtin" and "symb" are accepted as alternate spellings of "external"
    # and "symbol" respectively; colour every combination of prefix and
    # keyword as a single token, the same way elpi's own manual's
    # _pygments_elpi.py (a thin subclass of Pygments' stock ElpiLexer) does
    # with its own `_ext`/`_symkw` fragments. Per coq-elpi's own
    # etc/tutorial_style.rst ghref patterns: `pred`/`func` accept either
    # prefix, `symb`/`symbol` accept either prefix, `data` accepts only
    # `builtin`, and `kind`/`typeabbrev` accept neither.
    _ext_re = r"(?:external|builtin)"

    tokens = {
        'root': [
            include('elpi')
        ],

        'elpi': [
            include('_elpi-comment'),

            (r"(:before|:after|:if|:name|:replace|:remove)(\s*)(\")",
             bygroups(Keyword.ElpiMode, Text.Whitespace, String.Double),
             'elpi-string'),
            (r"(:functional|:nooc|:untyped|:external)\b", Keyword.ElpiMode),
            (r"(:index)(\s*)(\()", bygroups(Keyword.ElpiMode, Text.Whitespace, Punctuation),
             'elpi-indexing-expr'),
            (rf"\b({_ext_re}\s+pred|pred)(\s+)({const_sym_re})",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-pred-item'),
            (rf"\b({_ext_re}\s+func|func)(\s+)({const_sym_re})",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-func-item'),
            (rf"\b(external type|type)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-type'),
            (rf"\b(kind)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-type'),
            (rf"\b(builtin\s+data|data)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-type'),
            (rf"\b({_ext_re}\s+symb|symb)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-symb-item'),
            (rf"\b({_ext_re}\s+symbol|symbol)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-symb-item'),
            (r"\b(builtin)\b", Keyword.ElpiKeyword),
            (rf"\b(typeabbrev)(\s+)({const_sym_re})",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-type'),
            (r"\b(typeabbrev)(\s+)(\([^)]+\))",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-type'),
            (r"\b(accumulate)(\s+)(\")",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, String.Double),
             'elpi-string'),
            (rf"\b(accumulate|namespace|local)(\s+)({constant_re})",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Text)),
            (rf"\b(shorten)(\s+)({constant_re}\.)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Text)),
            (r"\b(pi|sigma)(\s+)([a-zA-Z][A-Za-z0-9_ ]*)(\\)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiVariable, Text)),
            (rf"\b(constraint)(\s+)(({const_sym_re}(\s+)?)+)",
             bygroups(Keyword.ElpiKeyword, Text.Whitespace, Name.ElpiFunction),
             'elpi-chr-rule-start'),

            (rf"(?=[A-Z_]){constant_re}", Name.ElpiVariable),
            (rf"(?=[a-z_])({constant_re}|_)(:[A-Za-z0-9_ ]*)?(\\)", Name.ElpiVariable),
            (r"_", Name.ElpiVariable),
            # A binder's `\' does not have to immediately follow its bound
            # variable (whitespace is insignificant there, e.g. `x \ ...` is
            # as valid as `x\ ...'); the rule above only covers the latter,
            # tightly-bound spelling, so a standalone `\' still needs its own
            # rule or it falls through as a lexer Error token.
            (r"\\", Keyword.ElpiKeyword),
            (rf"({symbol_re}|!|=>|;)", Keyword.ElpiKeyword),
            (constant_re, Text),
            (r"\[|\]|\||=>", Keyword.ElpiKeyword),
            # guillemets: coq-elpi's own convention for bracketing a global
            # name in printed/written Elpi syntax, e.g. `indt «nat»`; not
            # part of Elpi's own grammar, so not covered by symbol_re above.
            (r"[«»]", Operator),
            (r":", Keyword.ElpiKeyword),
            (r'"', String.Double, 'elpi-string'),
            (r'`', String.Double, 'elpi-btick'),
            (r'\'', String.Double, 'elpi-tick'),
            # A `{{ ... }}` Coq quotation: valid anywhere coq-elpi compiles
            # Elpi source (including plain .elpi files accumulated via
            # `Elpi Accumulate File`, not just inline in .v files), so it
            # needs handling here too, not just in CoqElpiLexer.
            (r'\{\{', String.Interpol, 'elpi-coq-quote'),
            (r'\{(?!\{)', Text, 'elpi-spill'),
            (r"\(", Punctuation, 'elpi-in-parens'),
            (r'\d[\d_]*', Number.Integer),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),
            (r"[\+\*\-/\^\.]", Operator),
        ],
        '_elpi-comment': [
            # the trailing newline is optional: a `%` comment on the last
            # line of a file with no final newline would otherwise not
            # match at all (and its leading `%` would lex as an Error).
            (r'%[^\n]*\n?', Comment),
            (r'/(?:\\\n)?[*](?:[^*]|[*](?!(?:\\\n)?/))*[*](?:\\\n)?/', Comment),
            (r"\s+", Text.Whitespace),
        ],
        'elpi-indexing-expr':[
            (r'[0-9 _]+', Number.Integer),
            (r'\)', Punctuation, '#pop'),
        ],
        'elpi-type': [
            (r"(ctype\s+)(\")", bygroups(Keyword.Type, String.Double), 'elpi-string'),
            # `..` (DOTS in the real lexer) marks a variadic tail, e.g. the
            # type of the built-in `,` (conjunction) operator, `(func
            # (func) ..)` -- must come before the single-`.` pop rule below.
            (r'\.\.', Keyword.Type),
            (r'->', Keyword.Type),
            (r'prop', Keyword.ElpiMode),
            # `symb`/`symbol` declarations may carry a trailing external-name
            # override, e.g. `symb sumof : ... -> myType = "1".` (as seen
            # throughout builtin-doc/*.elpi); a bare string otherwise has no
            # rule in this state (only the `ctype "..."` case above does).
            (r'"', String.Double, 'elpi-string'),
            (constant_re, Keyword.Type),
            # a nested parenthesised type may itself list several
            # comma-separated components, e.g. `(func K, K -> cmp)`.
            (r',', Text),
            (r"\(|\)", Keyword.Type),
            (r"\.", Text, '#pop'),
            include('_elpi-comment'),
        ],
        'elpi-symb-item': [
            (r":", Keyword.ElpiKeyword),
            include('elpi-type'),
        ],
        'elpi-chr-rule-start': [
            (r"\{", Punctuation, 'elpi-chr-rule'),
            include('_elpi-comment'),
        ],
        'elpi-chr-rule': [
           (r"\brule\b", Keyword.ElpiKeyword),
           (r"\\", Keyword.ElpiKeyword),
           (r"\}", Punctuation, '#pop:2'),
           include('elpi'),
        ],
        'elpi-pred-item': [
            (r"[io]:", Keyword.ElpiMode),
            (r"\.", Text, '#pop'),
            (r",", Keyword.ElpiMode),
            include('_elpi-inner-pred-fun'),
            (r"\)", Keyword.ElpiMode, '#pop'),
            (r"\(", Keyword.Type, '_elpi-type-item'),
            include('_elpi-comment'),
            include('_elpi-type-item'),
        ],
        'elpi-func-item': [
            (constant_re, Keyword.Type),
            (r"\.", Text, '#pop'),
            (r",", Keyword.ElpiMode),
            (r'->', Keyword.ElpiMode),
            include('_elpi-inner-pred-fun'),
            (r"\)", Keyword.ElpiMode, '#pop'),
            (r"\(", Keyword.Type, '_elpi-type-item'),
            include('_elpi-comment'),
            include('_elpi-type-item'),
        ],
        '_elpi-inner-pred-fun': [
            (r"(\()(\s*)(pred)", bygroups(Keyword.ElpiMode,Text.Whitespace,Keyword.ElpiKeyword), 'elpi-pred-item'),
            (r"(\()(\s*)(func)", bygroups(Keyword.ElpiMode,Text.Whitespace,Keyword.ElpiKeyword), 'elpi-func-item'),
        ],
        '_elpi-type-item': [
            (r'->', Keyword.Type),
            (constant_re, Keyword.Type),
            include('_elpi-inner-pred-fun'),
            (r"\(", Keyword.Type, '#push'),
            (r"\)", Keyword.Type, '#pop'),
            include('_elpi-comment'),
        ],

        ''

        'elpi-btick': [
            (r'[^` ]+', String.Double),
            (r'`', String.Double, '#pop'),
        ],
        'elpi-tick': [
            (r'[^\' ]+', String.Double),
            (r'\'', String.Double, '#pop'),
        ],
        'elpi-string': [
            (r'[^\"]+', String.Double),
            (r'"', String.Double, '#pop'),
        ],
        # A `{{ ... }}` Coq quotation reached from plain Elpi source (see
        # the 'elpi' state above). Delegates ordinary text to the full
        # CoqLexer, and handles `lp:` antiquotation re-entry into Elpi --
        # this was sketched (but never enabled, and never had a `using`
        # import to make it work) as `elpi-quote`/`elpi-quote-exit` in the
        # original coq-elpi Alectryon driver this module is vendored from.
        'elpi-coq-quote': [
            (r'\}\}', String.Interpol, '#pop'),
            (r"\s+", Text.Whitespace),
            (r"(lp:)(\{\{)", bygroups(String.Interpol, String.Interpol), 'elpi-coq-quote-exit'),
            # antiquoted names aren't limited to uppercase unification
            # variables, e.g. `pi a\ ... {{ lp:a -> Type }}` antiquotes the
            # lowercase nominal constant bound by `pi`; a bare `_` (the
            # anonymous variable) is also legal but isn't matched by
            # `constant_re` itself (its `_`-prefixed alternative requires at
            # least one more character), so it needs its own alternative.
            (rf"(lp:)({constant_re}|_)", bygroups(String.Interpol, Name.ElpiVariable)),
            # `lp:(...)` antiquotes an arbitrary Elpi expression, not just a
            # single variable, e.g. `lp:(Ety x y)`; lex its content with the
            # full Elpi ruleset (nested parens included) up to the matching
            # `)`, same as a bare `(...)` does at the top 'elpi' level. (The
            # previous rule here -- `(lp:\()([A-Za-z]+)( )([^)]*)(\))` --
            # only worked for a single-identifier head followed by a flat,
            # non-nested rest, e.g. `lp:(Ety x y)`; it mismatched on
            # anything with its own nested parens, e.g. `lp:(f (g x))`.)
            (r"(lp:)(\()", bygroups(String.Interpol, Punctuation), 'elpi-in-parens'),
            (r"((?!lp:|\}\})(.|\n))+", using(CoqLexer)),
        ],
        'elpi-coq-quote-exit': [
            include('elpi'),
            (r'\}\}', String.Interpol, '#pop'),
        ],
        'elpi-spill': [
            # opening uses a lookahead, not `\{[^\{]`, to tell a lone `{`
            # apart from a nested `{{` quotation (handled by `include`d
            # 'elpi' below) without consuming the character that follows.
            # Closing needs no such care: a `{{...}}` quotation opened from
            # within a spill is popped entirely by its own
            # 'elpi-coq-quote' state before control ever returns here, so
            # any `}` seen at this level always means "close this spill" --
            # even when immediately followed by another closing `}`, e.g.
            # the second `}` in `{std.max {a} {b}} + 1`, which closes the
            # *outer* spill right after this one closes the inner.
            # Requiring a non-`}` lookahead here (as `\}[^\}]` used to,
            # consuming two characters) would fail to match exactly that
            # case -- and is also what made a `namespace X { ... }` block
            # (mis-lexed as a spill, having no dedicated rule of its own)
            # error out on its closing `}` whenever it was immediately
            # followed by more input.
            (r'\{(?!\{)', Text, '#push'),
            (r'\}', Text, '#pop'),
            include('elpi'),
        ],
        'elpi-in-parens': [
            (r"\(", Punctuation, '#push'),
            include('elpi'),
            (rf"(\))(:[A-Za-z0-9_ ]*)?", bygroups(Punctuation,Name.ElpiVariable), '#pop'),
        ],
    }


# == Coq + embedded Elpi ======================================================


class CoqElpiLexer(CoqLexer, ElpiLexer):
    """Coq's lexer, extended to recognize ``lp:{{ ... }}`` quotations (and
    the ``lp:Name`` / ``lp:(Name ...)`` antiquotations) as embedded Elpi.

    Also teaches the Coq lexer about coq-elpi's own vernacular (``Elpi
    Command``, ``Elpi Tactic``, ...), matching what ``etc/tutorial_style.rst``
    used to register with Alectryon via its
    ``:alectryon/pygments/coq/cmd:``/``:alectryon/pygments/coq/tacn:``
    docinfo fields.
    """

    # coq-elpi's own vernacular is not known to CoqLexer.kwds['cmd']/['tacn'];
    # match it directly rather than trying to splice it into a base-class
    # regex that was already compiled at CoqLexer's class-definition time.
    _coq_elpi_cmd_re = words(
        ['Elpi', 'Command', 'Tactic', 'Program', 'Accumulate', 'Typecheck',
         'Export', 'Db', 'Query', 'Trace', 'Bound', 'Steps'],
        prefix=r'\b', suffix=r'\b')
    _coq_elpi_tacn_re = words(['elpi'], prefix=r'\b', suffix=r'\b')

    tokens = {
      'root': [
            (_coq_elpi_cmd_re, Keyword.Namespace),
            (_coq_elpi_tacn_re, Name.Builtin),
            # No clue what inherit would do here, so we copy Coq's ones
            include('_basic'),
            include('_vernac'),
            include('_keywords'),
            include('_other'),
      ],
      '_quotations': [
            (r"lp:\{\{",String.Interpol, 'elpi'),
            (r"(lp:)([A-Za-z_0-9']+)",bygroups(String.Interpol, Name.ElpiVariable)),
            (r"(lp:)(\()([A-Z][A-Za-z_0-9']*)([a-z0-9 ]+)(\))",bygroups(String.Interpol,String.Interpol,Name.ElpiVariable,Text,String.Interpol)),
      ],
      'antiquotation': [
            (r"\}\}",String.Interpol,'#pop'),
            include('root')
      ],
      'elpi': [
            (r"\}\}",String.Interpol,'#pop'),
            (r"\b(global|sort|app|fun|let|prod|match|fix)\b", Keyword.ElpiKeyword),
            (r"\{\{(:[a-z]+)?",String.Interpol,'antiquotation'), # back to Coq
            inherit
      ],
      '_other': [
          include('_quotations'),
          inherit
      ],

    }


__all__ = ["CoqLexer", "ElpiLexer", "CoqElpiLexer"]
