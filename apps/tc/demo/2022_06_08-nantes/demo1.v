From elpi Require Import compiler.
From Coq.Program Require Export Basics.
From Coq Require Export Setoid.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.

Elpi Debug "simple-compiler".

Module A.
  Set Implicit Arguments.

  Class MyClass {A B} (f : A -> B) : Prop.

  Definition times2 x := x * 2.

  Global Instance myInst: MyClass times2. Qed.

  (* Here we are in coq *)
  Check (_ : MyClass times2).
  Check (_: MyClass (fun x => x * 2)).

  (* Here we are in elpi *)
  Elpi Override TC TC_check All.
  Elpi AddInstances MyClass.

  Check (_ : MyClass times2).

  (* Elpi Trace Browser. *)
  Check (_: MyClass (fun x => x * 2)).

  Module UseAlias1.
    Elpi Accumulate TC_check lp:{{
      :name "rename1"
      tc {{:gref MyClass}} {{MyClass lp:F}} Sol :-
        F = {{fun x => x * 2}},
        coq.say "Found unfold of times2 !",
        tc {{:gref MyClass}} {{MyClass times2}} Sol.
    }}.
    Check (_: MyClass (fun x => x * 2)).
  End UseAlias1.
  
  Module UseAlias2.
    Elpi Accumulate TC_check lp:{{
      :before "rename1"
      :name "rename2"
      tc {{:gref MyClass}} {{MyClass lp:F}} Sol :-
        coq.unify-eq F {{fun _ => _ * 2}} ok,
        coq.say "Found unfold of times2 !",
        tc {{:gref MyClass}} {{MyClass times2}} Sol.
    }}.
    Check (_: MyClass (fun x => x * 2)).
  End UseAlias2.

  Module UseAlias3.
    Elpi Accumulate TC_check lp:{{
      pred alias i:term, o:term.
      alias {{fun x => x * 2}} {{times2}}.
    }}.

    (* Hand alias rule by hand  *)
    Elpi Accumulate TC_check lp:{{
      :before "rename2"
      :name "rename3"
      tc {{:gref MyClass}} {{MyClass lp:F}} Sol :-
        alias F F', 
        coq.say "Found unfold of times2 with alias !",
        tc {{:gref MyClass}} {{MyClass lp:F'}} Sol.
    }}.
    Check (_: MyClass (fun y => y * 2)).
  End UseAlias3.

  Module UseAlias4.
    (* Trying to generalize *)
    Elpi Accumulate TC_check lp:{{
      pred replace-with-alias i:term, o:term.
      replace-with-alias A Sol :- alias A Sol.
      replace-with-alias (app ToReplace) (app Sol) :-
        std.map ToReplace replace-with-alias Sol.
      replace-with-alias A A.

      :before "rename3"
      :name "rename4"
      tc {{:gref MyClass}} T Sol :- !,
        replace-with-alias T T',
        coq.say "Found unfold of times2 with alias2 !",
        tc {{:gref MyClass}} T' Sol.
    }}.
    Check (_: MyClass (fun y => y * 2)).
  End UseAlias4.
End A.
