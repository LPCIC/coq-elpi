From elpi Require Import compiler.

Elpi Debug "simple-compiler".
Unset TC_NameFullPath.

Module A.
  Set Implicit Arguments.

  Class MyClass {A B} (f : A -> B) : Prop.

  Definition times2 x := x * 2.

  Global Instance myInst: MyClass times2. Qed.

  (* Here we are in coq *)
  Goal MyClass times2. apply _. Qed.
  Goal MyClass (fun x => x * 2). apply _. Qed.

  (* Here we are in elpi *)
  Elpi Override TC TC_solver All.
  Elpi AddClasses MyClass.
  Elpi AddInstances MyClass.

  Goal MyClass times2. apply _. Qed.

  (* Elpi Trace Browser. *)
  Goal MyClass (fun x => x * 2). Fail apply _. Abort.

  Module UseAlias1.
    Elpi Accumulate TC_solver lp:{{
      :name "rename1"
      tc-MyClass A B F Sol :-
        F = {{fun x => x * 2}},
        coq.say "Found unfold of times2 !",
        tc-MyClass A B {{times2}} Sol.
    }}.
    Goal MyClass (fun x => x * 2). apply _. Qed.
  End UseAlias1.
  
  Module UseAlias2.
    Elpi Accumulate TC_solver lp:{{
      :before "rename1"
      :name "rename2"
      tc-MyClass A B F Sol :-
        coq.unify-eq F {{fun _ => _ * 2}} ok,
        coq.say "Found unfold of times2 !",
        tc-MyClass A B {{times2}} Sol.
    }}.
    Goal MyClass (fun x => x * 2). apply _. Qed.
  End UseAlias2.

  Module UseAlias3.
    Elpi Accumulate TC_solver lp:{{
      pred alias i:term, o:term.
      alias {{fun x => x * 2}} {{times2}}.
    }}.

    (* Hand alias rule by hand  *)
    Elpi Accumulate TC_solver lp:{{
      :before "rename2"
      :name "rename3"
      tc-MyClass A B F Sol :-
        alias F F', 
        coq.say "Found unfold of times2 with alias !",
        tc-MyClass A B F' Sol.
    }}.
    Goal MyClass (fun y => y * 2). apply _. Qed.
  End UseAlias3.

  Module UseAlias4.
    (* Trying to generalize *)
    Elpi Accumulate TC_solver lp:{{
      pred my-replace-with-alias i:term, o:term.
      my-replace-with-alias A Sol :- alias A Sol.
      my-replace-with-alias (app ToReplace) (app Sol) :-
        std.map ToReplace my-replace-with-alias Sol.
      my-replace-with-alias A A.

      :before "rename3"
      :name "rename4"
      tc-MyClass A B T Sol :- !,
        my-replace-with-alias T T',
        coq.say "Found unfold of times2 with alias2 !",
        tc-MyClass A B T' Sol.
    }}.
    Goal MyClass (fun y => y * 2). apply _. Qed.
  End UseAlias4.
End A.
