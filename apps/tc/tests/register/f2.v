From elpi.apps.tc.tests.register Require Export f1.

Goal A 1. apply _. Qed.

Elpi TC Deactivate Observer auto_compiler.

Instance I2 : A 2. Qed.

Goal A 2. Fail apply _. Abort.