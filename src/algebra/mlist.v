From iris.algebra Require Export mlist.
From Perennial.algebra Require Export own_discrete atleast.
Set Default Proof Using "Type".
Import uPred.

Section mlist_ext.
Context `{fmlistG A Σ}.
Implicit Types l : list A.


Global Instance fmlist_discretizable γ q l:
  Discretizable (fmlist γ q l).
Proof. rewrite /fmlist. apply _. Qed.
Global Instance fmlist_lb_discretizable γ l:
  Discretizable (fmlist_lb γ l).
Proof. rewrite /fmlist_lb. apply _. Qed.

End mlist_ext.
