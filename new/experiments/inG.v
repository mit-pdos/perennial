Require Import New.proof.proof_prelude.

(* This asserts that Σ has all the stuff that specified package requires. *)
Axiom pkgG : go_string → gFunctors → Set.
Existing Class pkgG.

(* This asserts that the specified package requires the specified cmra. *)
Axiom pkg_inG : go_string → cmra → Set.
Existing Class pkg_inG.

(* Combines the above two to conclude an [inG]. This is quite an unreadble
   name.... *)
Axiom pkgG_pkg_inG_inG :
  ∀ pkg Σ A, pkgG pkg Σ → pkg_inG pkg A → inG Σ A.
Global Existing Instance pkgG_pkg_inG_inG.

(* The first directly imports the second. *)
Class pkg_imports (pkg : go_string) (dependency : go_string) : Set.
Existing Class pkg_imports.

Axiom pkgG_pkg_imports : ∀ pkgh pkgl Σ, pkg_imports pkgh pkgl → pkgG pkgh Σ → pkgG pkgl Σ.
Global Existing Instance pkgG_pkg_imports.
Hint Mode pkgG_pkg_imports ! - - - -.

Section test.

Section context.
Axiom contextRA : cmra.
Axiom context_inG : pkg_inG "context" contextRA.
Global Existing Instance context_inG.

Axiom is_Context : ∀ {Σ} `{!inG Σ contextRA}, iProp Σ.
End context.

Section B.
Instance : pkg_imports "B" "context". Qed.
Context `{!pkgG "B" Σ}.
Lemma get_Context :
  True -∗ is_Context.
Proof. Admitted.
End B.
Set Printing Implicit.
About get_Context.
(* PROBLEM: the [is_Context] above actually stands for
  [@is_Context Σ
    (pkgG_pkg_inG_inG "context" Σ contextRA (pkgG_pkg_imports "B" "context" Σ pkg_imports_instance_0 pkgG0)
       context_inG)]
  In other words, its expecting an [is_Context] that refers to an inG found
  specifically by following (B imports context, then context includes contextRA).
 *)

Section C.
Instance : pkg_imports "C" "context". Qed.
Context `{!pkgG "C" Σ}.
Lemma use_Context :
  is_Context -∗ False.
Proof. Admitted.
End C.

Section D.

Instance : pkg_imports "D" "B". Qed.
Instance : pkg_imports "D" "C". Qed.

Context `{!pkgG "D" Σ}.

Lemma use_B_and_C :
  (True : iProp Σ) -∗ False.
Proof.
  iIntros "HB". iDestruct (get_Context with "HB") as "H".
  iDestruct (use_Context with "[H]") as "H".
  {
    iExactEq "H". repeat f_equal.
(*
  trying to prove:
  pkgG_pkg_imports "B" "context" Σ pkg_imports_instance_0
    (pkgG_pkg_imports "D" "B" Σ pkg_imports_instance_2 pkgG0) =
  pkgG_pkg_imports "C" "context" Σ pkg_imports_instance_1
    (pkgG_pkg_imports "D" "C" Σ pkg_imports_instance_3 pkgG0)
*)
Abort.
End D.

End test.
