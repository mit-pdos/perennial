From Perennial.program_proof Require Import grove_prelude.

Section main.

Context `{!heapGS Σ}.
Definition Spec (A R:Type): Type := A → (R → iProp Σ) → iProp Σ.

Example ex_spec1 : Spec nat nat :=
  λ args Φ, (Φ 0%nat).

(* This corresponds to `return (args + 1)` *)
Definition ex_spec2 : Spec nat nat :=
  λ args Φ, (Φ (args + 1)%nat).

(* Q: are all `Spec`s monotonic in Φ? *)
(* A: No, as evidences by the following proof. *)
Definition spec_bad : Spec nat nat :=
  λ args Φ, (Φ args -∗ False)%I.
Definition Φbad (n:nat) : iProp Σ := ⌜n > 40⌝.
Definition Ψbad (n:nat) : iProp Σ := ⌜n > 30⌝.

Lemma spec_bad_not_monotonic :
  ⊢ (∀ n, Φbad n -∗ Ψbad n) ∧
  (spec_bad 37%nat Φbad) ∧
  ((spec_bad 37%nat Ψbad) -∗ False)
.
Proof.
  iSplit.
  { iPureIntro. intros. simpl. lia. }
  iSplit.
  { iPureIntro. done. }
  iPureIntro.
  lia.
Qed.

(* One solution is to require individually proving montonicity for each
   [Spec A R] that we write down. Let's shelve this approach for now. *)

(* Another solution is to make specs manifestly monotonic. E.g.
   define an "expression" datatype GhostExpr, so that ∀ (e:GhostExpr),
   (spec_wp' e Φ) is monotonic in Φ.
   Two ways of thinking of GhostExpr:
   1) as a language of ghost code;
   2) as a type "iPred {A:Type} Σ", with special notation + constructors to
      establish monotonicity.

   Let's try 1:
    [return x] = Φ x.
    [A ; B] = [A] -∗ [B].
    [let x | P] = ∃ x, (P x).

   Example: Get_server_spec (from fencing/ctr_proof).

   let latestEpoch | (own_latest_epoch γ latestEpoch (1/2)) &&
   let v | (own_val γ v) &&
   own_val γ v;
   return v

 *)
End main.
