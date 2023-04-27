From Perennial.program_proof Require Import grove_prelude.

Section proof.

Context `{!heapGS Σ}.
(* TODO: *)
Definition label := nat.

Definition label_val : label → val.
Admitted.

Definition dwp (L:label) : goose_lang.expr → goose_lang.expr → (val → val → iProp Σ) → iProp Σ.
Admitted.

Notation "'DWP' e1 & e2 @ L {{ Φ } }" := (dwp L e1%E e2%E Φ)
  (at level 20, e1, e2, Φ at level 200, only parsing) : bi_scope.

Definition WriteFile : val.
Admitted.

Definition SpawnProc: val.
Admitted.

Context {fileL:label}.
Context {bootL:label}.

Definition boot : val :=
  λ: "secret" "spellchecker" "adversary",
  (* TODO: allocate a category? *)
  (* write a file in that category *)
  WriteFile #(LitString "secret.txt") (label_val fileL);;
  SpawnProc "spellchecker" #() ;;
  "adversary" #()
.

Theorem dwp_boot :
  ∀ secret1 secret2 (spellcheckerP adversaryP:val) Φ,
  (* must return the same values in the left and right *)
  (∀ v, Φ v v) -∗
  DWP (boot #secret1 spellcheckerP adversaryP) &
      (boot #secret2 spellcheckerP adversaryP)
          @ bootL {{ Φ }}.
Proof.
Admitted.

End proof.
