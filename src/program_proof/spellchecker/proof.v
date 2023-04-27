From Perennial.program_proof Require Import grove_prelude.

(*
  NOTE:
  Consider having (secrecy, integrity, ownership) for every object.
  In Hi/NiStar, only threads can have ownership. So, the "leads to" relation
  from NiStar actually implies the "can be read by" (⊑R) and "can write to" (⊑W)
  relations, since the object's O set will be ∅.

  E.g. In terms of the extra "can read from/write to" relations,
  the Nickel paper notes that:
    L_T ⊑W L_O → L_O ⊑R L_T' → L_T ⤳ L_T'.
  Equivalently, without introducing the extra relations,
    If L2.owned = ∅, then L1 ⤳ L2 → L2 ⤳ L3 → L1 ⤳ L3.
  Proof for secrecy part: L1.secrecy - L1.owned ⊆ L2.secrecy ⊆ L3.secrecy - L2.owned.

  So, HiStar's IFC policy is intransitive *only at threads* (since objets have
  L2.owned = ∅).
 *)

(* synonymous with "category" in histar lingo. *)
Definition tag := nat.

Module label.
Record t:= mk {
    s:gset tag; (* secrecy: larger → more access to secrets *)
    i:gset tag; (* integrity: larger → higher integrity *)
}.

(* just here for comparison *)
Definition classical_leadsto (L1 L2:t) :=
  (L1.(s) ⊆ L2.(s)) ∧ (L2.(i) ⊆ L1.(i))
.

(* anything that L1 owns, it can freely "declassify".
 *)
Definition leadsto (LT Lobj:t) (OT:gset tag) :=
  (LT.(s) ∖ OT  ⊆ L2.(s)) ∧ (L2.(i) OT  ⊆ L1.(i))
.
End label.

Section proof.

Context `{!heapGS Σ}.

Definition label_val : label.t → val.
Admitted.

Definition dwp (L:label.t) : goose_lang.expr → goose_lang.expr → (val → val → iProp Σ) → iProp Σ.
Admitted.

Notation "'DWP' e1 & e2 @ L {{ Φ } }" := (dwp L e1%E e2%E Φ)
  (at level 20, e1, e2, Φ at level 200,
   format "'[hv' 'DWP'  e1 & e2  '/' @  '[' L  ']' '/' {{  Φ  } } ']'") : bi_scope.

Definition CreateFileWithContents: val.
Admitted.

Definition SpawnProcAtLabel: val.
Admitted.

Definition RunAtLabel: val.
Admitted.

Context {c:tag}.
Definition fileL := label.mk {[ c ]} {[ c ]}.

Definition boot : val :=
  λ: "secret" "spellchecker" "adversary",
  (* TODO: allocate a category? *)
  (* write a file in that category *)
  let: "fname" := CreateFileWithContents (label_val fileL) "secret" in
  SpawnProcAtLabel "spellchecker" "fname";;
  RunAtLabel "adversary" #()
.

Theorem dwp_boot :
  ∀ secret1 secret2 (spellcheckerP adversaryP:val) Φ,
  (* must return the same values in the left and right *)
  (∀ v, Φ v v) -∗
  DWP (boot #secret1 spellcheckerP adversaryP) &
      (boot #secret2 spellcheckerP adversaryP)
          @ bootL {{ Φ }}.
Proof.
  iIntros.
Admitted.

End proof.
