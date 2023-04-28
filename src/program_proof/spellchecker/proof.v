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

(* NOTE: (about using the same tag for secrecy and integrity)
   Having (secrecy, integrity, ownership) as in Nickel means that if a thread
   owns `t`, then it can both declassify t and *and* endorse t. I was originally
   planning on having the tag type by nat/u64, and reusing the same tag `t` for
   secrecy and integrity. E.g. the number 37 can show up as part of a secrecy
   label, and also as part of an integrity label. This poses a problem when
   putting 37 in the owned label, since it would mean both endorsement and
   declassification, even though only one might be desired.

   For now, will make sure to never have the same number used for both secrecy
   and integrity.
 *)

(* synonymous with "category" in histar lingo. *)
Definition tag := nat.

Module label.
Record t:= mk {
    s:gset tag; (* secrecy: larger → more access to secrets *)
    i:gset tag; (* integrity: larger → higher integrity *)
    o:gset tag; (* owned: larger → more things that this can declassify & endorse *)
}.

(* just here for comparison *)
Definition classical_leadsto (L1 L2:t) :=
  (L1.(s) ⊆ L2.(s)) ∧ (L2.(i) ⊆ L1.(i))
.

(* Anything that L1 owns, it can freely "declassify". Anything that L2 owns, it
   can freely be "influenced from" without violating its integrity.
 *)
Definition leadsto L1 L2 :=
  (L1.(s) ∖ L1.(o)  ⊆ L2.(s)) ∧ (L2.(i) ∖ L2.(o)  ⊆ L1.(i) ∪ L1.(o))
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
   format "'[hv' 'DWP'  e1  '&'  e2  '/' @  '[' L  ']' '/' {{  Φ  } } ']'") : bi_scope.

Definition CreateFileWithContents: val.
Admitted.

Definition SpawnProcAtLabel: val.
Admitted.

Definition RunAtLabel: val.
Admitted.

Context {t_s t_i:tag}.
Definition fileL := label.mk {[ t_s ]} {[ t_i ]} ∅.

(* the boot program has cw so it can write to cw (writing to a file requires
   thread ⤳ file and file ⤳ thread). *)
(* These should be categories that are allocated by the boot program, but don't
   want to bother with that syscall right now. *)
Definition bootL := label.mk {[ t_s ]} {[ t_i ]} ∅.

Definition boot : val :=
  λ: "secret" "spellchecker" "adversary",
  (* TODO: allocate a category? *)
  (* write a file in that category *)
  let: "fname" := CreateFileWithContents (label_val fileL) "secret" in
  SpawnProcAtLabel "spellchecker" "fname";;
  RunAtLabel "adversary" #()
.

(*
  WP e1 & e2 @ L {{ Φ }} means:
  1.) If σ1 ≈L σ2, then σ1' ≈L σ2'.
  2.) ???

  Idea behind definition/model for WP:
  at the end of the day, we'll apply soundness of a DWP for only a specific
  label Lclosed. All the sub-DWPs we want to use are also specifically with
  respect to Lclosed. The many running threads, however, will have all sorts of
  different labels.
  As part of proving soundness, maintain invariant that σ1 ≈L σ2 currently.
  Consider a running thread with label L'. If
  a.) L' ⤳ Lclosed, then (maybe) we can deduce that σ1 ≈L' σ2.

  One possibility: allow for "2-values" in points-tos.
  Instead of having "fname f↦l secret1 ∗ fname f↦r secret2" in context, have
  "fname f↦2 secret", where the type of secret is
    (λ world, if world = left then secret1 else return secret2).
  Define (fname f↦2 secret) := left ∗ right.
 *)

(*
  Step 1: no "wrap".
  Want to show that left and right is indistinguishable to adversaryL.
  That will imply that the return value of adversaryL is equivalent.

  Step 2: with "wrap", DWP won't work. See next note.
*)

(*
  DWP is all about dealing with non-determinism of multithreading and
  "internally observable timing" [Sabelfeld and Sands].
  It insists that that number of threads in the left and right worlds is
  identical, and imagines an execution in which the scheduler in the left and
  right world picks the exact same threadId to schedule at each step. If one of
  the worlds has an extra thread, they are considered inequivalent by the
  bisimulation. If one of the threads takes an extra step, the bisimulation will
  likely break.

  E.g. if the wrap program clears out every file that has a spelling error, then
  the wrap program may terminate immediately, meaning there were no misspelled
  words, or might run for a very long time, indicating there were lots of
  misspellings.
 *)

Theorem dwp_boot secret1 secret2 (spellchecker adversary:val) :
  ∀ Φ,
  (* must return the same values in the left and right *)
  (∀ v, Φ v v) -∗
  DWP (boot #secret1 spellchecker adversary) &
      (boot #secret2 spellchecker adversary)
          @ bootL {{ Φ }}.
Proof.
  iIntros (?) "HΦ".
Admitted.

End proof.
