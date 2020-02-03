From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import basic_triples.
From Perennial.goose_lang Require Import map.
Import uPred.

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Lemma map_get_empty def k : map_get (∅, def) k = (def, false).
Proof.
  reflexivity.
Qed.

Lemma map_get_insert k v m def :
  map_get (<[k:=v]> m, def) k = (v, true).
Proof.
  rewrite /map_get.
  rewrite lookup_insert //.
Qed.

Lemma map_get_insert_ne k k' v m def :
  k ≠ k' ->
  map_get (<[k:=v]> m, def) k' = map_get (m, def) k'.
Proof.
  intros Hne.
  rewrite /map_get.
  rewrite lookup_insert_ne //.
Qed.

Lemma map_val_split mv m :
  map_val mv = Some m ->
  {∃ def, mv = MapNilV def ∧ m = (∅, def)} +
  {∃ k v mv' m', mv = MapConsV k v mv' ∧ map_val mv' = Some m' ∧ m = (<[k:=v]> (fst m'), snd m')}.
Proof.
  intros H.
  destruct mv; inversion H; subst; [ left | right ].
  - exists mv; auto.
  - destruct mv; try solve [ inversion H1 ].
    destruct mv1; try solve [ inversion H1 ].
    destruct mv1_1; try solve [ inversion H1 ].
    destruct l; try solve [ inversion H1 ].
    destruct_with_eqn (map_val mv2); try solve [ inversion H1 ].
    destruct p; inversion H1; subst; clear H1.
    eexists _, _, _, _; intuition eauto.
Qed.

Definition wp_MapGet stk E mref (m: gmap u64 val * val) mv k :
  {{{ mref ↦ Free mv ∗ ⌜map_val mv = Some m⌝ }}}
    MapGet #mref #k @ stk; E
  {{{ v ok, RET (v, #ok); ⌜map_get m k = (v, ok)⌝ ∗
                          mref ↦ Free mv }}}.
Proof.
  iIntros (𝛷) "[Hmref %] H𝛷".
  wp_call.
  wp_load.
  wp_pure (_ _).
  iAssert (∀ v ok, ⌜map_get m k = (v, ok)⌝ -∗ 𝛷 (v, #ok)%V)%I with "[Hmref H𝛷]" as "H𝛷".
  { iIntros (v ok) "%".
    by iApply ("H𝛷" with "[$Hmref]"). }
  iLöb as "IH" forall (m mv H).
  wp_call.
  destruct (map_val_split _ _ H).
  - (* nil *)
    destruct e as [def ?]; intuition subst.
    wp_pures.
    iApply "H𝛷".
    rewrite map_get_empty; auto.
  - destruct e as [k' [v [mv' [m' ?]]]]; intuition subst.
    wp_pures.
    wp_if_destruct.
    + wp_pures.
      iApply "H𝛷".
      rewrite map_get_insert //.
    + iApply "IH".
      * eauto.
      * iIntros (v' ok) "%".
        iApply "H𝛷".
        rewrite map_get_insert_ne //; try congruence.
        destruct m'; eauto.
Qed.

End heap.
