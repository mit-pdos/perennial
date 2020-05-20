From Perennial.Helpers Require Import Map.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import into_val.

Instance unit_IntoVal : IntoVal ().
Proof.
  refine {| to_val := λ _, #();
            IntoVal_def := ();
         |}.
  intros [] [] _; auto.
Defined.

Instance unit_IntoValForType : IntoValForType unit_IntoVal (struct.t unit.S).
Proof.
  constructor; auto.
Qed.

Section goose.
Context `{!heapG Σ}.

Implicit Types (free: gmap u64 ()).

Theorem wp_FreeRange (start sz: u64) :
  int.val start + int.val sz < 2^64 ->
  {{{ True }}}
    FreeRange #start #sz
  {{{ (mref: loc) free, RET #mref;
      is_map mref free ∗
      ⌜∀ (x:u64), int.val start ≤ int.val x < int.val start + int.val sz ->
                  free !! x = Some tt⌝ }}}.
Proof.
  iIntros (Hbound Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewMap () (t:=struct.t unit.S)).
  iIntros (mref) "Hmap".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (il) "i".
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ free, "Hmap" ∷ is_map mref free ∗
      "%Hmap_vals" ∷ ⌜∀ (x:u64), int.val start ≤ int.val x < int.val i ->
                      free !! x = Some tt⌝)%I
            with "[] [Hmap $i]").
  - word.
  - clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & i & %Hibound) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_apply (wp_MapInsert _ _ _ _ () with "Hmap"); auto.
    iIntros "Hm".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
    iPureIntro.
    replace (int.val (word.add i 1)) with (int.val i + 1) by word.
    intros x Hxbound.
    destruct (decide (x = i)); subst.
    + rewrite lookup_insert //.
    + rewrite lookup_insert_ne //.
      apply Hmap_vals.
      assert (int.val x ≠ int.val i) by (apply not_inj; auto).
      word.
  - iExists _; iFrame.
    iPureIntro.
    intros x Hxbound.
    word.
  - iIntros "[HI i]"; iNamed "HI".
    wp_pures.
    iApply "HΦ"; iFrame.
    iPureIntro.
    intros.
    apply Hmap_vals.
    word.
Qed.

Lemma big_sepM_lookup_holds {PROP:bi} `{Countable K} {V} (m: gmap K V) :
  ⊢@{PROP} [∗ map] k↦v ∈ m, ⌜m !! k = Some v⌝.
Proof.
  rewrite big_opM_eq /big_opM_def /curry /=.
  assert (map_Forall (λ (k:K) (v:V), m !! k = Some v) m) as Hmap.
  { apply map_Forall_lookup; auto. }
  apply map_Forall_to_list in Hmap.
  generalize dependent (map_to_list m).
  induction l as [|kv kvs IH]; simpl; intros; auto.
  inversion Hmap; subst.
  destruct kv as [k v].
  iSplitL.
  + simpl in H3; auto.
  + intuition.
Qed.

Lemma big_sepM_lookup_unit (PROP:bi) `{Countable K} (m: gmap K ()) :
  ⊢@{PROP} [∗ map] k↦_ ∈ m, ⌜m !! k = Some tt⌝.
Proof.
  iDestruct (big_sepM_lookup_holds m) as "Hmap".
  iApply (big_sepM_mono with "Hmap"); simpl; intros.
  destruct x; auto.
Qed.

Theorem wp_findKey mref free :
  {{{ is_map mref free }}}
    findKey #mref
  {{{ (k: u64) (ok: bool), RET (#k, #ok);
      ⌜if ok then free !! k = Some tt else True⌝ ∗
      is_map mref free
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (found_l) "found".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ok_l) "ok".
  wp_pures.
  wp_apply (wp_MapIter _ _ _ _
                       (∃ (found: u64) (ok: bool),
                           "found" ∷ found_l ↦[uint64T] #found ∗
                           "ok" ∷ ok_l ↦[boolT] #ok ∗
                           "%Hfound_is" ∷ ⌜if ok then free !! found = Some tt else True⌝)
                       (λ k _, ⌜free !! k = Some tt⌝)%I
                       (λ _ _, True)%I
                       with "Hmap [found ok]").
  - iExists _, _; iFrame.
  - (* TODO: should be able to prove this with iPureIntro and then something
    simple, but there's no IntoPure for big_sepM *)
    iApply big_sepM_lookup_unit.
  - iIntros (k v) "!>".
    clear Φ.
    iIntros (Φ) "[HI %Helem] HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    + wp_store. wp_store.
      iApply "HΦ".
      iSplitL; auto.
      iExists _, _; iFrame.
      auto.
    + iApply "HΦ".
      iSplitL; auto.
      iExists _, _; iFrame.
      apply negb_false_iff in Heqb; subst.
      auto.
  - iIntros "(His_map&HI&_HQ)"; iNamed "HI".
    wp_pures.
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ"; iFrame.
    auto.
Qed.

End goose.
