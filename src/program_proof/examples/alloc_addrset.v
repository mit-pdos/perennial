From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Export slice.
From Perennial.program_proof Require Export proof_prelude.
From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.goose_lang.lib Require Export typed_slice into_val.
From Perennial.Helpers Require Export range_set.

Section alloc_addrset.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section goose.
Context `{!heapGS Σ}.

Implicit Types (m: gmap u64 ()) (addrs: gset u64).

Definition is_addrset (m_ref: loc) addrs: iProp Σ :=
  ∃ m, own_map m_ref (DfracOwn 1) m ∗ ⌜dom m = addrs⌝.

Theorem is_addrset_from_empty (m_ref: loc) :
  own_map m_ref (DfracOwn 1) (∅: gmap u64 ()) -∗ is_addrset m_ref ∅.
Proof.
  iIntros "Hm".
  iExists _; iFrame.
  iPureIntro.
  set_solver.
Qed.

Theorem wp_freeRange (start sz: u64) E :
  uint.Z start + uint.Z sz < 2^64 ->
  {{{ True }}}
    freeRange #start #sz @ E
  {{{ (mref: loc), RET #mref;
      is_addrset mref (rangeSet (uint.Z start) (uint.Z sz)) }}}.
Proof.
  iIntros (Hbound Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewMap).
  iIntros (mref) "Hmap".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (il) "i".
  wp_pures.
  wp_apply (wp_forUpto (λ i, "%Hilower_bound" ∷ ⌜uint.Z start ≤ uint.Z i⌝ ∗
                             "*" ∷ ∃ m, "Hmap" ∷ own_map mref (DfracOwn 1) m ∗
                                        "%Hmapdom" ∷ ⌜dom m = rangeSet (uint.Z start) (uint.Z i - uint.Z start)⌝)%I
            with "[] [Hmap $i]").
  - word.

  - clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & i & %Hibound) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_apply (wp_MapInsert u64 () () with "Hmap"); auto.
    iIntros "Hm".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iSplitR.
    { iPureIntro; word. }
    rewrite /named.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    rewrite Hmapdom.
    replace (uint.Z (word.add i 1) - uint.Z start) with ((uint.Z i - uint.Z start) + 1) by word.
    eapply rangeSet_append_one; eauto.

  - iSplitR; auto.
    rewrite -> rangeSet_diag by word.
    iExists _; iFrame.
    rewrite dom_empty_L; auto.
  - iIntros "(HI&Hil)"; iNamed "HI".
    wp_pures.
    iApply "HΦ"; iFrame.
    iPureIntro; auto.
    rewrite Hmapdom.
    repeat (f_equal; try word).
Qed.

Lemma big_sepM_lookup_unit (PROP:bi) `{Countable K}
  `{!BiAffine PROP, !BiPersistentlyForall PROP} (m: gmap K ()) :
  ⊢@{PROP} [∗ map] k↦_ ∈ m, ⌜m !! k = Some tt⌝.
Proof.
  iDestruct (big_sepM_lookup_holds m) as "Hmap".
  iApply (big_sepM_mono with "Hmap"); simpl; intros.
  destruct x; auto.
Qed.

(* this is superceded by wp_findKey, but that theorem relies in an unproven map
iteration theorem *)
Theorem wp_findKey' mref m E :
  {{{ own_map mref (DfracOwn 1) m }}}
    findKey #mref @ E
  {{{ (k: u64) (ok: bool), RET (#k, #ok);
      ⌜if ok then m !! k = Some tt else True⌝ ∗ (* TODO: easier if this
      promises to find a key if it exists *)
      own_map mref (DfracOwn 1) m
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (found_l) "found".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ok_l) "ok".
  wp_pures.
  wp_apply (wp_MapIter _ _ _ _ _
                       (∃ (found: u64) (ok: bool),
                           "found" ∷ found_l ↦[uint64T] #found ∗
                           "ok" ∷ ok_l ↦[boolT] #ok ∗
                           "%Hfound_is" ∷ ⌜if ok then m !! found = Some tt else True⌝)
                       (λ k _, ⌜m !! k = Some tt⌝)%I
                       (λ _ _, True)%I
                       with "Hmap [found ok]").
  - iExists _, _; iFrame.
  - iApply big_sepM_lookup_unit.
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
      auto.
  - iIntros "(Hown_map&HI&_HQ)"; iNamed "HI".
    wp_pures.
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ"; iFrame.
    auto.
Qed.

Theorem wp_findKey mref free E :
  {{{ is_addrset mref free }}}
    findKey #mref @ E
  {{{ (k: u64) (ok: bool), RET (#k, #ok);
      ⌜if ok then k ∈ free else free = ∅⌝ ∗
      is_addrset mref free
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (found_l) "found".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ok_l) "ok".
  wp_pures.
  iDestruct "Hmap" as (m) "[Hmap %Hmapdom]".
  wp_apply (wp_MapIter_fold _ _ _ (λ mdone, ∃ (found: u64) (ok: bool),
                           "found" ∷ found_l ↦[uint64T] #found ∗
                           "ok" ∷ ok_l ↦[boolT] #ok ∗
                           "%Hfound_is" ∷ ⌜if ok then m !! found = Some tt else mdone = ∅⌝)%I
           with "Hmap [found ok]").
  - iExists _, _; by iFrame.
  - clear Φ.
    iIntros (mdone k v) "!>".
    iIntros (Φ) "(HI&(%&%)) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    + wp_store. wp_store.
      iApply "HΦ".
      iExists _, _; iFrame.
      destruct v; auto.
    + iApply "HΦ".
      iExists _, _; iFrame.
      auto.
  - iIntros "[Hm HI]"; iNamed "HI".
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ".
    destruct ok.
    + iSplitR.
      { iPureIntro.
        rewrite -Hmapdom.
        apply elem_of_dom; eauto. }
      iExists _; by iFrame "∗%".
    + iSplitR.
      { iPureIntro.
        rewrite -Hmapdom; subst.
        rewrite dom_empty_L //. }
      iExists _; by iFrame "∗%".
Qed.

Theorem wp_mapRemove m_ref remove_ref free remove E :
  {{{ is_addrset m_ref free ∗ is_addrset remove_ref remove }}}
    mapRemove #m_ref #remove_ref @ E
  {{{ RET #(); is_addrset m_ref (free ∖ remove) ∗ is_addrset remove_ref remove }}}.
Proof.
  iIntros (Φ) "[His_free His_remove] HΦ".
  rewrite /mapRemove.
  wp_pures.
  iDestruct "His_remove" as (m) "[His_remove %Hdom]".
  wp_apply (wp_MapIter_2 _ _ _ _ _
                         (λ mtodo mdone, is_addrset m_ref (free ∖ dom mdone))
              with "His_remove [His_free] [] [HΦ]").
  - rewrite dom_empty_L.
    rewrite difference_empty_L.
    iFrame.

  - clear Hdom m Φ.
    iIntros (k [] mtodo mdone) "!>".
    iIntros (Φ) "[His_free %Hin] HΦ".
    wp_call.
    iDestruct "His_free" as (m) "[His_free %Hdom]".
    wp_apply (wp_MapDelete with "His_free").
    iIntros "Hm".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    rewrite /map_del dom_delete_L.
    set_solver.
  - iIntros "[Hremove Hfree]".
    wp_pures.
    iApply "HΦ".
    rewrite Hdom.
    by iFrame.
Qed.

Theorem wp_SetAdd mref used addr_s q (addrs: list u64) E :
  {{{ is_addrset mref used ∗ own_slice_small addr_s uint64T q addrs }}}
    SetAdd #mref (slice_val addr_s) @ E
  {{{ RET #(); is_addrset mref (used ∪ list_to_set addrs) ∗
               own_slice_small addr_s uint64T q addrs }}}.
Proof.
  iIntros (Φ) "(Hused&Haddrs) HΦ".
  rewrite /SetAdd; wp_pures.
  wp_apply (wp_forSlicePrefix (λ done todo, is_addrset mref (used ∪ list_to_set done))
                              with "[] [Hused $Haddrs]").

  - clear Φ.
    iIntros (? a ? ? _) "!>".
    iIntros (Φ) "Hused HΦ".
    wp_pures.
    iDestruct "Hused" as (m) "[Hused %Hdom]".
    wp_apply (wp_MapInsert _ _ () with "Hused").
    { auto. }
    iIntros "Hm".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    set_solver.
  - simpl.
    iExactEq "Hused".
    f_equal.
    set_solver.
  - iIntros "[Hs Haddrs]".
    wp_pures. iApply "HΦ"; by iFrame.
Qed.

End goose.
End alloc_addrset.
