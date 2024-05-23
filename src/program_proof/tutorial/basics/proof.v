From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import basics.

Section basics_proof.
Context `{!heapGS Σ}.

Definition tracker_state (t : loc) (m : gmap u64 u64) : iProp Σ :=
  ∃ (mref : loc),
    "Ht_mref" ∷ t ↦[Tracker :: "m"] #mref ∗
    "Ht_m" ∷ own_map mref (DfracOwn 1) m.

Definition tracker_inv (t : loc) : iProp Σ :=
  ∃ (m : gmap u64 u64),
    "Ht_state" ∷ tracker_state t m.

Definition is_tracker (t : loc) : iProp Σ :=
  ∃ (muptr : loc),
    "Ht_mu" ∷ t ↦[Tracker :: "mu"] #muptr ∗
    "#Ht_lock" ∷ is_lock nroot #muptr (tracker_inv t).

Lemma wp_lookupLocked (t : loc) (m : gmap u64 u64) (k : u64) :
  {{{ tracker_state t m }}}
    Tracker__lookupLocked #t #k
  {{{ (v : u64) (b : bool), RET (#v, #b); tracker_state t m ∗
      ⌜if b then m !! k = Some v else m !! k = None⌝ }}}.
Proof.
  iIntros (Φ) "Ht HΦ".
  iNamed "Ht".
  wp_call.
  wp_loadField.

  Search impl.MapGet.

  wp_apply (wp_MapGet with "Ht_m").
  iIntros (v ok) "[%Hok Ht_m]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iSplitL.
  { iExists _. iFrame. }
  iPureIntro.
  destruct ok.
  {
    Search map_get lookup.
    apply map_get_true.
    eauto.
  }
  {
    Search map_get lookup.
    apply map_get_false in Hok.
    destruct Hok.
    eauto.
  }
Qed.

Lemma wp_registerLocked (t : loc) (m : gmap u64 u64) (k : u64) (v : u64) :
  {{{ tracker_state t m }}}
    Tracker__registerLocked #t #k #v
  {{{ (b : bool), RET #b;
      if b then
        tracker_state t (<[k := v]> m)
      else
        tracker_state t m }}}.
Proof.
  iIntros (Φ) "Ht HΦ".
  wp_call.
  wp_apply (wp_lookupLocked with "[Ht]").
  { iApply "Ht". }
  iIntros (? b) "[Ht %Hok]".
  wp_pures.
  wp_if_destruct.
  {
    iApply "HΦ". iFrame. done.
  }
  {
    iNamed "Ht".
    wp_loadField.

    Search impl.MapInsert.

    wp_apply (wp_MapInsert u64 u64 with "[Ht_m]").
    { eauto. }
    { iApply "Ht_m". }
    iIntros "Ht_m".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iExists _.
    iFrame.
  }
Qed.

Lemma wp_Lookup (t : loc) (k : u64) :
  {{{ is_tracker t }}}
    Tracker__Lookup #t #k
  {{{ (v : u64) (b : bool), RET (#v, #b); True }}}.
Proof.
  iIntros (Φ) "Ht HΦ".
  iNamed "Ht".
  wp_call.
  wp_loadField.

  Search lock.acquire.

  wp_apply (acquire_spec with "[]").
  { iApply "Ht_lock". }
  iIntros "[Hlocked Ht]".
  iNamed "Ht".
  wp_apply (wp_lookupLocked with "Ht_state").
  iIntros (v b) "[Ht_state %Hres]".

  wp_pures.
  wp_loadField.

  Search lock.release.

  wp_apply (release_spec with "[Hlocked Ht_state]").
  { iFrame "Ht_lock". iFrame "Hlocked".
    iExists _. iFrame. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Register (t : loc) (k : u64) (v : u64) :
  {{{ is_tracker t }}}
    Tracker__Register #t #k #v
  {{{ (b : bool), RET #b; True }}}.
Proof.
  iIntros (Φ) "Ht HΦ".
  iNamed "Ht".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Ht_lock").
  iIntros "[Hlocked Ht]".
  iNamed "Ht".
  wp_pures.
  wp_apply (wp_registerLocked with "Ht_state").
  iIntros (b) "Hb".
  wp_pures.
  wp_loadField.
  destruct b.
  {
    wp_apply (release_spec with "[Hlocked Hb]").
    { iFrame "Ht_lock". iFrame "Hlocked". iModIntro.
      iExists _. iFrame. }
    wp_pures.
    iApply "HΦ".
    done.
  }
  {
    wp_apply (release_spec with "[Hlocked Hb]").
    { iFrame "Ht_lock". iFrame "Hlocked". iModIntro.
      iExists _. iFrame. }
    wp_pures.
    iApply "HΦ".
    done.
  }
Qed.

End basics_proof.
