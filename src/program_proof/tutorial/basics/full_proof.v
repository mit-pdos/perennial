From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import basics.
From iris.base_logic.lib Require Import ghost_map.

Section basics_proof.
Context `{!heapGS Σ}.
Context `{!ghost_mapG Σ u64 u64}.

Definition tracker_state (t : loc) γ (m : gmap u64 u64) : iProp Σ :=
  ∃ (mref : loc),
    "Ht_mref" ∷ t ↦[Tracker :: "m"] #mref ∗
    "Ht_m" ∷ own_map mref (DfracOwn 1) m ∗
    "Ht_g" ∷ ghost_map_auth γ 1 m
.

Definition tracker_inv (t : loc) γ : iProp Σ :=
  ∃ (m : gmap u64 u64),
    "Ht_state" ∷ tracker_state t γ m.

Definition is_tracker (t : loc) γ : iProp Σ :=
  ∃ (muptr : loc),
    "Ht_mu" ∷ t ↦[Tracker :: "mu"] #muptr ∗
    "#Ht_lock" ∷ is_lock nroot #muptr (tracker_inv t γ).

Lemma wp_lookupLocked (t : loc) γ (m : gmap u64 u64) (k : u64) :
  {{{ tracker_state t γ m }}}
    Tracker__lookupLocked #t #k
  {{{ (v : u64) (b : bool), RET (#v, #b); tracker_state t γ m ∗
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

Lemma wp_lookupLocked_success (t : loc) γ (m : gmap u64 u64) (k v : u64) :
  {{{ tracker_state t γ m ∗ k ↪[γ] v }}}
    Tracker__lookupLocked #t #k
  {{{ RET (#v, #true); tracker_state t γ m ∗ k ↪[γ] v }}}
.
Proof.
  iIntros (Φ) "[Ht Hptsto] HΦ".
  iNamed "Ht".
  wp_call.
  wp_loadField.

  Search impl.MapGet.

  wp_apply (wp_MapGet with "Ht_m").
  iIntros (v' ok) "[%Hok Ht_m]".
  wp_pures.
  iModIntro.

  iDestruct (ghost_map_lookup with "Ht_g Hptsto") as %Hlookup.
  unfold map_get in Hok.
  rewrite Hlookup in Hok.
  simpl in Hok.
  injection Hok as ? ?.
  subst.

  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_registerLocked (t : loc) γ (m : gmap u64 u64) (k : u64) (v : u64) :
  {{{ tracker_state t γ m }}}
    Tracker__registerLocked #t #k #v
  {{{ (b : bool), RET #b;
      if b then
        tracker_state t γ (<[k := v]> m) ∗ k ↪[γ] v
      else
        tracker_state t γ m }}}.
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
    iMod (ghost_map_insert with "Ht_g") as "[Ht_g Hptsto]".
    { done. }
    iModIntro.
    iFrame.
  }
Qed.

Lemma wp_Lookup (t : loc) γ (k : u64) :
  {{{ is_tracker t γ }}}
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

Lemma wp_Lookup_success (t : loc) γ (k v : u64) :
  {{{ is_tracker t γ ∗ k ↪[γ] v }}}
    Tracker__Lookup #t #k
  {{{ RET (#v, #true); k ↪[γ] v }}}.
Proof.
  iIntros (Φ) "[Ht Hptsto] HΦ".
  iNamed "Ht".
  wp_call.
  wp_loadField.

  Search lock.acquire.

  wp_apply (acquire_spec with "[]").
  { iApply "Ht_lock". }
  iIntros "[Hlocked Ht]".
  iNamed "Ht".
  wp_apply (wp_lookupLocked_success with "[Ht_state Hptsto]").
  { iFrame. }
  iIntros "[Ht_state Hptsto]".

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

Lemma wp_Register (t : loc) γ (k : u64) (v : u64) :
  {{{ is_tracker t γ }}}
    Tracker__Register #t #k #v
  {{{ (b : bool), RET #b; if b then k ↪[γ] v else True }}}.
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
    iDestruct "Hb" as "[Ht_state Hptsto]".
    wp_apply (release_spec with "[Hlocked Ht_state]").
    { iFrame "Ht_lock". iFrame "Hlocked". iModIntro.
      iExists _. iFrame. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
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
