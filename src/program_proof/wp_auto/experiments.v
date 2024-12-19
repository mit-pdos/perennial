From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import basics.

Section basics_proof.
Context `{!heapGS Σ}.

Definition tracker_state (t : loc) (m : gmap u64 u64) : iProp Σ :=
  ∃ (mref : loc),
    "Ht_mref" ∷ t ↦[Tracker :: "m"] #mref ∗
    "Ht_m" ∷ own_map mref 1 m.

Definition tracker_inv (t : loc) : iProp Σ :=
  ∃ (m : gmap u64 u64),
    "Ht_state" ∷ tracker_state t m.

Definition is_tracker (t : loc) : iProp Σ :=
  ∃ (muptr : loc),
    "Ht_mu" ∷ t ↦[Tracker :: "mu"] #muptr ∗
    "#Ht_lock" ∷ is_lock nroot #muptr (tracker_inv t).

Lemma rename_iprop m n {P:iProp Σ} :
  named n P = named m P
.
Proof. reflexivity. Qed.

Instance named_proper {A:Type} : Proper ((λ (_ _:byte_string), True) ==> (@eq A) ==> (eq)) named.
Proof. solve_proper. Qed.

Lemma wp_lookupLocked (t : loc) (m : gmap u64 u64) (k : u64) Htracker :
  {{{ Htracker ∷ tracker_state t m }}}
    Tracker__lookupLocked #t #k
  {{{ (v : u64) (b : bool), RET (#v, #b); Htracker ∷ tracker_state t m ∗
      ("%" ++ Htracker ++ "_ok") ∷ ⌜if b then m !! k = Some v else m !! k = None⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  (* erewrite named_proper. 2-3: done. *)
  rewrite (rename_iprop "Htracker" Htracker).
  iNamed "Hpre".
  iNamed "Htracker".
  wp_rec. wp_pures.
  wp_loadField.

  (*
  iDestruct wp_MapGet as "-#HH".
  { shelve. }
  notypeclasses refine (coq_tactics.tac_specialize_frame _ "HH" _ false _ _ _ _ _ _ _ _ _ _ _).
  { done. }
  { tc_solve. }
  { tc_solve. }
  2:{ done. }
  simpl.
  iFrame.
  notypeclasses refine (coq_tactics.tac_unlock _ _ _).
  iIntros "HH". *)

  wp_apply (wp_MapGet with "[$]").

  (*
  Search ((∃ (_:_), _) ∗ _)%I.
  rewrite sep_exist_r. *)

  iIntros (v ok) "[%Ht_m_lookup Ht_m]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iSplitL.
  { iExists _. iFrame. }
  iPureIntro.
  destruct ok.
  {
    apply map_get_true.
    eauto.
  }
  {
    apply map_get_false in Ht_m_lookup.
    destruct Ht_m_lookup.
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
  wp_rec. wp_pures.
  wp_apply (wp_lookupLocked with "[Ht]").
  { iNamedAccu. }
  iIntros (? b) "[Ht %Hok]".
  wp_pures.
  wp_if_destruct.
  {
    iApply "HΦ". iFrame. done.
  }
  {
    repeat iNamed "Ht".
    wp_loadField.

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

Lemma later_sep_l_intro (P Q:iProp Σ) :
  bi_entails (P ∗ Q)  (▷ P ∗ Q)
.
Proof. iIntros "[$ $]". Qed.

Lemma wp_Lookup (t : loc) (k : u64) :
  {{{ is_tracker t  }}}
    Tracker__Lookup #t #k
  {{{ (v : u64) (b : bool), RET (#v, #b); True }}}.
Proof.
  iIntros (Φ) "Ht HΦ".
  iNamed "Ht".
  wp_rec. wp_pures.
  wp_loadField.

  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Ht]".
  iNamed "Ht".
  wp_apply (wp_lookupLocked with "[$]").
  iIntros (v b) "[Ht_state %Hres]".

  wp_pures.
  wp_loadField.

  iDestruct wp_Mutex__Unlock as "-#HH".
  notypeclasses refine (coq_tactics.tac_specialize_frame _ "HH" _ false _ _ _ _ _ _ _ _ _ _ _).
  { done. }
  { tc_solve. }
  { tc_solve. }
  2:{ done. }
  simpl.
  iFrame "∗#".
  iApply later_sep_l_intro.
  unfold tracker_inv.
  iApply sep_exist_r.
  repeat iExists _.
  iFrame.
  notypeclasses refine (coq_tactics.tac_unlock _ _ _).
  iIntros "HH".
  wp_apply "HH".
  wp_pures.

  (*
  wp_apply (wp_Mutex__Unlock with "[Hlocked Ht_state]").
  { iFrame "Ht_lock". iFrame "Hlocked".
    iExists _. iFrame. } *)
  wp_pures.
  iModIntro.
  iApply "HΦ".
  done.
Qed.

End basics_proof.
