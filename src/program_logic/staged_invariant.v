From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop gen_heap.
From Perennial.Helpers Require Import ipm.
From Perennial.program_logic Require Export step_fupd_extra crash_token ghost_var.
From Perennial.algebra Require Import partition gen_heap_names big_op.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO (boolO) (prodO gnameO gnameO)))));
  staging_shot_inG :> inG Σ (csumR (exclR unitO) (agreeR unitO));
  staging_gnames_inG :> gen_heapPreG nat () Σ;
  staging_bunches_inG :> partition_preG nat nat Σ
}.

Definition stagedΣ : gFunctors :=
  #[savedPropΣ; gen_heapΣ nat (); partitionΣ nat nat;
      GFunctor (authR (optionUR (exclR (prodO (boolO) (prodO gnameO gnameO)))));
      GFunctor (csumR (exclR unitO) (agreeR unitO))].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinl (Excl ())).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

Record staged_names :=
  { staging_gnames_names : gen_heap_names;
    staging_bunches_names : gen_heap_names }.

Section definitions.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.

Context (Γ: staged_names).

Instance sghG : gen_heapG nat () Σ :=
  gen_heapG_update_pre (staging_gnames_inG) (staging_gnames_names Γ).

Instance staged_bunches_partitionG : partitionG nat nat Σ :=
  {| partition_heap_inG := gen_heapG_update_pre (partition_heap_preG) (staging_bunches_names Γ) |}.

Notation sphG := (@partition_heap_inG _ _ _ _ _ _ _ _ _ staged_bunches_partitionG).

Definition pN := nroot.@"pending".
Definition cN := nroot.@"crash".
Definition bN := nroot.@"bunchstore".

Definition crash_prop_wf (σdom: gmap nat unit) Qc :=
  ([∗ map] i↦_ ∈ σdom, ∃ (γ: gname), meta (hG := sghG) i cN γ ∗ saved_prop_own γ (Qc i))%I.

Definition bunch_wf k E E' (Ps Pr Qc: nat → iProp Σ) i bunch :=
  (∃ (γ: gname) (b: bool) γprop_stored γprop_remainder, meta (hG := sphG) i bN γ ∗
     own γ (● Excl' (b, (γprop_stored, γprop_remainder))) ∗
     saved_prop_own γprop_stored (Ps i) ∗
     saved_prop_own γprop_remainder (Pr i) ∗
     □ (C -∗ Ps i -∗ if b then |={E, E'}_k=> ([∗ set] j∈bunch, ▷ Qc j) ∗ (▷ Pr i)
                            else ([∗ set] j∈bunch, ▷ Qc j) ∗ (▷ Pr i)))%I.

Definition bunches_wf k E E' σ (Ps Pr Qc: nat → iProp Σ) :=
  ([∗ map] i↦bunch ∈ σ, bunch_wf k E E' Ps Pr Qc i bunch)%I.

Definition bunch_live (Ps: nat → iProp Σ) i := Ps i.
Definition bunch_crashed (Pr Qc: nat → iProp Σ) i bunch :=
  (C ∗ ▷ Pr i ∗ ([∗ set] j ∈ bunch, ▷ Qc j ∨ (∃ γ, meta (hG := sghG) j pN γ ∗ staged_done γ)))%I.

(*
Definition inv_crashed (σ: gmap nat (gset nat)) (Pr Qc: nat → iProp Σ) :=
  (C ∗ [∗ map] i↦bunch∈ σ, Pr i ∗ ([∗ set] j ∈ bunch, ∃ γ, meta (hG := sghG) j pN γ ∗ (Qc j ∨ staged_done γ)))%I.

Definition inv_live (σ: gmap nat (gset nat)) (Ps: nat → iProp Σ) :=
  ([∗ map] i↦_∈ σ, Ps i)%I.
*)

Definition inv_status σ (Ps Pr Qc: nat → iProp Σ) :=
  ([∗ map] i ↦ bunch ∈ σ, bunch_live Ps i ∨ bunch_crashed Pr Qc i bunch)%I.

Definition staged_inv (N: namespace) (k: nat) (E E': coPset) : iProp Σ :=
  (inv N (∃ σ σdom  (Ps Pr Qc: nat → iProp Σ),
             ⌜ dom (gset nat) σdom = union_partition σ ⌝ ∗
             partition_ctx σ ∗
             gen_heap_ctx σdom ∗
             crash_prop_wf σdom Qc ∗
             bunches_wf k E E' σ Ps Pr Qc ∗
             inv_status σ Ps Pr Qc))%I.

(*
Definition staged_inv `{!invG Σ, !crashG Σ, !stagedG Σ} (N: namespace)(L: Type) `{Countable L}
           k E E' (γ γ': gname) (Qc: L → iProp Σ) : iProp Σ :=
  (inv N (∃ γprop_stored γprop_remainder Ps Pr,
             own γ (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             □ (C -∗ Ps -∗ |={E, E'}_k=> Qc ∗ Pr) ∗
             (Ps ∨ (Pr ∗ C ∗ staged_done γ'))))%I.
*)

Definition staged_bundle (Q Q': iProp Σ) b (bundle: gset nat) : iProp Σ :=
  (∃ i γ γprop γprop' Qalt Qalt',
      mapsto (hG := sphG) i 1 bundle ∗
      meta (hG := sphG) i bN γ ∗
      own γ (◯ Excl' (b, (γprop, γprop'))) ∗
      ▷ (□ (▷ Qalt -∗ ▷ Q)) ∗ ▷ (□ (▷ Qalt' -∗ ▷ Q')) ∗
      saved_prop_own γprop Qalt ∗
      saved_prop_own γprop' Qalt').

(*
Definition staged_crash (i: nat) (P: iProp Σ) : iProp Σ :=
  (∃ γ, meta (hG := sghG) i cN γ ∗ saved_prop_own γ P).
*)

Definition staged_crash (P: iProp Σ) s : iProp Σ :=
  (∃ Ps, ([∗ set] i ∈ s, ∃ γ, meta (hG := sghG) i cN γ ∗ saved_prop_own γ (Ps i)) ∗
         □ (▷ P -∗ ([∗ set] i ∈ s, ▷ Ps i))).

Definition staged_crash_pending (P: iProp Σ) i : iProp Σ :=
  (mapsto (hG := sghG) i 1 ()) ∗
  (∃ γ, meta (hG := sghG) i pN γ ∗ staged_pending γ) ∗
  (∃ γ, meta (hG := sghG) i cN γ ∗ saved_prop_own γ P).

Definition bunch_wf_later k E E' (Ps Pr Qc: nat → iProp Σ) i bunch :=
  (∃ (γ: gname) (b: bool) γprop_stored γprop_remainder, meta (hG := sphG) i bN γ ∗
     own γ (● Excl' (b, (γprop_stored, γprop_remainder))) ∗
     ▷ saved_prop_own γprop_stored (Ps i) ∗
     ▷ saved_prop_own γprop_remainder (Pr i) ∗
     ▷ □ (C -∗ Ps i -∗ if b then |={E, E'}_k=> ([∗ set] j∈bunch, ▷ Qc j) ∗ (▷ Pr i)
                         else ([∗ set] j ∈ bunch, ▷ Qc j) ∗ (▷ Pr i)))%I.

Definition bunches_wf_later k E E' σ (Ps Pr Qc: nat → iProp Σ) :=
  ([∗ map] i↦bunch ∈ σ, bunch_wf_later k E E' Ps Pr Qc i bunch)%I.

Lemma bunches_wf_to_later k E E' σ Ps Pr Qc Em:
  ▷ bunches_wf k E E' σ Ps Pr Qc ={Em}=∗
  bunches_wf_later k E E' σ Ps Pr Qc.
Proof.
  iIntros "Hb". rewrite /bunches_wf.
  iDestruct (big_sepM_later with "Hb") as "Hb".
  iApply big_sepM_fupd.
  iApply (big_sepM_mono with "Hb").
  iIntros (???) "H".
  iDestruct "H" as (????) "H".
  iDestruct "H" as "(>Hm&>Hown&Hsaved1&Hsaved2&Hwand)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

Lemma bunches_wf_pers_lookup k E E' σ Ps Pr Qc i s γ (b: bool) γprop_stored γprop_remainder:
  σ !! i = Some s →
  meta (hG := sphG) i bN γ -∗
  own γ (◯ Excl' (b, (γprop_stored, γprop_remainder))) -∗
  bunches_wf k E E' σ Ps Pr Qc -∗
     saved_prop_own γprop_stored (Ps i) ∗
     saved_prop_own γprop_remainder (Pr i) ∗
     □ (C -∗ Ps i -∗ if b then |={E, E'}_k=> ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i)
                            else ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i))%I.
Proof.
  iIntros (?) "#Hm Hown Hbunch".
  rewrite /bunches_wf.
  iDestruct (big_sepM_lookup with "Hbunch") as "Hb"; first eauto.
  rewrite /bunch_wf. iDestruct "Hb" as (γ' ???) "(?&Hown'&?&?&?)".
  iDestruct (meta_agree with "Hm [$]") as %Heq. subst.
  unify_ghost.
  iFrame.
Qed.

Lemma bunches_wf_later_pers_lookup k E E' σ Ps Pr Qc i s γ (b: bool) γprop_stored γprop_remainder:
  σ !! i = Some s →
  meta (hG := sphG) i bN γ -∗
  own γ (◯ Excl' (b, (γprop_stored, γprop_remainder))) -∗
  ▷ bunches_wf k E E' σ Ps Pr Qc -∗
     ▷ (saved_prop_own γprop_stored (Ps i) ∗
        saved_prop_own γprop_remainder (Pr i) ∗
        □ (C -∗ Ps i -∗ if b then |={E, E'}_k=> ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i)
                            else ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i)))%I.
Proof.
  iIntros. iNext. iApply (bunches_wf_pers_lookup with "[$] [$] [$]"); eauto.
Qed.

Lemma bunches_wf_later_pers_lookup_weak k E E' σ Ps Pr Qc i s:
  σ !! i = Some s →
  ▷ bunches_wf k E E' σ Ps Pr Qc -∗
     ▷ ∃ (b: bool) γprop_stored γprop_remainder,
         (saved_prop_own γprop_stored (Ps i) ∗
        saved_prop_own γprop_remainder (Pr i) ∗
        □ (C -∗ Ps i -∗ if b then |={E, E'}_k=> ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i)
                            else ([∗ set] j∈s, ▷ Qc j) ∗ (▷ Pr i)))%I.
Proof.
  iIntros (?) "Hbunch". iNext.
  rewrite /bunches_wf.
  iDestruct (big_sepM_lookup with "Hbunch") as "Hb"; first eauto.
  rewrite /bunch_wf. iDestruct "Hb" as (γ' ???) "(?&Hown'&?&?&?)".
  iExists _, _, _. iFrame.
Qed.

Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance staged_persistent N k E E': Persistent (staged_inv N k E E').
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done γ: staged_pending γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending γ.
Proof.
  iApply (own_alloc (Cinl (Excl ()))).
  { econstructor. }
Qed.

(*
Lemma staged_inv_alloc N k E E':
  (|={E}=> staged_inv N k E' E')%I.
Proof.
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc Qr) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "H".
  iIntros "(HQ&#HQP)".
  iMod (inv_alloc N E _ with "[HQ H1]") as "HI"; last first.
  { iModIntro. iExists γ, γ'. iFrame "H". iSplitL "HI".
    - iApply "HI".
    - iExists γprop, γprop'. iFrame. iFrame "#".
  }
  iNext. iExists γprop, γprop', Q, Qr. iFrame. iFrame "#".
  iModIntro. iIntros. iApply step_fupdN_inner_later; auto; iNext.
  iApply "HQP"; by iFrame.
Qed.
*)

Lemma staged_inv_alloc N k E E' P Q Qr:
  ↑N ⊆ E →
  staged_inv N k E' E' ∗
  ▷ Q ∗ □ (C -∗ ▷ Q -∗ ▷ P ∗ ▷ Qr) ={E}=∗
  ∃ i, staged_bundle Q Qr false {[i]} ∗ staged_crash P {[i]} ∗ staged_crash_pending P i.
Proof.
  iIntros (?) "(Hinv&HQ&#HQP)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iMod (partition_alloc with "Hpart") as (bid i Hnotin1 Hnotin2) "(Hpart&Hbundle&Hbundle_meta)".
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc Qr) as (γprop') "#Hsaved_rem".
  iMod (own_alloc (● (Excl' (false, (γprop, γprop'))) ⋅ ◯ (Excl' (false, (γprop, γprop'))))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (meta_set ⊤ bid γ bN with "Hbundle_meta") as "#HbidN"; first by set_solver.
  rewrite -Hdom in Hnotin2.
  assert (σdom !! i = None) as Hin3.
  { by eapply not_elem_of_dom in Hnotin2. }
  iMod (gen_heap_alloc σdom i () with "Hheap") as "(Hheap&Hi_pts&Hi_meta)"; first auto.
  iMod (pending_alloc) as (γp) "Hpend".
  iDestruct (meta_token_difference i (↑pN) ⊤ with "Hi_meta") as "(HipN&Hi_meta)".
  { set_solver. }
  iMod (meta_set _ i γp pN with "HipN") as "#HipN"; first by set_solver.
  iMod (saved_prop_alloc P) as (γcrash) "#Hsaved_crash".
  iMod (meta_set _ i γcrash cN with "Hi_meta") as "#HicN"; first by solve_ndisj.
  iMod ("Hclo" with "[-Hbundle H2 Hpend Hi_pts]").
  { iNext.
    iExists _, _, (λ k, if decide (k = bid) then Q else (Qs k)),
                  (λ k, if decide (k = bid) then Qr else (Qsr k)),
                  (λ k, if decide (k = i) then P else (Pc k)).
    iFrame.
    iSplitL "".
    { iPureIntro. rewrite dom_insert_L /union_partition.
      rewrite Hdom map_fold_insert; [ auto | set_solver |].
      eauto.
    }
    iSplitL "Hcrash_wf".
    {
      rewrite /crash_prop_wf.
      iApply (big_sepM_insert); first auto.
      iSplitL "".
      { iExists _. destruct (decide (i = i)) => //=. iFrame "#". }
      iApply (big_sepM_mono with "Hcrash_wf").
      { iIntros (k' [] ?) "H". destruct (decide (k' = i)); first by congruence.
        eauto. }
    }
    iSplitL "Hbunch_wf H1".
    { iApply (big_sepM_insert); first auto.
      iSplitL "H1".
      { iExists _, _, _, _. iFrame.
        rewrite ?decide_True //.
        iFrame "#".
        iModIntro. iIntros.
        rewrite big_opS_singleton.
        rewrite decide_True //.
        by iApply "HQP".
      }
      iApply (big_sepM_mono with "Hbunch_wf").
      { iIntros (k' [] ?) "H".
        iDestruct "H" as (? b ??) "(?&?&?&?&#Hwand)".
        iExists _, _, _, _. iFrame.
        destruct (decide (k' = bid)); first by congruence.
        iFrame; iModIntro. iIntros "? ?". iSpecialize ("Hwand" with "[$] [$]").
        destruct b.
        * iApply (step_fupdN_inner_wand with "Hwand"); auto.
         iApply sep_mono_l.
         iApply big_sepS_mono.
         iIntros (i' Hin') "HPc".
         destruct (decide (i' = i)); try iFrame.
         subst.
         exfalso. eapply not_elem_of_union_partition in Hin'; auto.
         { erewrite <-Hdom. eauto. }
         { eauto. }
        * iDestruct "Hwand" as "(Hwand&$)".
         iApply (big_sepS_mono with "Hwand").
         iIntros (i' Hin') "HPc".
         destruct (decide (i' = i)); try iFrame.
         subst.
         exfalso. eapply not_elem_of_union_partition in Hin'; auto.
         { erewrite <-Hdom. eauto. }
         { eauto. }
      }
    }
    iApply big_sepM_insert; first auto.
    iSplitL "HQ".
    { iLeft. rewrite /bunch_live decide_True //. }
    rewrite /inv_status.
    iApply (big_sepM_mono with "Hstatus").
    iIntros (k' x' Hin') "HQ".
    rewrite /bunch_live/bunch_crashed.
    rewrite ?decide_False; try congruence.
    iApply (or_mono_r with "HQ").
    iIntros "($&($&H))".
    iApply (big_sepS_mono with "H").
    iIntros (i' Hin'') "HPc".
    destruct (decide (i' = i)); try iFrame.
    subst.
    exfalso. eapply not_elem_of_union_partition in Hin'; eauto.
    { erewrite <-Hdom. eauto. }
  }
  iModIntro. iExists _.
  iSplitL "Hbundle H2".
  { iExists _, _, _, _, Q, Qr. iFrame. iFrame "#".
    iSplitL.
    - iIntros "!> !> $".
    - iIntros "!> !> $".
  }
  iSplitL "".
  { iExists _. rewrite ?big_sepS_singleton. iFrame "#".
    iSplitL "".
    - iExists _. iFrame "#".
    - iModIntro; eauto.
  }
  iFrame "Hi_pts".
  iSplitL.
  { iExists _. iFrame. iFrame "#". }
  { iExists _. iFrame. iFrame "#". }
Qed.

Theorem staged_bundle_weaken Q1 Q1' Q2 Q2' b bundle :
  □(Q1 -∗ Q2) -∗
  □(Q1' -∗ Q2') -∗
  staged_bundle Q1 Q1' b bundle -∗
  staged_bundle Q2 Q2' b bundle.
Proof.
  iIntros "#HQ12 #HQ12' H".
  iDestruct "H" as (i γ γprop γprop' Qalt Qalt') "(Hbundle&Hmeta&Hown&#Hequiv1&#Hequiv2&Hsaved1&Hsaved2)".
  iExists i, γ, γprop, γprop', Qalt, Qalt'; iFrame.
  iSplitL "Hequiv1".
  - iIntros "!> !> H".
    iDestruct ("Hequiv1" with "H") as "H".
    iApply "HQ12"; auto.
  - iIntros "!> !> H".
    iDestruct ("Hequiv2" with "H") as "H".
    iApply "HQ12'"; auto.
Qed.

Theorem staged_bundle_weaken_1 Q1 Q1' Q2 b bundle :
  □(Q1 -∗ Q2) -∗
  staged_bundle Q1 Q1' b bundle -∗
  staged_bundle Q2 Q1' b bundle.
Proof.
  iIntros "#HQ12 H".
  iApply staged_bundle_weaken; iFrame "# ∗".
  auto.
Qed.

Theorem staged_bundle_weaken_2 Q1 Q1' Q2' b bundle :
  □(Q1' -∗ Q2') -∗
  staged_bundle Q1 Q1' b bundle -∗
  staged_bundle Q1 Q2' b bundle.
Proof.
  iIntros "#HQ12' H".
  iApply staged_bundle_weaken; iFrame "# ∗".
  auto.
Qed.

Lemma later_equiv_big_sepS {L} `{Countable L} (s: gset L) (P Q: L → iProp Σ):
  ([∗ set] i ∈ s, ▷ (P i ≡ Q i)) -∗
  (▷ (([∗ set] i ∈ s, P i) ≡ ([∗ set] i ∈ s, Q i))) : iProp Σ.
Proof.
  induction s using set_ind_L.
  - rewrite ?big_sepS_empty. eauto.
  - iIntros "H". rewrite ?big_sepS_insert //.
    iDestruct "H" as "(H1&H2)".
    iPoseProof (IHs with "H2") as "H2".
    iNext. iRewrite "H1". iRewrite "H2". eauto.
Qed.

Lemma staged_crash_agree σ s Pc_set Pc:
  s ⊆ dom (gset nat) σ →
  crash_prop_wf σ Pc -∗
  ([∗ set] i ∈ s, ∃ γ : gname, meta i cN γ ∗ saved_prop_own γ (Pc_set i)) -∗
  ▷ (([∗ set] i ∈ s, Pc_set i) ≡ ([∗ set] i ∈ s, Pc i)).
Proof.
  iIntros (Hsub) "Hc Hown".
  iApply later_equiv_big_sepS.
  rewrite /crash_prop_wf.
  iDestruct (big_sepM_forall with "Hc") as "#Hc1".
  iDestruct (big_sepS_forall with "Hown") as "#Hc2".
  iApply big_sepS_forall.
  iIntros (k Hin).
  assert (k ∈ dom (gset nat) σ) as Hin' by set_solver.
  apply elem_of_dom in Hin' as ([]&Hin').
  iDestruct ("Hc1" with "[//]") as (γ1) "(Hmeta1&Hsaved1)".
  iDestruct ("Hc2" with "[//]") as (γ2) "(Hmeta2&Hsaved2)".
  iDestruct (meta_agree with "Hmeta1 Hmeta2") as %Heq1. subst.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved2") as "Hequiv".
  iNext. iRewrite "Hequiv"; eauto.
Qed.

Lemma staged_crash_agree_later σ s Pc_set Pc:
  s ⊆ dom (gset nat) σ →
  ▷ crash_prop_wf σ Pc -∗
  ([∗ set] i ∈ s, ∃ γ : gname, meta i cN γ ∗ saved_prop_own γ (Pc_set i)) -∗
  ▷▷ (([∗ set] i ∈ s, Pc_set i) ≡ ([∗ set] i ∈ s, Pc i)).
Proof. iIntros. iNext. by iApply staged_crash_agree. Qed.

Lemma staged_crash_agree_later_1 σ P Pc i:
  i ∈ dom (gset nat) σ →
  ▷ crash_prop_wf σ Pc -∗
  (∃ γ : gname, meta i cN γ ∗ saved_prop_own γ P) -∗
  ▷▷ (P ≡ Pc i).
Proof.
  iIntros (Hin) "Hc Hown !>".
  iDestruct (big_sepM_forall with "Hc") as "#Hc1".
  apply elem_of_dom in Hin as ([]&Hin).
  iDestruct ("Hc1" with "[//]") as (γ1) "(Hmeta1&Hsaved1)".
  iDestruct "Hown" as (γ) "(Hmeta2&Hsaved2)".
  iDestruct (meta_agree with "Hmeta1 Hmeta2") as %Heq1. subst.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved2") as "Hequiv".
  iNext. iRewrite "Hequiv"; eauto.
Qed.

Lemma staged_inv_weak_open E N k E1 P i:
  ↑N ⊆ E →
  E1 ⊆ E ∖ ↑N →
  staged_inv N k E1 E1 ∗
  staged_crash_pending P i ∗
  C -∗ |={E,E}_(S (S k))=> ▷ P.
Proof.
  iIntros (??) "(#Hinv&(Hpts&Hpending&Hsaved)&#HC)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (gen_heap_valid with "Hheap Hpts") as %Hin.

  iDestruct (staged_crash_agree_later_1 with "[$] [$]") as "#Hequiv_crash".
  { apply elem_of_dom; eauto. }
  edestruct (union_partition_elem_of_1 σ i) as (bid&s&Heq&Hin').
  { rewrite -Hdom. apply elem_of_dom; eauto. }

  iDestruct (bunches_wf_later_pers_lookup_weak with "Hbunch_wf") as (b ??) "(#H1&#H2&#Hwand)"; first eauto.
  iMod (bunches_wf_to_later with "Hbunch_wf") as "Hbunch_wf".
  rewrite /inv_status.
  iDestruct (big_sepM_later with "Hstatus") as "Hstatus".
  iDestruct (big_sepM_lookup_acc with "Hstatus") as "(Hstatus&Hstatus_rest)"; first eauto.
  iDestruct (later_or with "Hstatus") as "Hstatus".
  iMod (fupd_intro_mask' _ E1) as "Hclo_E"; first auto.
  iMod (fupd_intro_mask' _ (∅)) as "Hclo_E1"; first by set_solver.
  iModIntro. rewrite Nat_iter_S. iModIntro. iNext.
  iEval (rewrite (lock bunch_crashed)) in "Hstatus". (* protect against ▷-stripping *)
  rewrite Nat_iter_S. do 2 iModIntro. iNext. rewrite -lock.
  iDestruct "Hstatus" as "[Hlive|(_&Hcrashed)]".
  - rewrite /bunch_live.
    iSpecialize ("Hwand" with "[$] [$]").
    destruct b.
    * iMod "Hclo_E1" as "_".
      iApply (step_fupdN_wand with "Hwand"). iIntros "H".
      iMod "H" as "(HPcs&HQsr)".
      iDestruct (big_sepS_delete with "HPcs") as "(HP&HPcs)"; first eapply Hin'.
      iMod "Hclo_E" as "_".
      iDestruct "Hpending" as (γ) "(#?&Hpend)".
      iMod (pending_upd_done with "[$]") as "Hdone".
      iSpecialize ("Hstatus_rest" with "[HQsr HPcs Hdone]").
      {
        iRight. iNext. rewrite /bunch_crashed. iFrame. iFrame "#".
        iApply big_sepS_delete; first eassumption.
        iSplitL "Hdone".
        {
          iRight. iExists _. iFrame. eauto.
        }
        iApply (big_sepS_mono with "HPcs").
        { iIntros. by iLeft. }
      }
      iMod ("Hclo" with "[-HP]").
      { iNext. iExists _, _, _, _, _. iFrame. eauto. }
      iModIntro. iRewrite "Hequiv_crash". eauto.
    * iMod "Hclo_E1" as "_".
      iMod "Hclo_E".
      iApply (step_fupdN_inner_later'); auto.
      iNext.
      iDestruct "Hwand" as "(HPcs&HQsr)".
      iDestruct (big_sepS_delete with "HPcs") as "(HP&HPcs)"; first eapply Hin'.
      iDestruct "Hpending" as (γ) "(#?&Hpend)".
      iMod (pending_upd_done with "[$]") as "Hdone".
      iSpecialize ("Hstatus_rest" with "[HQsr HPcs Hdone]").
      {
        iRight. iNext. rewrite /bunch_crashed. iFrame. iFrame "#".
        iApply big_sepS_delete; first eassumption.
        iSplitL "Hdone".
        {
          iRight. iExists _. iFrame. eauto.
        }
        iApply (big_sepS_mono with "HPcs").
        { iIntros. by iLeft. }
      }
      iMod ("Hclo" with "[-HP]").
      { iNext. iExists _, _, _, _, _. iFrame. eauto. }
      iModIntro. iRewrite "Hequiv_crash". eauto.
  -  iMod "Hclo_E1" as "_".
     iMod "Hclo_E".
     iApply (step_fupdN_inner_later'); auto.
     iNext.
     iDestruct "Hcrashed" as "(HQsr&HPcs)".
     iDestruct (big_sepS_delete with "HPcs") as "(HP&HPcs)"; first eapply Hin'.
     iDestruct "Hpending" as (γ) "(#?&Hpend)".
     iDestruct "HP" as "[HP|Hfalse]"; last first.
     { iDestruct "Hfalse" as (?) "(Hmeta&Hdone)".
       iDestruct (meta_agree with "Hmeta [$]") as %Heq'. subst.
       iDestruct (pending_done with "[$] [$]") as %[].
     }
      iMod (pending_upd_done with "[$]") as "Hdone".
     iSpecialize ("Hstatus_rest" with "[HQsr HPcs Hdone]").
     {
       iRight. rewrite /bunch_crashed. iFrame. iFrame "#".
       iApply big_sepS_delete; first eassumption.
       iSplitL "Hdone".
       {
         iRight. iExists _. iFrame. eauto.
       }
       iApply (big_sepS_mono with "HPcs"); eauto.
     }
     iMod ("Hclo" with "[-HP]").
     { iNext. iExists _, _, _, _, _. iFrame. eauto. }
     iModIntro. iRewrite "Hequiv_crash". eauto.
Qed.


Lemma staged_bundle_join N k E E' Q1 Qr1 Q2 Qr2 s1 s2:
  ↑N ⊆ E →
  staged_inv N k E' E' ∗
  staged_bundle Q1 Qr1 false s1 ∗
  staged_bundle Q2 Qr2 false s2
  ={E}=∗
  staged_bundle (Q1 ∗ Q2) (Qr1 ∗ Qr2) false (s1 ∪ s2).
Proof.
  iIntros (?) "(Hinv&Hb1&Hb2)".
  rewrite /staged_bundle.
  iDestruct "Hb1" as (bid1 γ1 γprop1 γprop1' Q1alt Qr1alt)
                       "(Hbid1&#Hb_meta1&Hown1&#Hequiv1&#Hequiv1_alt&#Hsaved1&#Hsavedr1)".
  iDestruct "Hb2" as (bid2 γ2 γprop2 γprop2' Q2alt Qr2alt)
                       "(Hbid2&#Hb_meta2&Hown2&#Hequiv2&#Hequiv2_alt&#Hsaved2&#Hsavedr2)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (gen_heap_valid with "[Hpart] Hbid1") as %Hin1.
  { iDestruct "Hpart" as "(?&$)". }
  iDestruct (gen_heap_valid with "[Hpart] Hbid2") as %Hin2.
  { iDestruct "Hpart" as "(?&$)". }
  iDestruct (partition_valid_disj with "Hpart Hbid1 Hbid2") as %[Hdisj Hneq].
  iMod (partition_join with "Hpart Hbid2 Hbid1") as "(Hpart&Hbid2&Hbid1)".

  iMod (saved_prop_alloc (Qs bid1 ∗ Qs bid2)) as (γprop1_new) "#Hsaved1_new".
  iMod (saved_prop_alloc (Qsr bid1 ∗ Qsr bid2)) as (γprop1'_new) "#Hsavedr1_new".
  iMod (saved_prop_alloc True) as (γprop2_new) "#Hsaved2_new".
  iMod (saved_prop_alloc True) as (γprop2'_new) "#Hsavedr2_new".

  iMod (bunches_wf_to_later with "Hbunch_wf") as "Hbunch_wf".

  set (Qs' := (λ k, if decide (k = bid1) then (Qs bid1 ∗ Qs bid2) else
                    if decide (k = bid2) then True else
                    Qs k)%I).
  set (Qsr' := (λ k, if decide (k = bid1) then (Qsr bid1 ∗ Qsr bid2) else
                    if decide (k = bid2) then True else
                    Qsr k)%I).
  iAssert (|==> bunches_wf_later k E' E' (<[bid2:=∅]> (<[bid1:=s1 ∪ s2]> σ)) Qs' Qsr' Pc ∗
                ▷ saved_prop_own γprop1 (Qs bid1) ∗
                ▷ saved_prop_own γprop1' (Qsr bid1) ∗
                ▷ saved_prop_own γprop2 (Qs bid2) ∗
                ▷ saved_prop_own γprop2' (Qsr bid2) ∗
                own γ1 (◯ Excl' (false, (γprop1_new, γprop1'_new))) ∗
                own γ2 (◯ Excl' (false, (γprop2_new, γprop2'_new))) ∗
                ▷ □ (C -∗ Qs bid1 -∗ ([∗ set] j ∈ s1, ▷ Pc j) ∗ ▷ Qsr bid1) ∗
                ▷ □ (C -∗ Qs bid2 -∗ ([∗ set] j ∈ s2, ▷ Pc j) ∗ ▷ Qsr bid2))%I with "[Hbunch_wf Hown1 Hown2]"
         as ">(Hbunches&#Hsaved1'&#Hsavedr1'&#Hsaved2'&#Hsavedr2'&Hown1&Hown2&#Hwand1&#Hwand2)".
  { rewrite /bunches_wf_later big_sepM_insert_delete.
    iDestruct (big_sepM_delete with "Hbunch_wf") as "(Hbid2_bunch&Hbunch_wf)"; first eapply Hin2.
    iAssert (|==> bunch_wf_later k E' E' Qs' Qsr' Pc bid2 ∅ ∗
                  ▷ saved_prop_own γprop2 (Qs bid2) ∗
                  ▷ saved_prop_own γprop2' (Qsr bid2) ∗
                  own γ2 (◯ Excl' (false, (γprop2_new, γprop2'_new))) ∗
                  ▷ □ (C -∗ Qs bid2 -∗ ([∗ set] j ∈ s2, ▷ Pc j) ∗ ▷ Qsr bid2))%I
      with "[Hbid2_bunch Hown2]" as ">($&$&$&$&#Hwand2)".
    {
      iDestruct "Hbid2_bunch" as (????) "(Hm2&Hown_auth2&Hs2&Hsr2&#Hwand2)".
      iDestruct (meta_agree with "Hb_meta2 Hm2") as %<-.
      unify_ghost.
      iMod (ghost_var_update γ2 (false, (γprop2_new, γprop2'_new)) with "[$] [$]") as "(Hown_auth2&$)".
      iModIntro. rewrite /bunch_wf_later. iFrame "#". iFrame. iExists _, _, _, _. iFrame.
      rewrite /Qs'/Qsr'.
      destruct (decide (bid2 = bid1)) => //=.
      rewrite ?decide_True //. iFrame "#".
      iNext. iModIntro. iIntros "#HC _".
      rewrite big_sepS_empty //=.
    }
    iFrame "Hwand2".

    iDestruct (big_sepM_delete _ _ bid1 with "Hbunch_wf") as "(Hbid1_bunch&Hbunch_wf)".
    { rewrite lookup_delete_ne //. }
    iAssert (|==> bunch_wf_later k E' E' Qs' Qsr' Pc bid1 (s1 ∪ s2) ∗
                  ▷ saved_prop_own γprop1 (Qs bid1) ∗
                  ▷ saved_prop_own γprop1' (Qsr bid1) ∗
                  own γ1 (◯ Excl' (false ,(γprop1_new, γprop1'_new))) ∗
                  ▷ □ (C -∗ Qs bid1 -∗ ([∗ set] j ∈ s1, ▷ Pc j) ∗ ▷ Qsr bid1))%I
      with "[Hbid1_bunch Hown1]" as ">(?&$&$&$&Hwand1)".
    {
      iDestruct "Hbid1_bunch" as (????) "(Hm1&Hown_auth1&Hs1&Hsr1&#Hwand1)".
      iDestruct (meta_agree with "Hb_meta1 Hm1") as %<-.
      unify_ghost.
      iMod (ghost_var_update γ1 (false, (γprop1_new, γprop1'_new)) with "[$] [$]") as "(Hown_auth1&$)".
      iModIntro. rewrite /bunch_wf_later. iFrame "#". iFrame. iExists _, _, _, _. iFrame.
      rewrite /Qs'/Qsr'.
      rewrite ?decide_True //. iFrame "#".
      destruct (decide (bid2 = bid1)) => //=.
      iNext. iModIntro. iIntros "#HC (HQ1&HQ2)". rewrite big_sepS_union //.
      iDestruct ("Hwand1" with "HC [$]") as "($&$)".
      iDestruct ("Hwand2" with "HC [$]") as "($&$)".
    }
    iFrame "Hwand1".
    rewrite delete_insert_ne //.
    rewrite big_sepM_insert_delete.
    iFrame.
    iModIntro. iApply (big_sepM_mono with "Hbunch_wf").
    intros k' s' Hlookup.
    rewrite /bunch_wf_later. rewrite /Qs'/Qsr'.
    apply lookup_delete_Some in Hlookup as (Hneq1&Hlookup).
    apply lookup_delete_Some in Hlookup as (Hneq2&Hlookup).
    rewrite ?decide_False //=.
  }
  iMod ("Hclo" with "[-Hbid1 Hown1]").
  { iNext. iExists _, _, _, _, _. iFrame "Hcrash_wf Hbunches Hpart Hheap".
    iSplitL "".
    { iPureIntro. rewrite Hdom. rewrite -union_partition_move //.
      { rewrite Hin2. f_equal; set_solver+. }
    }
    rewrite /inv_status.
    iApply big_sepM_insert_delete.
    rewrite delete_insert_ne //.
    rewrite big_sepM_insert_delete.
    iDestruct (big_sepM_delete _ _ bid2 with "Hstatus") as "(Hb2&Hstatus)"; first done.
    iDestruct (big_sepM_delete _ _ bid1 with "Hstatus") as "(Hb1&Hstatus)".
    { rewrite lookup_delete_ne //. }
    rewrite assoc.
    iSplitL "Hb1 Hb2".
    {
      rewrite /bunch_live. rewrite /bunch_crashed.
      iDestruct "Hb1" as "[Hb1l|(#HC&HQr1&Hb1cr)]".
      {
        iDestruct "Hb2" as "[Hb2l|(#HC&HQr2&Hb2cr)]".
        { rewrite /Qs'.
          destruct (decide (bid1 = bid2)) => //=;
          destruct (decide (bid2 = bid1)) => //=; [].
          rewrite ?decide_True //=; [].
          iSplitL ""; first by iLeft.
          iLeft. iFrame.
        }
        { rewrite /Qsr'.
          destruct (decide (bid1 = bid2)) => //=;
          destruct (decide (bid2 = bid1)) => //=; [].
          rewrite ?decide_True //=; [].
          iDestruct ("Hwand1" with "[$] [$]") as "(Hb1cr&HQr1)".
          iSplitL "".
          { iRight. rewrite big_sepS_empty. iFrame "#". eauto. }
          iRight. iFrame. iFrame "#". iApply big_sepS_union; first by auto.
          iFrame. iApply (big_sepS_mono with "Hb1cr"). eauto.
        }
      }
      iDestruct "Hb2" as "[Hb2l|(_&HQr2&Hb2cr)]".
      {
        { rewrite /Qsr'.
          destruct (decide (bid1 = bid2)) => //=;
          destruct (decide (bid2 = bid1)) => //=; [].
          rewrite ?decide_True //=; [].
          iDestruct ("Hwand2" with "[$] [$]") as "(Hb2cr&HQr2)".
          iSplitL "".
          { iRight. rewrite big_sepS_empty. iFrame "#". eauto. }
          iRight. iFrame. iFrame "#". iApply big_sepS_union; first by auto.
          iFrame. iApply (big_sepS_mono with "Hb2cr"); eauto.
        }
      }
      rewrite /Qsr'.
      destruct (decide (bid1 = bid2)) => //=;
      destruct (decide (bid2 = bid1)) => //=;
      rewrite ?decide_True //=; [].
      iSplitL "".
      { iRight. rewrite big_sepS_empty. iFrame "#". eauto. }
      iRight. iFrame. iFrame "#". iApply big_sepS_union; first by auto.
      iFrame.
    }
    iApply (big_sepM_mono with "Hstatus").
    {
      iIntros (?? Hlookup) "H".
      apply lookup_delete_Some in Hlookup as (Hneq1&Hlookup).
      apply lookup_delete_Some in Hlookup as (Hneq2&Hlookup).
      rewrite /Qs'/Qsr'/bunch_live/bunch_crashed. simpl.
      rewrite ?decide_False //=.
    }
  }
  iModIntro. iExists _, _, _, _, _, _. iFrame. iFrame "#".
  rewrite -?later_sep. iNext.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1'".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2'".
  iDestruct (saved_prop_agree with "Hsavedr1 Hsavedr1'") as "Hequivr1'".
  iDestruct (saved_prop_agree with "Hsavedr2 Hsavedr2'") as "Hequivr2'".
  iSplitL; iModIntro.
  - iIntros "[H1 H2]".
    iDestruct ("Hequiv1" with "[H1]") as "$".
    { iNext. iRewrite "Hequiv1'". done. }
    iDestruct ("Hequiv2" with "[H2]") as "$".
    { iNext. iRewrite "Hequiv2'". done. }
  - iIntros "[H1 H2]".
    iDestruct ("Hequiv1_alt" with "[H1]") as "$".
    { iNext. iRewrite "Hequivr1'". done. }
    iDestruct ("Hequiv2_alt" with "[H2]") as "$".
    { iNext. iRewrite "Hequivr2'". done. }
Qed.

Lemma staged_inv_open E N k E1 E2 P Q Qr b s:
  ↑N ⊆ E →
  E2 ⊆ E1 →
  staged_inv N k E1 E2 ∗
  staged_bundle Q Qr b s ∗
  staged_crash P s ={E,E∖↑N}=∗
  (▷ ▷ Q ∗ ▷ (∀ Q' Qr' b', ▷ Q' ∗ □ (C -∗ Q' -∗ if (b': bool) then |={E1, E2}_k=> ▷ P ∗ ▷ Qr' else
                                                ▷ P ∗ ▷ Qr')
                         ={E∖↑N,E}=∗ staged_bundle Q' Qr' b' s)) ∨
  (▷ ▷ Qr ∗ C ∗ |={E∖↑N, E}=> staged_bundle Q True b s).
Proof.
  iIntros (??) "(#Hinv&Hb&Hcrash)".
  iDestruct "Hcrash" as (Pc_set) "(#Hcrash_agree&#Hcrash_wand)".
  iDestruct "Hb" as (bid γ γprop γprop' Qalt Qralt)
                       "(Hbid&#Hb_meta&Hown&#Hequiv&#Hequiv_alt&#Hsaved&#Hsavedr)".
  iInv "Hinv" as "H" "Hclo".
  iDestruct "H" as (σ σdom Qs Qsr Pc) "(>Hdom&>Hpart&>Hheap&Hcrash_wf&Hbunch_wf&Hstatus)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (gen_heap_valid with "[Hpart] Hbid") as %Hin.
  { iDestruct "Hpart" as "(?&$)". }
  iDestruct (bunches_wf_later_pers_lookup with "[$] [$] [$]") as "(#HQs&#HQr&#Hwand)"; first eauto.
  iDestruct (staged_crash_agree_later with "[$] [$]") as "#Hequiv_crash".
  { rewrite Hdom. by eapply union_partition_subset. }
  rewrite /inv_status.
  iDestruct (big_sepM_later with "Hstatus") as "Hstatus".
  iDestruct (big_sepM_delete with "Hstatus") as "(Hstatus&Hstatus_rest)"; first eauto.
  iDestruct "Hstatus" as "[Hlive|(>#HC&Hcrashed)]".
  - iLeft.
    iModIntro. iSplitL "Hlive".
    { iNext. iDestruct (saved_prop_agree with "Hsaved HQs") as "Hequiv'".
      iApply "Hequiv". iNext. iRewrite "Hequiv'". auto. }
    iNext.
    iIntros (Q' Qr' b') "(HQs'&#Hwand')".
    iMod (saved_prop_alloc Q') as (γprop_new) "#Hsaved_new".
    iMod (saved_prop_alloc Qr') as (γprop'_new) "#Hsaved'_new".
    iMod (bunches_wf_to_later with "Hbunch_wf") as "Hbunch_wf".
    set (Qs' := (λ k, if decide (k = bid) then Q' else Qs k)).
    set (Qsr' := (λ k, if decide (k = bid) then Qr' else Qsr k)).
    iAssert (|==> bunches_wf_later k E1 E2 σ Qs' Qsr' Pc ∗
                  ▷ saved_prop_own γprop (Qs bid) ∗
                  ▷ saved_prop_own γprop' (Qsr bid) ∗
                  own γ (◯ Excl' (b', (γprop_new, γprop'_new))))%I with "[Hbunch_wf Hown]"
           as ">(Hbunches&#Hsaved1'&#Hsavedr1'&Hown)".
    { rewrite /bunches_wf_later.
      iDestruct (big_sepM_delete with "Hbunch_wf") as "(Hb&Hbunch_wf)"; first eauto.
      rewrite (big_sepM_delete _ σ); last eauto.
        iDestruct "Hb" as (????) "(Hm&Hown_auth&Hs&Hsr&#Hwand_old)".
        iDestruct (meta_agree with "Hb_meta Hm") as %<-.
        unify_ghost.
        iMod (ghost_var_update γ (b', (γprop_new, γprop'_new)) with "[$] [$]") as "(Hown_auth&$)".
        rewrite -assoc.
        iSplitL "Hm Hs Hsr Hown_auth".
        {
          rewrite /bunch_wf_later. iModIntro. iExists _, _, _, _. iFrame.
          rewrite /Qs'/Qsr'.
          rewrite ?decide_True //. iFrame "#".
          iNext. iModIntro. iIntros "#HC HQ'".
          iSpecialize ("Hwand'" with "[$] [$]").
          destruct b'.
          * iApply (step_fupdN_inner_wand' with "Hwand'"); auto.
            iIntros "(?&$)".
            iApply big_sepS_later. iRewrite -"Hequiv_crash". iApply big_sepS_later.
            by iApply "Hcrash_wand".
          * iDestruct ("Hwand'") as "(?&$)".
            iApply big_sepS_later. iRewrite -"Hequiv_crash". iApply big_sepS_later.
            by iApply "Hcrash_wand".
        }
        iFrame "#".
        iModIntro. iApply (big_sepM_mono with "Hbunch_wf").
        iIntros (k0 ? Hlookup_delete).
        apply lookup_delete_Some in Hlookup_delete as (?&?).
        rewrite /bunch_wf_later/Qs'/Qsr'. rewrite ?decide_False //=.
      }
    iMod ("Hclo" with "[-Hown Hbid]").
    {
      iNext. iExists _, _, _, _, _. iFrame.
      iSplitL ""; first eauto.
      iApply big_sepM_delete; first eauto.
      rewrite {1}/Qs'/bunch_live decide_True //; iFrame.
      iApply (big_sepM_mono with "Hstatus_rest").
      { iIntros (k0 ? Hlookup_delete).
        apply lookup_delete_Some in Hlookup_delete as (?&?).
        rewrite /Qs'/Qsr'/bunch_crashed. rewrite ?decide_False //.
        apply or_mono_r. apply sep_mono_r. apply sep_mono; first by auto.
        apply big_sepS_mono=>??. apply or_mono_l. auto. }
    }
    iModIntro. iExists _, _, _, _, _, _. iFrame. iFrame "#".
    iSplitL; iIntros "!> !> $".
  - iRight.
    iModIntro. iDestruct "Hcrashed" as "(HQsr&Hcrashed)". iSplitL "HQsr".
    { iNext. iDestruct (saved_prop_agree with "Hsavedr HQr") as "Hequiv'".
      iApply "Hequiv_alt". iNext. iRewrite "Hequiv'". auto. }
    iFrame "HC".
    iMod (saved_prop_alloc True%I) as (γprop'_new) "#Hsaved'_new".
    iMod (bunches_wf_to_later with "Hbunch_wf") as "Hbunch_wf".
    set (Qs' := Qs).
    set (Qsr' := (λ k, if decide (k = bid) then True%I else Qsr k)).
    iAssert (|==> bunches_wf_later k E1 E2 σ Qs' Qsr' Pc ∗
                  ▷ saved_prop_own γprop (Qs bid) ∗
                  ▷ saved_prop_own γprop' (Qsr bid) ∗
                  own γ (◯ Excl' (b, (γprop, γprop'_new))))%I with "[Hbunch_wf Hown]"
           as ">(Hbunches&#Hsaved1'&#Hsavedr1'&Hown)".
    { rewrite /bunches_wf_later.
      iDestruct (big_sepM_delete with "Hbunch_wf") as "(Hb&Hbunch_wf)"; first eauto.
      rewrite (big_sepM_delete _ σ); last eauto.
        iDestruct "Hb" as (????) "(Hm&Hown_auth&Hs&Hsr&#Hwand_old)".
        iDestruct (meta_agree with "Hb_meta Hm") as %<-.
        unify_ghost.
        iMod (ghost_var_update γ (b, (γprop, γprop'_new)) with "[$] [$]") as "(Hown_auth&$)".
        rewrite -assoc.
        iSplitL "Hm Hs Hsr Hown_auth".
        {
          rewrite /bunch_wf_later. iModIntro. iExists _, _, _, _. iFrame.
          rewrite /Qs'/Qsr'.
          rewrite ?decide_True //. iFrame "#".
          iNext. iModIntro. iIntros "#HC' HQ'".
          iSpecialize ("Hwand_old" with "[$] [$]").
          destruct b.
          * iApply (step_fupdN_inner_wand' with "Hwand_old"); auto.
            iIntros "(?&?)". iSplitL; eauto.
          * iDestruct ("Hwand_old") as "(?&?)". iSplitL; eauto.
        }
        iFrame "#".
        iModIntro. iApply (big_sepM_mono with "Hbunch_wf").
        iIntros (k0 ? Hlookup_delete).
        apply lookup_delete_Some in Hlookup_delete as (?&?).
        rewrite /bunch_wf_later/Qs'/Qsr'. rewrite ?decide_False //=.
      }
    iMod ("Hclo" with "[-Hown Hbid]").
    {
      iNext. iExists _, _, _, _, _. iFrame.
      iSplitL ""; first eauto.
      iApply big_sepM_delete; first eauto.
      iSplitL "Hcrashed".
      { iRight. rewrite /bunch_crashed {1}/Qsr' decide_True //; iFrame. eauto. }
      iApply (big_sepM_mono with "Hstatus_rest").
      { iIntros (k0 ? Hlookup_delete).
        apply lookup_delete_Some in Hlookup_delete as (?&?).
        rewrite /Qsr'/bunch_live/bunch_crashed. rewrite decide_False //. }
    }
    iModIntro. iExists _, _, _, _, _, _. iFrame. iFrame "#". eauto.
Qed.

Lemma staged_inv_NC_open E N k E1 E2 P Q Qr b s:
  ↑N ⊆ E →
  E2 ⊆ E1 →
  NC ∗
  staged_inv N k E1 E2 ∗
  staged_bundle Q Qr b s ∗
  staged_crash P s ={E,E∖↑N}=∗
  (▷ ▷ Q ∗ ▷ (∀ Q' Qr' b', ▷ Q' ∗ □ (C -∗ Q' -∗ if (b': bool) then |={E1, E2}_k=> ▷ P ∗ ▷ Qr' else
                                                ▷ P ∗ ▷ Qr')
                         ={E∖↑N,E}=∗ staged_bundle Q' Qr' b' s)).
Proof.
  iIntros (??) "(HNC&Hinv&Hval)".
  iMod (staged_inv_open with "[$]") as "[H|(_&HC&_)]"; auto.
  iDestruct (NC_C with "[$] [$]") as %[].
Qed.

End definitions.

Lemma staged_inv_init `{!invG Σ, !stagedG Σ, !crashG Σ} N k E1 E2 E:
  ⊢ |={E}=> ∃ Γ, staged_inv Γ N k E1 E2.
Proof.
  iMod (partition_init (L := nat) (V := nat)) as (n1) "H1".
  iMod (gen_heap_name_init (∅: gmap nat unit)) as (n2) "H2".
  iExists {| staging_gnames_names := n2; staging_bunches_names := n1 |}.
  rewrite /staged_inv.
  iMod (inv_alloc N E _ with "[-]") as "$"; last done.
  iNext. iExists ∅, ∅, (λ _, True%I), (λ _, True%I), (λ _, True%I). iFrame.
  iSplitL "".
  { rewrite /union_partition map_fold_empty dom_empty_L //=. }
  rewrite /crash_prop_wf/bunches_wf/inv_status ?big_sepM_empty //.
Qed.
