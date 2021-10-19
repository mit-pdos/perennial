From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre dist_adequacy.
From Perennial.goose_lang Require Export recovery_lifting dist_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
From Perennial.goose_lang Require Import crash_modality.
Set Default Proof Using "Type".

Theorem goose_dist_adequacy `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}
        Σ `{hPre: !gooseGpreS Σ} (ebσs : list node_init_cfg)
        g φinv (HINITG: ffi_initgP g) (HINIT: ∀ σ, σ ∈ init_local_state <$> ebσs → ffi_initP σ.(world) g) :
  (∀ `(HG : !gooseGlobalGS Σ),
      ⊢
        ffi_global_start goose_ffiGlobalGS g ={⊤}=∗
        wpd ⊤ ebσs ∗
        (∀ g, ffi_global_ctx goose_ffiGlobalGS g -∗ |={⊤, ∅}=> ⌜ φinv g ⌝)) →
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  eapply (wpd_dist_adequacy_inv Σ _ _ _ _ _ _ _ (λ n, 10 * (n + 1))%nat).
  iIntros (Hinv ?) "".
  iMod (ffi_global_init _ _ g) as (ffi_namesg) "(Hgw&Hgstart)"; first by auto.
  iMod (credit_name_init (crash_borrow_ginv_number)) as (name_credit) "(Hcred_auth&Hcred&Htok)".

  set (hG := GooseGlobalGS _ _ (creditGS_update_pre _ _ name_credit) ffi_namesg).

  iExists global_state_interp, fork_post.
  iExists _, _.

  iMod (Hwp hG with "[$]") as "(Hwp&Hφ)".

  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  iModIntro.
  iFrame "Hgw Hinv Hcred_auth Htok".
  iSplitR; first by eauto.
  iSplitL "Hwp"; last first.
  { iIntros (???) "Hσ".
    iApply ("Hφ" with "[Hσ]").
    iDestruct "Hσ" as "($&_)".
  }
  rewrite /wpd/dist_weakestpre.wpd.
  iApply (big_sepL_mono with "Hwp").
  iIntros (k' σ Hin) "H %Hc".


  iMod (na_heap_name_init tls σ.(init_local_state).(heap)) as (name_na_heap) "Hh".
  iMod (ffi_local_init _ _ σ.(init_local_state).(world)) as (ffi_names) "(Hw&Hstart)".
  { eapply HINIT. apply elem_of_list_fmap. eexists. split; first done.
    eapply elem_of_list_lookup_2. done. }
  iMod (trace_name_init σ.(init_local_state).(trace) σ.(init_local_state).(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
  set (hL := GooseLocalGS Σ Hc ffi_names (na_heapGS_update_pre _ name_na_heap) (traceGS_update_pre Σ _ name_trace)).

  iMod ("H" $! hL with "[$] [$] [$]") as (Φ Φrx Φinv) "Hwpr".
  iModIntro. iExists state_interp, _, _, _.
  iSplitR "Hwpr"; first by iFrame.
  rewrite /wpr//=.
Qed.

Section failstop.

Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}.

(* We can model failstop execution by just having the restart thread be a trivial program that just halts.
   Thus, a node "restarts" after a crash but it does not do anything. *)
Definition dist_adequate_failstop (ebσs: list (expr * state)) (g: global_state) :=
  let ρs := fmap (λ ebσ, {| init_thread := fst ebσ;
                           init_restart := of_val #();
                           init_local_state := snd ebσ |})
               ebσs in
  dist_adequate (CS := goose_crash_lang) ρs g.

(* Like above, but, for failstop execution one only needs to prove a wp about initial threads, not a wpr *)
Theorem goose_dist_adequacy_failstop
        Σ `{hPre: !gooseGpreS Σ} (ebσs : list (expr * state))
        g φinv (HINITG: ffi_initgP g) (HINIT: ∀ σ, σ ∈ snd  <$> ebσs → ffi_initP σ.(world) g) :
  (∀ `(HG : !gooseGlobalGS Σ),
      ⊢
        ffi_global_start goose_ffiGlobalGS g ={⊤}=∗
        ([∗ list] ebσ ∈ ebσs,
           let e := fst ebσ in
           let σ := snd ebσ in
           ∀ `(hL: !gooseLocalGS Σ),
             ffi_local_start (goose_ffiLocalGS) σ.(world) -∗
             trace_frag σ.(trace) -∗
             oracle_frag σ.(oracle) ={⊤}=∗
             ∃ Φ, wp NotStuck ⊤ e Φ) ∗
        (∀ g, ffi_global_ctx goose_ffiGlobalGS g -∗ |={⊤, ∅}=> ⌜ φinv g ⌝)) →
  dist_adequate_failstop ebσs g (λ g, φinv g).
Proof.
  intros Hwp. rewrite /dist_adequate_failstop.
  eapply (goose_dist_adequacy Σ); first done.
  { intros σ (?&->&Hin)%elem_of_list_fmap. eapply HINIT; eauto.
    apply elem_of_list_fmap in Hin as (?&->&?) => //=.
    eapply elem_of_list_fmap. eauto. }
  iIntros (HG) "Hg".
  iMod (Hwp HG with "[$]") as "(Hwp&$)". iModIntro.
  iApply big_sepL_fmap. simpl.
  iApply (big_sepL_mono with "Hwp").
  iIntros (i (e&σ) Hlookup) "H".
  iIntros (HL) "Hffi Htrace Horacle". iMod ("H" $! HL with "[$] [$] [$]") as "Hwp".
  iDestruct "Hwp" as (Φ) "H". simpl.
  iModIntro. iExists Φ, (λ _ _, True%I), (λ _, True%I).
  set (Hheao := HeapGS _ HG HL).
  iApply (idempotence_wpr _ _ _ _ _ _ _ (λ _, True%I) with "[H] []").
  { iApply wp_wpc. eauto. }
  { iModIntro. iIntros (????) "_".
    iModIntro.
    rewrite /post_crash.
    iIntros (???) "H". iModIntro; iFrame. iIntros "H". iSplit; first auto.
    iApply wpc_value; eauto.
  }
Qed.

End failstop.
