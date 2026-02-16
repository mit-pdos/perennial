From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From Perennial.goose_lang Require Import lang.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export lifting recovery_lifting.
From Perennial.goose_lang Require Import adequacy lang crash_borrow.
Set Default Proof Using "Type".

Theorem goose_recv_adequacy `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
  {go_gctx : GoGlobalContext}
  {Hffi_adequacy:ffi_interp_adequacy} Σ `{hPre: !gooseGpreS Σ} s e r σ g φ φr φinv n :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ), ∃ Φinv,
     ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
       ffi_local_start goose_ffiLocalGS σ.(world) -∗
       own_go_state σ.(go_state).(package_state) -∗
       pre_borrowN n ={⊤}=∗
       □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ hL : gooseLocalGS Σ,
           let hG := HeapGS _ _ hL _ in
           Φinv hG -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       wpr s ⊤ e r (λ v, ⌜φ v⌝) (Φinv) (λ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := goose_crash_lang) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hinit Hinitg Hwp.
  eapply (wp_recv_adequacy_inv Σ _ _ (n * 4 + crash_borrow_ginv_number)).
  iIntros (???).
  iMod (na_heap_name_init tls σ.(heap)) as (name_na_heap) "Hh".
  iMod (ffi_global_init _ _ g.(global_world)) as (ffi_namesg) "(Hgw&Hgstart)"; first by eauto.
  iMod (ffi_local_init _ _ σ.(world)) as (ffi_names) "(Hw&Hstart)"; first by eauto.
  iMod (go_state_init _ σ.(go_state).(package_state)) as (globals_name) "(Hg & Hgfrag)".
  iMod (credit_name_init (n*4 + crash_borrow_ginv_number)) as (name_credit) "(Hcred_auth&Hcred&Htok)".
  iDestruct (cred_frag_split with "Hcred") as "(Hpre&Hcred)".
  iMod (proph_map_init κs g.(used_proph_id)) as (proph_names) "Hproph".

  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  (* TODO(RJ): reformulate init lemmas to better match what we need here. *)
  set (hG := GooseGlobalGS _ _ proph_names (creditGS_update_pre _ _ name_credit) ffi_namesg).
  set (hL := GooseLocalGS Σ Hc ffi_names
                          (σ.(go_state).(go_lctx))
                          (na_heapGS_update_pre _ name_na_heap)
                          (go_stateGS_update_pre Σ _ globals_name)).
  destruct (Hwp _ _) as [Φinv Hwp']. clear Hwp.
  iExists state_interp, global_state_interp, fork_post.
  iExists _, _.
  iExists ((λ Hinv hGen, ∃ hL:gooseLocalGS Σ, ⌜hGen = goose_generationGS (L:=hL)⌝ ∗ Φinv (HeapGS _ _ hL _)))%I.
  iDestruct (@cred_frag_to_pre_borrowN _ _ _ _ _ hG _ n with "Hpre") as "Hpre".
  iMod (Hwp' with "[$] [$] [$] [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (??) "Hσ".
    iApply ("H1" with "Hσ").
  }
  iSplitR.
  {
    iModIntro. iIntros (HG') "(%hL' & -> & H)".
    iApply "H2". done.
  }
  iFrame. iFrame "Hinv". iSplitR; first done. iSplitR; first done.
  rewrite /wpr.
  iApply (recovery_weakestpre.wpr_strong_mono with "Hwp").
  iSplit; first by eauto.
  iSplit; first by eauto.
  iIntros (? v) "(% & % & $)". done.
Qed.

Section failstop.

Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}.
Context {go_gctx : GoGlobalContext}.

(* We can model failstop execution by just having the restart thread be a trivial program that just halts.
   Thus, the machine "restarts" after a crash but it does not do anything. *)
Definition adequate_failstop (e: expr) (σ: state) (g: global_state)
    (φpost : val → state → global_state → Prop) :=
  recv_adequate (CS := goose_crash_lang) NotStuck e (of_val #()) σ g φpost (λ _ _ _, True) (λ _ _, True).

(* Like above, but, for failstop execution one only needs to prove a wp, not a
wpr. Due to that, no φinv is supported (since after the crash σ changed so
[φinv σ] no longer has any reason to hold). *)
Theorem goose_recv_adequacy_failstop
        Σ `{hPre: !gooseGpreS Σ} (e: expr) (σ: state) (g: global_state) φpost :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
    ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
      ffi_local_start goose_ffiLocalGS σ.(world) ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φpost v⌝ }}) →
  adequate_failstop e σ g (λ v _ _, φpost v).
Proof.
  intros Hinitg Hinit Hwp. eapply goose_recv_adequacy with (n:=0%nat); [done..|].
  exists (λ _, True)%I.
  iIntros "Hstartg Hstart _ _".
  iMod (Hwp with "Hstartg Hstart") as "Hwp". iModIntro.
  iSplitR.
  { iIntros "!> * _". iApply ncfupd_mask_intro; auto. }
  iSplitR.
  { do 2 iIntros "!> * _". iApply ncfupd_mask_intro; auto. }
  iApply (idempotence_wpr (hG:=HeapGS _ _ _ _) _ _ _ _ _ _ _ (λ _, True%I) with "[Hwp] []").
  { iApply wp_wpc. eauto. }
  { iModIntro. iIntros (????) "_".
    iModIntro.
    rewrite /crash_modality.post_crash.
    iIntros (???) "H". iModIntro; iFrame. iIntros "H". iSplit; first auto.
    iApply wpc_value; eauto.
  }
Qed.

End failstop.
