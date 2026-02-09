From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From Perennial.goose_lang Require Import lang.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Import crash_modality adequacy lang lifting.
Set Default Proof Using "Type".

Section wpr_definitions.

Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

(* FIXME: to be useful with new goose, this will require the package.Assumptions
   to be threaded through. E.g. [idempotence_wpr] will need to have
   package.Assumptions as precondition in the restart case. *)
Definition wpr {go_goctx : GoGlobalContext} `{hG: !gooseGlobalGS Σ, hL: !gooseLocalGS Σ} (s: stuckness) (E: coPset)
  (e: expr) (recv: expr) (Φ: val → iProp Σ) (Φinv: heapGS Σ → iProp Σ) (Φr: heapGS Σ → val → iProp Σ) :=
  wpr goose_crash_lang s _ E e recv
              Φ
              (λ hGen, ∃ hL:gooseLocalGS Σ, ⌜hGen = goose_generationGS (L:=hL)⌝ ∗ Φinv (HeapGS _ _ hL))%I
              (λ hGen v, ∃ hL:gooseLocalGS Σ, ⌜hGen = goose_generationGS (L:=hL)⌝ ∗ Φr (HeapGS _ _ hL) v)%I.

Section wpr.
Context `{hG: !heapGS Σ} {go_gctx : GoGlobalContext}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

Lemma wpr_strong_mono s E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr s E e rec Φ Φinv Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
  wpr s E e rec Ψ Ψinv Ψr.
Proof.
  rewrite /wpr. iIntros "Hwpr Himpl".
  iApply (wpr_strong_mono with "Hwpr [Himpl]").
  repeat iSplit.
  - by iDestruct "Himpl" as "($&_)".
  - iIntros "% (% & % & ?)".
    iDestruct "Himpl" as "(_&H)".
    iExists _. iSplit; first done. by iApply "H".
  - iIntros "%% (% & % & ?)".
    iDestruct "Himpl" as "(_&H)".
    iExists _. iSplitR; first done. by iApply "H".
Qed.

Lemma fupd_wpr s E e rec Φ Φinv Φr :
  (|={E}=> wpr s E e rec Φ Φinv Φr) -∗
  wpr s E e rec Φ Φinv Φr.
Proof.
  iIntros "H".
  rewrite /wpr.
  rewrite wpr_unfold /wpr_pre.
  iApply @fupd_wpc. eauto.
Qed.

Lemma idempotence_wpr `{!ffi_interp_adequacy} s E1 e rec Φx
  (Φinv : heapGS Σ → iProp Σ)
  (Φrx : heapGS Σ → val → iProp Σ)
  (Φcx : heapGS Σ → iProp Σ) :
  ⊢ WPC e @ s ; E1 {{ Φx }} {{ Φcx _ }} -∗
   (□ ∀ (hL': gooseLocalGS Σ) σ σ'
        (HC: goose_crash σ σ'),
        let hG' := HeapGS _ _ hL' in (* sadly this let-binding is lost for users of this lemma, but they should really have it in scope to use the right instances of everything. *)
        Φcx hG' -∗ ▷ post_crash (hG := hG') (λ hG'', let hL'' := goose_localGS (heapGS:=hG'') in
        ffi_restart (goose_ffiLocalGS (hL:=hL'')) σ'.(world) -∗
        (Φinv hG'' ∧ WPC rec @ s ; E1 {{ Φrx hG'' }} {{ Φcx hG'' }}))) -∗
    wpr s E1 e rec Φx Φinv Φrx.
Proof.
  iIntros "Hwpc #Hidemp".
  iApply (idempotence_wpr goose_crash_lang s E1 e rec _ _ _
                          (λ hGen, ∃ hL:gooseLocalGS Σ, ⌜hGen = goose_generationGS (L:=hL)⌝ ∗
                                   Φcx (HeapGS _ _ hL))%I
                                                    with "[Hwpc] [Hidemp]"); first auto.
  { iApply (wpc_crash_mono with "[] Hwpc").
    iIntros "HΦcx". iExists _. destruct hG. by iFrame. }
  iModIntro. iIntros (HG' σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "(%HL' & -> & H)".
  iSpecialize ("Hidemp" $! HL' _ _ Hcrash with "H").
  rewrite /state_interp.
  simpl. iIntros "@ Hg".
  iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
  iDestruct "Hg" as "(Hgffi&Hg)".
  iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) with "Hffi") as (ffi_names) "(Hw&Hcrel&Hc)".
  { inversion Hcrash; subst; eauto. }
  iClear "Hg_auth".
  iMod (go_state_reinit _) as (globals_name) "[Hg_auth Hglobals]".
  iModIntro.
  iNext.
  iMod (NC_alloc) as (Hc') "HNC".
  (* TODO(RJ): reformulate na_heap_reinit and trace_reinit to better match what we need here. *)
  set (hL' := GooseLocalGS Σ Hc' ffi_names
                σ_post_crash.(go_state).(go_lctx)
                (na_heapGS_update _ name_na_heap)
                (go_stateGS_update Σ _ globals_name)
      ).
  iExists (goose_generationGS (L:=hL')).
  iSpecialize ("Hidemp" $! σ_pre_crash.(world) σ_post_crash.(world) hL' with "Hcrel").
  iMod ("Hidemp") as "(Hrestart&Hidemp)".
  iSpecialize ("Hidemp" with "Hc").
  rewrite /state_interp//=.
  iFrame.
  iDestruct "Hg" as "($&$&Hc&$)".
  iMod (cred_interp_incr_k _ (9 * ns + 10) with "Hc") as "(Hc&_)".
  assert (ns + (9 * ns + 10) = 10 * (ns + 1))%nat as -> by lia.
  iModIntro. iFrame "∗#%".
  repeat iSplit.
  - done.
  - iDestruct "Hidemp" as "[H _]". iExists _. iFrame. done.
  - iDestruct "Hidemp" as "[_ H]".
    iApply (wpc_mono with "H"); eauto.
Qed.

End wpr.
End wpr_definitions.
