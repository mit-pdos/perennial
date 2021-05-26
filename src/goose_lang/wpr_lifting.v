From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Import crash_modality typing adequacy lang.
Set Default Proof Using "Type".

Section wpr_definitions.

Context `{ffi_sem: ffi_semantics}.
Context {ext_tys: ext_types ext}.
Context `{!ffi_interp ffi}.

Canonical Structure heap_local_namesO := leibnizO heap_local_names.

Program Global Instance heapG_perennialG `{!heapGS Σ} :
  perennialG goose_lang goose_crash_lang heap_local_namesO Σ :=
{
  perennial_irisG := λ Hcrash hnames,
                     @heapG_irisG _ _ _ _ _ (heap_update_local _ _ _ Hcrash (@pbundleT _ _ hnames));
  perennial_crashG := λ _ _, eq_refl;
  perennial_num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  perennial_step_count_next := (λ n, 10 * (n + 1))%nat;
}.
Next Obligation. eauto. Qed.
Next Obligation. eauto. Qed.
Next Obligation. eauto. Qed.

Definition wpr `{hG: !heapGS Σ} (s: stuckness) (k: nat) (E: coPset)
  (e: expr) (recv: expr) (Φ: val → iProp Σ) (Φinv: heapGS Σ → iProp Σ) (Φr: heapGS Σ → val → iProp Σ) :=
  wpr s k _ ({| pbundleT := heap_get_local_names Σ _ |}) E e recv
              Φ
              (λ Hc names, Φinv (heap_update_local _ _ _ Hc (@pbundleT _ _ names)))
              (λ Hc names v, Φr (heap_update_local _ _ _ Hc (@pbundleT _ _ names)) v).


Section wpr.
Context `{hG: !heapGS Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

Lemma wpr_strong_mono s k E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr s k E e rec Φ Φinv Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
  wpr s k E e rec Ψ Ψinv Ψr.
Proof.
  rewrite /wpr. iIntros "Hwpr Himpl".
  iApply (wpr_strong_mono with "Hwpr [Himpl]").
  repeat iSplit.
  - by iDestruct "Himpl" as "($&_)".
  - iIntros.
    iDestruct "Himpl" as "(_&H)".
    iIntros. by iApply "H".
  - iIntros.
    iDestruct "Himpl" as "(_&H)".
    iIntros. by iApply "H".
Qed.

Lemma fupd_wpr s k E e rec Φ Φinv Φr :
  (|={E}=> wpr s k E e rec Φ Φinv Φr) -∗
  wpr s k E e rec Φ Φinv Φr.
Proof.
  iIntros "H".
  rewrite /wpr.
  rewrite wpr_unfold /wpr_pre.
  iApply @fupd_wpc. eauto.
Qed.

Lemma idempotence_wpr `{!ffi_interp_adequacy} s k E1 e rec Φx Φinv Φrx Φcx:
  ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx hG }} -∗
   (□ ∀ (hG': heapGS Σ) (Hpf: @heapG_invG _ _ _ _ hG = @heapG_invG _ _ _ _ hG') σ σ'
        (HC: crash_prim_step (goose_crash_lang) σ σ'),
        Φcx hG' -∗ ▷ post_crash(λ hG', ffi_restart (heapG_ffiG) σ'.(world) -∗
        (Φinv hG' ∧ WPC rec @ s ; k; E1 {{ Φrx hG' }} {{ Φcx hG' }}))) -∗
    wpr s k E1 e rec Φx Φinv Φrx.
Proof.
  iIntros "Hwpc #Hidemp".
  iApply (idempotence_wpr s k E1 e rec _ _ _
                          (λ Hc names, Φcx (heap_update_local _ _ _ Hc (@pbundleT _ _ names)))
                                                    with "[Hwpc] [Hidemp]"); first auto.
  { rewrite //= heap_get_update' //=. }
  { iModIntro. iIntros (?? σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "H".
    iSpecialize ("Hidemp" $! (heap_update_local _ _ _ _ _) with "[//] [//] H").
    {
      rewrite /state_interp.
      iIntros "(_&Hffi_old&Htrace_auth&Horacle_auth) Hg".
      iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
      iDestruct "Hg" as "(Hgffi&Hg)".
      iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) with "Hffi_old Hgffi") as (ffi_names) "(Hw&Hgffi&Hcrel&Hc)".
      { inversion Hcrash; subst; eauto. }
      iMod (trace_reinit _ σ_post_crash.(trace) σ_post_crash.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
      set (hnames := {| heap_local_heap_names := name_na_heap;
                        heap_local_ffi_local_names := ffi_names;
                        heap_local_trace_names := name_trace |}).
      iModIntro.
      iNext. iIntros (Hc' ?) "HNC".
      set (hG' := (heap_update_local _ _ _ Hc' hnames)).
      iSpecialize ("Hidemp" $! σ_pre_crash.(world) σ_post_crash.(world) hG' with "[Hcrel] [Hc]").
      { rewrite //= ffi_update_update //=. }
      { rewrite //= ffi_update_update //=. }
      iExists ({| pbundleT := hnames |}).
      rewrite /state_interp//=.
      rewrite ffi_update_update. iFrame.
      unshelve (iExists _); auto.
      { rewrite ?ffi_global_ctx_nolocal //. }
      unshelve (iExists _); auto.
      iDestruct "Hg" as "($&Hc&$)".
      iMod (cred_interp_incr_k _ (9 * ns + 10) with "Hc") as "(Hc&_)".
      assert (ns + (9 * ns + 10) = 10 * (ns + 1))%nat as -> by lia.
      by iFrame.
    }
  }
Qed.

End wpr.
End wpr_definitions.
