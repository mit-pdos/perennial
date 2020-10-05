From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Import crash_modality typing adequacy lang.
Set Default Proof Using "Type".

Section wpr_definitions.

Context `{ffi_semantics: ext_semantics}.
Context {ext_tys: ext_types ext}.
Context `{!ffi_interp ffi}.

Canonical Structure heap_namesO := leibnizO heap_names.

Global Instance heapG_perennialG `{!heapG Σ} : perennialG goose_lang goose_crash_lang heap_namesO Σ :=
{
  perennial_irisG := λ Hinv Hcrash hnames,
                     @heapG_irisG _ _ _ _ _ (heap_update _ _ Hinv Hcrash (@pbundleT _ _ hnames));
  perennial_invG := λ _ _ _, eq_refl;
  perennial_crashG := λ _ _ _, eq_refl
}.

Definition wpr `{hG: !heapG Σ} `{hC: !crashG Σ} (s: stuckness) (k: nat) (E: coPset)
  (e: expr) (recv: expr) (Φ: val → iProp Σ) (Φinv: heapG Σ → iProp Σ) (Φr: heapG Σ → val → iProp Σ) :=
  wpr s k (heapG_invG) hC ({| pbundleT := heap_get_names Σ _ |}) E e recv
              Φ
              (λ Hi Hc names, Φinv (heap_update _ _ Hi Hc (@pbundleT _ _ names)))
              (λ Hi Hc names v, Φr (heap_update _ _ Hi Hc (@pbundleT _ _ names)) v).


Section wpr.
Context `{hG: !heapG Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

Lemma wpr_strong_mono s k E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr s k E e rec Φ Φinv Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ <bdisc> ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
  wpr s k E e rec Ψ Ψinv Ψr.
Proof.
  rewrite /wpr. iIntros "Hwpr Himpl".
  iApply (wpr_strong_mono with "Hwpr [Himpl]").
  repeat iSplit.
  - by iDestruct "Himpl" as "($&_)".
  - iIntros.
    iDestruct "Himpl" as "(_&H)".
    iModIntro.
    iSplit.
    * iIntros. by iApply "H".
    * iIntros. by iApply "H".
Qed.

Lemma idempotence_wpr `{!ffi_interp_adequacy} s k E1 e rec Φx Φinv Φrx Φcx:
  ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx hG }} -∗
   (□ ∀ (hG: heapG Σ) σ σ' (HC: crash_prim_step (goose_crash_lang) σ σ'),
        Φcx hG -∗ ▷ post_crash(λ hG', ffi_restart (heapG_ffiG) σ'.(world) -∗
        (Φinv hG' ∧ WPC rec @ s ; k; E1 {{ Φrx hG' }} {{ Φcx hG' }}))) -∗
    wpr s k E1 e rec Φx Φinv Φrx.
Proof.
  iIntros "Hwpc #Hidemp".
  iApply (idempotence_wpr s k E1 e rec _ _ _
                          (λ Hi Hc names, Φcx (heap_update _ _ Hi Hc (@pbundleT _ _ names)))
                                                    with "[Hwpc] [Hidemp]"); first auto.
  { rewrite //= heap_get_update' //=. }
  { iModIntro. iIntros (??? σ_pre_crash σ_post_crash Hcrash κs ?) "H".
    iSpecialize ("Hidemp" $! (heap_update _ _ _ _ _) with "[//] H").
    {
      rewrite /state_interp.
      iIntros "(_&_&Hffi_old&Htrace_auth&Horacle_auth)".
      iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
      iMod (proph_map.proph_map_reinit _ κs σ_post_crash.(used_proph_id)) as (name_proph_map) "Hp".
      iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) with "Hffi_old") as (ffi_names) "(Hw&Hcrel&Hc)".
      { inversion Hcrash; subst; eauto. }
      iMod (trace_reinit _ σ_post_crash.(trace) σ_post_crash.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
      set (hnames := {| heap_heap_names := name_na_heap;
                        heap_proph_name := name_proph_map;
                        heap_ffi_names := ffi_names;
                        heap_trace_names := name_trace |}).
      iModIntro.
      iNext. iIntros (Hi' Hc' ?) "HNC".
      set (hG' := (heap_update _ _ Hi' Hc' hnames)).
      iSpecialize ("Hidemp" $! σ_pre_crash.(world) σ_post_crash.(world) hG' with "[Hcrel] [Hc]").
      { rewrite //= ffi_update_update //=. }
      { rewrite //= ffi_update_update //=. }
      iExists ({| pbundleT := hnames |}).
      iModIntro.
      rewrite /state_interp//=.
      rewrite ffi_update_update. iFrame.
    }
  }
Qed.

End wpr.
End wpr_definitions.
