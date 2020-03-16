From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Import typing adequacy.
Set Default Proof Using "Type".

Section wpr_definitions.

Context `{ffi_semantics: ext_semantics}.
Context {ext_tys: ext_types ext}.
Context `{!ffi_interp ffi}.

Canonical Structure heap_namesO := leibnizO heap_names.

Global Instance heapG_perennialG `{!heapG Σ} : perennialG heap_lang heap_crash_lang heap_namesO Σ :=
{
  perennial_irisG := λ Hinv hnames, @heapG_irisG _ _ _ _ _ (heap_update _ _ Hinv (@pbundleT _ _ hnames));
  perennial_invG := λ _ _, eq_refl
}.

End wpr_definitions.

Theorem heap_recv_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy} Σ `{!heapPreG Σ} `{crashPreG Σ} s k e r σ φ φr φinv Φinv :
  (∀ `{Hheap : !heapG Σ} `{Hc: !crashG Σ} Hinv t,
     ⊢ |={⊤}=>
       (ffi_start (heapG_ffiG) σ.(world) -∗ trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) -∗
       □ (∀ n σ κ, state_interp σ κ n ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
       □ (∀ Hi t, Φinv Hi t -∗
                       let _ := heap_update _ Hheap Hi (@pbundleT _ _ t) in
                       □ ∀ σ κ n, state_interp σ κ n ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
        wpr s k Hinv Hc t ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ _ v, ⌜φr v⌝))) →
  recv_adequate (CS := heap_crash_lang) s e r σ (λ v _, φ v) (λ v _, φr v) φinv.
Proof.
  intros Hwp. eapply (wp_recv_adequacy_inv _ _ _ heap_namesO _ _).
  iIntros (???) "".
  iMod (na_heap_init tls σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (ffi_name_init _ _ σ.(world)) as (HffiG) "(Hw&Hstart)".
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(Htr&Htrfrag&Hor&Hofrag)".
  set (hG := (HeapG _ _ (ffi_update_pre _ _ HffiG) _ _ HtraceG)).
  set (hnames := heap_get_names _ hG).
  iExists ({| pbundleT := hnames |}).
  iExists
    (λ t σ κs, let _ := heap_update_names Σ hG (@pbundleT _ _ t) in
               state_interp σ κs O)%I,
    (λ t _, True%I).
  iExists (λ _ _, eq_refl).
  iMod (Hwp hG Hc Hinv {| pbundleT := hnames |} with "[$] [$] [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iAlways. iIntros (??) "H". rewrite heap_get_update.
    by iApply "H1".
  }
  iSplitR.
  { iAlways. iIntros (??) "H". iDestruct ("H2" with "H") as "#H3".
    iAlways. iIntros (??) "H". iMod ("H3" with "[$]"); eauto.
  }
  iFrame. rewrite //= ffi_get_update //=.
Qed.
