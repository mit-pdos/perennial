From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export wpr_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
Set Default Proof Using "Type".

Theorem heap_recv_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy} Σ `{hPre: !heapPreG Σ} s k e r σ g φ φr φinv Φinv (HINIT: ffi_initP σ.(world) g) :
  (∀ `{Hheap : !heapG Σ},
     ⊢ (ffi_start (heapG_ffiG) σ.(world) g -∗ trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) ={⊤}=∗
       □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ hG (Hpf: @heapG_invG _ _ _ _ Hheap = @heapG_invG _ _ _ _ hG),
                     Φinv hG -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
        wpr s k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝))) →
  recv_adequate (CS := goose_crash_lang) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  eapply (wp_recv_adequacy_inv _ _ _ heap_namesO _ _ _ _ _ _ _ _ _ (λ names0 Hinv Hc names, Φinv (heap_update _ (heap_update_pre _ _ Hinv Hc (@pbundleT _ _ names0)) Hinv Hc (@pbundleT _ _ names))) (λ n, n)).
  iIntros (???) "".
  iMod (na_heap_name_init tls σ.(heap)) as (name_na_heap) "Hh".
  iMod (ffi_name_init _ _ σ.(world) g) as (ffi_names ffi_namesg) "(Hw&Hgw&Hstart)"; first auto.
  iMod (trace_name_init σ.(trace) σ.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
  set (hnames := {| heap_heap_names := name_na_heap;
                      heap_ffi_local_names := ffi_names;
                      heap_ffi_global_names := ffi_namesg;
                      heap_trace_names := name_trace |}).
  set (hG := heap_update_pre _ hPre Hinv Hc hnames).
  iExists ({| pbundleT := hnames |}).
  iExists
    (λ t σ nt, let _ := heap_update Σ hG Hinv Hc (@pbundleT _ _ t) in
               state_interp σ nt)%I,
    (λ t g ns κs, let _ := heap_update Σ hG Hinv Hc (@pbundleT _ _ t) in
                  global_state_interp g ns κs).
  iExists _. (* (λ Hc t, λ (σ0 : state) (_ : nat) (κs0 : list observation) (_ : nat),
                                              lifting.heapG_irisG_obligation_1 Σ
                                                (heap_update Σ (heap_update_pre Σ hPre Hinv Hc hnames) Hinv Hc
                                                   pbundleT) σ0 κs0). *)
  iExists _.
  iExists _.
  iExists _.
  iMod (Hwp hG with "[$] [$] [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (??) "Hσ".
    iApply ("H1" with "[Hσ]").
    iExactEq "Hσ". do 2 f_equal.
    rewrite /heap_update/hG/heap_update_pre//=. f_equal.
    rewrite ffi_update_pre_update. eauto.
  }
  iSplitR.
  {
    iModIntro. iIntros (Hc' names') "H".
    iDestruct ("H2" $! _ _ with "[H]") as "#H3".
    { iExactEq "H".
      f_equal.
    }
    iModIntro. iIntros (??) "H". iSpecialize ("H3" with "H"); eauto.
  }
  iFrame. rewrite /hG//=.
  rewrite ffi_update_pre_update //=. iFrame.
  rewrite /wpr. rewrite /hG//=.
  rewrite heap_update_pre_get.
  rewrite //=.
  Unshelve.
  - eauto.
  - exact O.
Qed.
