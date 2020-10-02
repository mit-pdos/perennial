From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export wpr_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
Set Default Proof Using "Type".

Theorem heap_recv_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy} Σ `{!heapPreG Σ} s k e r σ φ φr φinv Φinv (HINIT: ffi_initP σ.(world)) :
  (∀ `{Hheap : !heapG Σ},
     ⊢ (ffi_start (heapG_ffiG) σ.(world) -∗ trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) ={⊤}=∗
       □ (∀ n σ κ, state_interp σ κ n ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
       □ (∀ hG, Φinv hG -∗ □ ∀ σ κ n, state_interp σ κ n ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
        wpr s k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝))) →
  recv_adequate (CS := goose_crash_lang) s e r σ (λ v _, φ v) (λ v _, φr v) φinv.
Proof.
  intros Hwp.
  eapply (wp_recv_adequacy_inv _ _ _ heap_namesO _ _ _ _ _ _ _ _ (λ Hi Hc names, Φinv (heap_update_pre _ _ Hi Hc (@pbundleT _ _ names)))).
  iIntros (???) "".
  iMod (na_heap_name_init tls σ.(heap)) as (name_na_heap) "Hh".
  iMod (proph_map_name_init _ κs σ.(used_proph_id)) as (name_proph_map) "Hp".
  iMod (ffi_name_init _ _ σ.(world)) as (ffi_names) "(Hw&Hstart)"; first auto.
  iMod (trace_name_init σ.(trace) σ.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
  set (hnames := {| heap_heap_names := name_na_heap;
                      heap_proph_name := name_proph_map;
                      heap_ffi_names := ffi_names;
                      heap_trace_names := name_trace |}).
  set (hG := heap_update_pre _ _ Hinv Hc hnames).
  iExists ({| pbundleT := hnames |}).
  iExists
    (λ Hi t σ κs, let _ := heap_update Σ hG Hi Hc (@pbundleT _ _ t) in
               state_interp σ κs O)%I,
    (λ t _, True%I).
  iExists (λ _ _ _, eq_refl).
  iExists (λ _ _ _, eq_refl).
  iMod (Hwp hG with "[$] [$] [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (??) "H". rewrite heap_update_pre_update.
    by iApply "H1".
  }
  iSplitR.
  {
    iModIntro. iIntros (Hinv' Hc' names') "H". rewrite ?heap_update_pre_update.
    iDestruct ("H2" with "H") as "#H3".
    iModIntro. iIntros (??) "H". iMod ("H3" with "H").
    eauto.
  }
  iFrame. rewrite /hG//=.
  rewrite ffi_update_pre_update //=. iFrame.
  rewrite /wpr. rewrite /hG//=.
  rewrite heap_update_pre_get.
  iApply (recovery_weakestpre.wpr_strong_mono with "Hwp").
  repeat iSplit; [| iModIntro; iSplit]; eauto.
  - iIntros. rewrite heap_update_pre_update. eauto.
    Unshelve.
    (* TODO: where is this ocming from? *)
    exact O.
Qed.
