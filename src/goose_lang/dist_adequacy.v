From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre dist_adequacy.
From Perennial.goose_lang Require Export wpr_lifting dist_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
Set Default Proof Using "Type".

Theorem heap_dist_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}
        Σ `{hPre: !heapPreG Σ} k (ebσs : list (expr * state))
        g φinv (HINIT: ∀ σ, σ ∈ snd <$> ebσs → ffi_initP σ.(world) g) :
  (∀ `{Hheap : !heap_globalG Σ} (cts : list (crashG Σ * heap_local_names)),
      ⊢
        ffi_pre_global_start Σ (heap_preG_ffi) (heap_globalG_names) g ={⊤}=∗
        ([∗ list] i ↦ ct; σ ∈ cts; snd <$> ebσs,
              let hG := heap_globalG_heapG Hheap (fst ct) (snd ct) in
              ffi_local_start (heapG_ffiG) σ.(world) g ∗ trace_frag σ.(trace) ∗ oracle_frag σ.(oracle)) ={⊤}=∗
        (∀ g, ffi_pre_global_ctx Σ (heap_preG_ffi) (heap_globalG_names) g -∗ |={⊤, ∅}=> ⌜ φinv g ⌝) ∗
        wpd k ⊤ cts (fst <$> ebσs)) →
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  eapply (wpd_dist_adequacy_inv _ _ _ heap_local_namesO).
  iIntros (Hinv ?) "".
  iMod (ffi_name_global_init _ _ g) as (ffi_namesg) "(Hgw&Hgstart)"; first auto.
  set (hgG := {| heap_globalG_preG := _; heap_globalG_names := ffi_namesg;
                     heap_globalG_invG := Hinv |}).
  iAssert (|==> ∃ cts, ffi_pre_global_ctx Σ heap_preG_ffi ffi_namesg g ∗
              ([∗ list] i ↦ ct; σ ∈ cts; snd <$> ebσs,
              let hG := heap_globalG_heapG hgG (fst ct) (snd ct) in
              NC 1 ∗ state_interp σ 0) ∗
              ([∗ list] i ↦ ct; σ ∈ cts; snd <$> ebσs,
              let hG := heap_globalG_heapG hgG (fst ct) (snd ct) in
              ffi_local_start (heapG_ffiG) σ.(world) g ∗ trace_frag σ.(trace) ∗ oracle_frag σ.(oracle)))%I

    with "[Hgw]" as "H".
  { clear -HINIT. remember (snd <$> ebσs) as σs eqn:Heq. rewrite -Heq. clear Heq.
    iInduction σs as [| σ σs] "IH".
    { iExists []; eauto. }
    { iMod ("IH" with "[] [$]") as (cts) "(Hpre&H1&H2)".
      { iPureIntro. intros. eapply HINIT. set_solver. }
      iMod (na_heap_name_init tls σ.(heap)) as (name_na_heap) "Hh".
      iMod (ffi_name_init _ _ σ.(world) g with "[$]") as (ffi_names) "(Hw&Hgw&Hstart)"; first auto.
      { eapply HINIT. set_solver. }
      iMod (trace_name_init σ.(trace) σ.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
      iMod (NC_alloc) as (Hc) "HNC".
      set (hnames := {| heap_local_heap_names := name_na_heap;
                      heap_local_ffi_local_names := ffi_names;
                      heap_local_trace_names := name_trace |}).
      iExists ((Hc, hnames) :: cts).
      iModIntro. iFrame.
      rewrite ffi_pre_global_ctx_spec /= ffi_update_pre_get_global //.
    }
  }
  iMod "H" as (cts) "(Hgw&Hres1&Hres2)".
  iExists ((λ x, (fst x, {| pbundleT := snd x |})) <$> cts).
  (* XXX: we need an Hc floating about below because heap_update_pre expects one, but it is
          not really needed. *)
  iMod (NC_alloc) as (Hc) "_".
  iExists
    (λ t σ nt, let _ := heap_globalG_heapG hgG Hc (@pbundleT _ _ t) in
               state_interp σ nt)%I.
  iExists
    (λ g ns κs, ffi_pre_global_ctx Σ heap_preG_ffi ffi_namesg g).
  iExists (λ _ _, True)%I.
  unshelve (iExists _, _, _, _); eauto.
  iMod (Hwp hgG with "[$] [$]") as ">(H1&Hwp)".
  iModIntro.
  iSplitL "H1".
  {  iIntros (???) "Hσ".
    iApply ("H1" with "[Hσ]").
    rewrite //=.
  }
  iFrame "Hgw".
  iSplitL "Hres1".
  { rewrite ?big_sepL2_fmap_r ?big_sepL2_fmap_l. eauto. }
  rewrite /wpd/distributed_weakestpre.wpd.
  iSplit.
  { iModIntro. iIntros (ct Hin). iSplit; first eauto.
    iIntros (g' ns' κs'). rewrite //=. eauto. }
  rewrite ?big_sepL2_fmap_r ?big_sepL2_fmap_l.
  iApply (big_sepL2_mono with "Hwp").
  iIntros (k' (Hc'&Hnames) (e&σ) Hin1 Hin2) "H".
  iDestruct "H" as (Φ Φrx Φinv) "Hwpr".
  set (hG := heap_globalG_heapG hgG Hc Hnames).
  iExists Φ, (λ Hc names v, Φrx (heap_update_local _ hG _ Hc (@pbundleT _ _ names)) v),
    (λ Hc names, Φinv (heap_update_local _ hG _ Hc (@pbundleT _ _ names))).
  rewrite /wpr//=.
  assert (heap_get_local_names Σ (heap_globalG_heapG hgG Hc' Hnames) = Hnames) as Heqnames.
  { rewrite /heap_globalG_heapG.
    rewrite /heap_get_local_names/heap_update_pre//=.
    destruct Hnames => //=. rewrite /na_heapG_get_names/na_heapG_update_pre//=.
    rewrite ffi_update_pre_get_local; eauto. destruct heap_local_heap_names; eauto. }
  rewrite Heqnames.
  iDestruct (wpr_proper_irisG_equiv with "Hwpr") as "Hwpr"; last first.
  { iApply (@recovery_weakestpre.wpr_strong_mono with "Hwpr []").
    iSplit; eauto.
    iModIntro. iSplit; eauto. }
  clear.
  intros Hcnew tnew.
  split_and!; eauto.
  - rewrite //= ffi_update_pre_update. eauto.
  - rewrite //= ffi_update_pre_update.
    iIntros. rewrite ffi_pre_global_ctx_spec; eauto.
    rewrite ffi_update_pre_get_global //=.
    eauto.
Qed.

(* This version might be more useful. Rather than assembling a wpd explicitly
  (which would require tracking and connecting the cts parameter of the wpd) it
  takes as input a list of proofs that, given initial local resources, we can
  construct a wpr for each node. *)
Theorem heap_dist_adequacy_alt `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}
        Σ `{hPre: !heapPreG Σ} k (ebσs : list (expr * state))
        g φinv (HINIT: ∀ σ, σ ∈ snd <$> ebσs → ffi_initP σ.(world) g) :
  (∀ `{Hheap : !heap_globalG Σ},
      ⊢
        ffi_pre_global_start Σ (heap_preG_ffi) (heap_globalG_names) g ={⊤}=∗
        ([∗ list] ebσ ∈ ebσs,
              let eb := fst ebσ in
              let σ := snd ebσ in
              ∀ Hcrash local_names,
              let hG := heap_globalG_heapG Hheap Hcrash local_names in
              ffi_local_start (heapG_ffiG) σ.(world) g ∗
              trace_frag σ.(trace) ∗ oracle_frag σ.(oracle) ={⊤}=∗
              ∃ Φ Φinv Φrx, wpr NotStuck k ⊤ eb eb Φ Φinv Φrx) ∗
        (∀ g, ffi_pre_global_ctx Σ (heap_preG_ffi) (heap_globalG_names) g -∗ |={⊤, ∅}=> ⌜ φinv g ⌝)) →
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  eapply (heap_dist_adequacy _ k); eauto.
  iIntros (??) "H".
  iMod (Hwp with "[$]") as "(Hwprs&Hinv)".
  iModIntro. iIntros "H". iFrame "Hinv".
  rewrite /wpd.
  rewrite ?big_sepL2_fmap_r.
  iDestruct (big_sepL2_length with "[$]") as %Hlength.
  iApply big_sepL.big_sepL2_to_sepL_2'; first auto.
  iDestruct (big_sepL.big_sepL2_to_sepL_2' with "H") as "H"; first auto.
  iDestruct (big_sepL_sep with "[$Hwprs $H]") as "H".
  iApply big_sepL_fupd.
  iApply (big_sepL_mono with "H").
  iIntros (i (eb&σ) Hlookup) "(Hwand&Hres)".
  iDestruct "Hres" as (ct Hlookup2) "Hres".
  iMod ("Hwand" $! (fst ct) (snd ct) with "[$]") as "H".
  iModIntro. iExists _; iSplit; eauto.
  rewrite //=. iDestruct "H" as (???) "H". iExists _, _, _. iFrame.
Qed.
