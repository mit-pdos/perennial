From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre distributed_weakestpre distributed_adequacy.
From Perennial.goose_lang Require Export wpr_lifting wpd_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
Set Default Proof Using "Type".

Theorem heap_dist_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}
        Σ `{hPre: !heapPreG Σ} k (ebσs : list (expr * state))
        g φinv (HINIT: ∀ σ, σ ∈ snd <$> ebσs → ffi_initP σ.(world) g) :
  (∀ `{Hheap : !heap_globalG Σ} (cts : list (crashG Σ * heap_local_names)),
      ⊢
        ffi_pre_global_start Σ (heap_preG_ffi) (heap_globalG_names) g -∗
        ([∗ list] i ↦ ct; σ ∈ cts; snd <$> ebσs,
              let hG := heap_globalG_heapG Hheap (fst ct) (snd ct) in
              ffi_local_start (heapG_ffiG) σ.(world) g ∗ trace_frag σ.(trace) ∗ oracle_frag σ.(oracle)) ={⊤}=∗
        (∀ g, ffi_pre_global_ctx Σ (heap_preG_ffi) (heap_globalG_names) g -∗ |={⊤, ∅}=> ⌜ φinv g ⌝) ∗
        wpd k ⊤ cts (fst <$> ebσs)) →
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  eapply (wpd_dist_adequacy_inv _ _ _ heap_namesO).
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
  iExists ((λ x, (fst x, {| pbundleT := (hgG_extend_local_names hgG (snd x))|})) <$> cts).
  (* XXX: we need an Hc floating about below because heap_update_pre expects one, but it is
          not really needed. *)
  iMod (NC_alloc) as (Hc) "_".
  iExists
    (λ t σ nt, let _ := heap_update_pre Σ hPre Hinv Hc (@pbundleT _ _ t) in
               state_interp σ nt)%I.
  iExists
    (λ g ns κs, ffi_pre_global_ctx Σ heap_preG_ffi ffi_namesg g).
  iExists _. (* (λ Hc t, λ (σ0 : state) (_ : nat) (κs0 : list observation) (_ : nat),
                                              lifting.heapG_irisG_obligation_1 Σ
                                                (heap_update Σ (heap_update_pre Σ hPre Hinv Hc hnames) Hinv Hc
                                                   pbundleT) σ0 κs0). *)
  iExists _.
  iExists _.
  iExists _.
  iExists _.
  iMod (Hwp hgG with "[$] [$]") as "(H1&Hwp)".
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
  { iPureIntro. intros ct.
    rewrite /equal_global_inG.
    rewrite elem_of_list_fmap. intros ((?&?)&Heq&Hin).
    rewrite Heq //=.
  }
  rewrite ?big_sepL2_fmap_r ?big_sepL2_fmap_l.
  iApply (big_sepL2_mono with "Hwp").
  iIntros (k' (Hc'&Hnames) (e&σ) Hin1 Hin2) "H".
  iDestruct "H" as (Φ Φrx Φinv) "Hwpr".
  iExists Φ, (λ Hc names v, Φrx (heap_update_pre _ _ _ Hc (@pbundleT _ _ names)) v),
    (λ Hc names, Φinv (heap_update_pre _ _ _ Hc (@pbundleT _ _ names))).
  rewrite /wpr//=.
  assert (Build_pbundleG _ Σ (heap_get_names Σ (heap_globalG_heapG hgG Hc' Hnames)) =
          Build_pbundleG _ Σ (hgG_extend_local_names hgG Hnames)) as ->.
  { f_equal.
    rewrite /hgG_extend_local_names.
    rewrite /heap_globalG_heapG.
    rewrite heap_update_pre_get //=. }
  iExactEq "Hwpr". f_equal.
  { admit. }
  { rewrite /heap_globalG_heapG.
    rewrite /hgG_extend_local_names//=. admit. }
Abort.
