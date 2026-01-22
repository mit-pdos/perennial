From New.proof Require Import proof_prelude.
From iris.bi.lib Require Import fractional.

Require Export New.code.sync.atomic.
Require Export New.generatedproof.sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : atomic.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) atomic := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) atomic := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop atomic get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    atomic.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init atomic }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=).
  wp_alloc _unused as "_". wp_auto. iFrame "∗#". done.
Qed.

Lemma noCopy_emp l dq :
  ⊢ l ↦{dq} atomic.noCopy.mk : iProp Σ.
Proof. rewrite typed_pointsto_unseal //=. Qed.

Lemma align_emp l dq :
  ⊢ l ↦{dq} atomic.align64.mk : iProp Σ.
Proof. rewrite typed_pointsto_unseal //=. Qed.

(* 64-bit structs have an extra field (align64) *)
Definition own_Uint64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Uint64.mk (zero_val _) (zero_val _) v.
Definition own_Int64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Int64.mk (zero_val _) (zero_val _) v.
Definition own_Uint32 (u : loc) dq (v : w32) : iProp Σ :=
  u ↦{dq} atomic.Uint32.mk (zero_val _) v.
Definition own_Int32 (u : loc) dq (v : w32) : iProp Σ :=
  u ↦{dq} atomic.Int32.mk (zero_val _) v.

(* BEGIN TEMPLATE *)
Lemma wp_LoadUint64 (addr : loc) dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP @! atomic.LoadUint64 #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_load with "[$]"). done.
Qed.

Lemma wp_SwapUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
  WP @! atomic.SwapUint64 #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_swap with "[$]"). done.
Qed.

Lemma wp_StoreUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP @! atomic.StoreUint64 #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (AtomicSwap _ _).
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_swap with "[$]") as "Haddr".
  iMod ("HΦ" with "Haddr") as "HΦ".
  iModIntro. wp_pures.
  wp_end.
Qed.

Lemma wp_AddUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
  WP @! atomic.AddUint64 #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  rewrite typed_pointsto_unseal /typed_pointsto_def /=.
  rewrite !go.into_val_unfold /=.
  wp_apply (wp_atomic_op with "Haddr"); first done.
  iFrame.
Qed.

Lemma wp_CompareAndSwapUint64 (addr : loc) (old : w64) (new : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=>
     ▷ ∃ (v: w64) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP @! atomic.CompareAndSwapUint64 #addr #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(>? & >-> & HΦ)".
  rewrite bool_decide_decide.
  destruct decide; subst.
  - wp_apply (wp_cmpxchg_suc with "[$]") as "?"; first done.
    iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
  -  wp_apply (wp_cmpxchg_fail with "[$]") as "?"; first done.
     iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
Qed.

#[global] Opaque own_Uint64.
#[local] Transparent own_Uint64.
Global Instance own_Uint64_timeless a b c : Timeless (own_Uint64 a b c) := _.
Global Instance own_Uint64_fractional u v :
  Fractional (λ q, own_Uint64 u (DfracOwn q) v).
Proof. apply fractional_of_dfractional. apply _. Qed.
Global Instance own_Uint64_as_fractional u q v :
  AsFractional (own_Uint64 u (DfracOwn q) v) (λ q, own_Uint64 u (DfracOwn q) v) q := _.
Global Instance own_Uint64_combines_gives u v v' dq dq' :
  CombineSepGives (own_Uint64 u dq v) (own_Uint64 u dq' v') (⌜ v = v'⌝).
Proof. unfold CombineSepGives.
  iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
  iDestruct "H" as %?. iModIntro. iPureIntro.
  naive_solver.
Qed.

Lemma wp_Uint64__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v, own_Uint64 u dq v ∗ (own_Uint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @! (go.PointerType atomic.Uint64) @! "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".
  iNext.
  iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__Store u v :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ old, own_Uint64 u (DfracOwn 1) old ∗ (own_Uint64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @! (go.PointerType atomic.Uint64) @! "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_StoreUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iNext. iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__Add u delta :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ old, own_Uint64 u (DfracOwn 1) old ∗
  (own_Uint64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
   Φ #(word.add old delta))) -∗
  WP u @! (go.PointerType atomic.Uint64) @! "Add" #delta {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_AddUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iNext. iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v dq, own_Uint64 u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Uint64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @! (go.PointerType atomic.Uint64) @! "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_CompareAndSwapUint64 with "[$]").
  iMod "HΦ". iModIntro. iNext.
  iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

  iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iSplitR.
  { by destruct decide. }
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto. done.
Qed.
(* END TEMPLATE *)

(* AUTO-GENERATED - DO NOT EDIT *)
  (* auto-generated by int_template.py *)
  (** Int64 *)
  Lemma wp_LoadInt64 (addr : loc) dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP @! atomic.LoadInt64 #addr {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_load with "[$]"). done.
  Qed.

  Lemma wp_SwapInt64 (addr : loc) (v : w64) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
    WP @! atomic.SwapInt64 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]"). done.
  Qed.

  Lemma wp_StoreInt64 (addr : loc) (v : w64) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreInt64 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (AtomicSwap _ _).
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]") as "Haddr".
    iMod ("HΦ" with "Haddr") as "HΦ".
    iModIntro. wp_pures.
    wp_end.
  Qed.

  Lemma wp_AddInt64 (addr : loc) (v : w64) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
    WP @! atomic.AddInt64 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[Haddr HΦ]".
    rewrite typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite !go.into_val_unfold /=.
    wp_apply (wp_atomic_op with "Haddr"); first done.
    iFrame.
  Qed.

  Lemma wp_CompareAndSwapInt64 (addr : loc) (old : w64) (new : w64) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=>
       ▷ ∃ (v: w64) dq,
       addr ↦{dq} v ∗
       ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
       (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
    ) -∗
    WP @! atomic.CompareAndSwapInt64 #addr #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (CmpXchg _ _ _).
    iMod "HΦ" as (??) "(>? & >-> & HΦ)".
    rewrite bool_decide_decide.
    destruct decide; subst.
    - wp_apply (wp_cmpxchg_suc with "[$]") as "?"; first done.
      iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
    -  wp_apply (wp_cmpxchg_fail with "[$]") as "?"; first done.
       iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
  Qed.

  #[global] Opaque own_Int64.
  #[local] Transparent own_Int64.
  Global Instance own_Int64_timeless a b c : Timeless (own_Int64 a b c) := _.
  Global Instance own_Int64_fractional u v :
    Fractional (λ q, own_Int64 u (DfracOwn q) v).
  Proof. apply fractional_of_dfractional. apply _. Qed.
  Global Instance own_Int64_as_fractional u q v :
    AsFractional (own_Int64 u (DfracOwn q) v) (λ q, own_Int64 u (DfracOwn q) v) q := _.
  Global Instance own_Int64_combines_gives u v v' dq dq' :
    CombineSepGives (own_Int64 u dq v) (own_Int64 u dq' v') (⌜ v = v'⌝).
  Proof. unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
    iDestruct "H" as %?. iModIntro. iPureIntro.
    naive_solver.
  Qed.

  Lemma wp_Int64__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Int64 u dq v ∗ (own_Int64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @! (go.PointerType atomic.Int64) @! "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".
    iNext.
    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int64 u (DfracOwn 1) old ∗ (own_Int64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @! (go.PointerType atomic.Int64) @! "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int64 u (DfracOwn 1) old ∗
    (own_Int64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @! (go.PointerType atomic.Int64) @! "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Int64 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Int64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @! (go.PointerType atomic.Int64) @! "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapInt64 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  (** Uint32 *)
  Lemma wp_LoadUint32 (addr : loc) dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : w32), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP @! atomic.LoadUint32 #addr {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_load with "[$]"). done.
  Qed.

  Lemma wp_SwapUint32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
    WP @! atomic.SwapUint32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]"). done.
  Qed.

  Lemma wp_StoreUint32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreUint32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (AtomicSwap _ _).
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]") as "Haddr".
    iMod ("HΦ" with "Haddr") as "HΦ".
    iModIntro. wp_pures.
    wp_end.
  Qed.

  Lemma wp_AddUint32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
    WP @! atomic.AddUint32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[Haddr HΦ]".
    rewrite typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite !go.into_val_unfold /=.
    wp_apply (wp_atomic_op with "Haddr"); first done.
    iFrame.
  Qed.

  Lemma wp_CompareAndSwapUint32 (addr : loc) (old : w32) (new : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=>
       ▷ ∃ (v: w32) dq,
       addr ↦{dq} v ∗
       ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
       (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
    ) -∗
    WP @! atomic.CompareAndSwapUint32 #addr #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (CmpXchg _ _ _).
    iMod "HΦ" as (??) "(>? & >-> & HΦ)".
    rewrite bool_decide_decide.
    destruct decide; subst.
    - wp_apply (wp_cmpxchg_suc with "[$]") as "?"; first done.
      iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
    -  wp_apply (wp_cmpxchg_fail with "[$]") as "?"; first done.
       iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
  Qed.

  #[global] Opaque own_Uint32.
  #[local] Transparent own_Uint32.
  Global Instance own_Uint32_timeless a b c : Timeless (own_Uint32 a b c) := _.
  Global Instance own_Uint32_fractional u v :
    Fractional (λ q, own_Uint32 u (DfracOwn q) v).
  Proof. apply fractional_of_dfractional. apply _. Qed.
  Global Instance own_Uint32_as_fractional u q v :
    AsFractional (own_Uint32 u (DfracOwn q) v) (λ q, own_Uint32 u (DfracOwn q) v) q := _.
  Global Instance own_Uint32_combines_gives u v v' dq dq' :
    CombineSepGives (own_Uint32 u dq v) (own_Uint32 u dq' v') (⌜ v = v'⌝).
  Proof. unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
    iDestruct "H" as %?. iModIntro. iPureIntro.
    naive_solver.
  Qed.

  Lemma wp_Uint32__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Uint32 u dq v ∗ (own_Uint32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @! (go.PointerType atomic.Uint32) @! "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".
    iNext.
    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Uint32 u (DfracOwn 1) old ∗ (own_Uint32 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @! (go.PointerType atomic.Uint32) @! "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Uint32 u (DfracOwn 1) old ∗
    (own_Uint32 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @! (go.PointerType atomic.Uint32) @! "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Uint32 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Uint32 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @! (go.PointerType atomic.Uint32) @! "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapUint32 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  (** Int32 *)
  Lemma wp_LoadInt32 (addr : loc) dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : w32), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP @! atomic.LoadInt32 #addr {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_load with "[$]"). done.
  Qed.

  Lemma wp_SwapInt32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
    WP @! atomic.SwapInt32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]"). done.
  Qed.

  Lemma wp_StoreInt32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreInt32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (AtomicSwap _ _).
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    wp_apply (wp_atomic_swap with "[$]") as "Haddr".
    iMod ("HΦ" with "Haddr") as "HΦ".
    iModIntro. wp_pures.
    wp_end.
  Qed.

  Lemma wp_AddInt32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
    WP @! atomic.AddInt32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[Haddr HΦ]".
    rewrite typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite !go.into_val_unfold /=.
    wp_apply (wp_atomic_op with "Haddr"); first done.
    iFrame.
  Qed.

  Lemma wp_CompareAndSwapInt32 (addr : loc) (old : w32) (new : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=>
       ▷ ∃ (v: w32) dq,
       addr ↦{dq} v ∗
       ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
       (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
    ) -∗
    WP @! atomic.CompareAndSwapInt32 #addr #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_bind (CmpXchg _ _ _).
    iMod "HΦ" as (??) "(>? & >-> & HΦ)".
    rewrite bool_decide_decide.
    destruct decide; subst.
    - wp_apply (wp_cmpxchg_suc with "[$]") as "?"; first done.
      iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
    -  wp_apply (wp_cmpxchg_fail with "[$]") as "?"; first done.
       iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
  Qed.

  #[global] Opaque own_Int32.
  #[local] Transparent own_Int32.
  Global Instance own_Int32_timeless a b c : Timeless (own_Int32 a b c) := _.
  Global Instance own_Int32_fractional u v :
    Fractional (λ q, own_Int32 u (DfracOwn q) v).
  Proof. apply fractional_of_dfractional. apply _. Qed.
  Global Instance own_Int32_as_fractional u q v :
    AsFractional (own_Int32 u (DfracOwn q) v) (λ q, own_Int32 u (DfracOwn q) v) q := _.
  Global Instance own_Int32_combines_gives u v v' dq dq' :
    CombineSepGives (own_Int32 u dq v) (own_Int32 u dq' v') (⌜ v = v'⌝).
  Proof. unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
    iDestruct "H" as %?. iModIntro. iPureIntro.
    naive_solver.
  Qed.

  Lemma wp_Int32__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Int32 u dq v ∗ (own_Int32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @! (go.PointerType atomic.Int32) @! "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".
    iNext.
    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int32__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int32 u (DfracOwn 1) old ∗ (own_Int32 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @! (go.PointerType atomic.Int32) @! "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int32__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int32 u (DfracOwn 1) old ∗
    (own_Int32 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @! (go.PointerType atomic.Int32) @! "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int32__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Int32 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Int32 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @! (go.PointerType atomic.Int32) @! "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapInt32 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iStructNamed "Hown". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    { iApply typed_pointsto_combine. iFrame. }
    iModIntro.
    wp_auto. done.
  Qed.

(* END AUTO-GENERATED *)

(** Bool *)
(* Uint64 proof adapted for Bool - not part of template generation because it
doesn't exactly fit the pattern *)
Definition b32 (b: bool): w32 := W32 (if b then 1 else 0).

#[global] Instance b32_inj : Inj (=) (=) b32.
Proof.
  intros b1 b2 H.
  rewrite /b32 in H.
  destruct b1, b2; auto; word.
Qed.

Definition own_Bool (u : loc) dq (v : bool) : iProp Σ :=
  u ↦{dq} atomic.Bool.mk (zero_val _) (b32 v).
#[global] Opaque own_Bool.
#[local] Transparent own_Bool.
Global Instance own_Bool_timeless a b c : Timeless (own_Bool a b c) := _.
Global Instance own_Bool_fractional u v : Fractional (λ q, own_Bool u (DfracOwn q) v).
Proof. apply fractional_of_dfractional. apply _. Qed.
Global Instance own_Bool_as_fractional u q v :
  AsFractional (own_Bool u (DfracOwn q) v) (λ q, own_Bool u (DfracOwn q) v) q := _.
Global Instance own_Bool_combines_gives u v v' dq dq' :
  CombineSepGives (own_Bool u dq v) (own_Bool u dq' v') (⌜ v = v'⌝).
Proof. unfold CombineSepGives.
  iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
  iDestruct "H" as %?. iModIntro. iPureIntro.
  assert (b32 v = b32 v') by congruence.
  naive_solver.
Qed.

Lemma wp_Bool__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷∃ v, own_Bool u dq v ∗ (own_Bool u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @! (go.PointerType atomic.Bool) @! "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[>Hown HΦ]".
  iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto.
  destruct v; auto.
Qed.

Lemma wp_b32 (b: bool) :
  ∀ Φ,
    is_pkg_init atomic -∗
    Φ (#(b32 b)) -∗ WP @! atomic.b32 #b {{ Φ }}.
Proof.
  iIntros (Φ) "#? HΦ".
  wp_func_call.
  wp_call. wp_auto.
  destruct b; wp_auto; iFrame.
Qed.

Lemma wp_Bool__Store u (v: bool) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷∃ old, own_Bool u (DfracOwn 1) old ∗ (own_Bool u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @! (go.PointerType atomic.Bool) @! "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_b32.
  wp_apply (wp_StoreUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[>Hown HΦ]".

  iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Bool__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷∃ v dq, own_Bool u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Bool u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @! (go.PointerType atomic.Bool) @! "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_b32.
  wp_apply wp_b32.
  wp_apply (wp_CompareAndSwapUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (??) "(>Hown & >-> & HΦ)".

  iStructNamed "Hown". simpl.
  iExists _. iFrame.
  iSplitR.
  { destruct v, old; auto. }
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  { iApply typed_pointsto_combine. iFrame. simpl.
    iSplitL; last done. rewrite /named. iExactEq "Hv". f_equal.
    destruct v, old; auto.
  }
  iModIntro.
  wp_auto.
  destruct v, old; auto.
Qed.

(** Pointer *)
Lemma wp_LoadPointer (addr : loc) dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (v : loc), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP @! atomic.LoadPointer #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_load with "[$]"). done.
Qed.

Lemma wp_SwapPointer (addr : loc) (v : loc) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : loc), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
  WP @! atomic.SwapPointer #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_swap with "[$]"). done.
Qed.

Lemma wp_StorePointer (addr : loc) (v : loc) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : loc), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP @! atomic.StorePointer #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (AtomicSwap _ _).
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  wp_apply (wp_atomic_swap with "[$]") as "Haddr".
  iMod ("HΦ" with "Haddr") as "HΦ".
  iModIntro. wp_pures.
  wp_end.
Qed.

Lemma wp_CompareAndSwapPointer (addr : loc) (old new : loc) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=>
     ▷ ∃ (v: loc) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP @! atomic.CompareAndSwapPointer #addr #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(>? & >-> & HΦ)".
  rewrite bool_decide_decide.
  destruct decide; subst.
  - wp_apply (wp_cmpxchg_suc with "[$]") as "?"; first done.
    iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
  -  wp_apply (wp_cmpxchg_fail with "[$]") as "?"; first done.
     iMod ("HΦ" with "[$]"). iModIntro. by wp_auto.
Qed.


Section pointer.
Context `{!ZeroVal T'} `{!TypedPointsto T'} `{!IntoValTyped T' T} `{!go.TypeRepr T T'}.

Definition own_Pointer (u : loc) dq (v : loc) : iProp Σ :=
  u ↦{dq} atomic.Pointer.mk T' (zero_val _) (zero_val _) v.
#[global] Opaque own_Pointer.
#[local] Transparent own_Pointer.
Global Instance own_Pointer_timeless a b c : Timeless (own_Pointer a b c) := _.

Lemma wp_Pointer__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Pointer u dq v ∗ (own_Pointer u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @! (go.PointerType $ atomic.Pointer T) @! "Load" #() {{ Φ }}.
Proof.
  wp_start as "_". wp_auto.
  wp_bind.
  wp_apply wp_LoadPointer.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  iStructNamed "Haddr". simpl. iFrame.
  iModIntro. iModIntro. iIntros "Hv".
  iMod ("HΦ" with "[_0 _1 Hv]") as "HΦ".
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro. wp_auto. wp_end.
Qed.

Lemma wp_Pointer__Swap u v' :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Pointer u (DfracOwn 1) v ∗ (own_Pointer u (DfracOwn 1) v' ={∅,⊤}=∗ Φ #v)) -∗
  WP u @! (go.PointerType (atomic.Pointer T)) @! "Swap" #v' {{ Φ }}.
Proof.
  wp_start as "_". wp_auto.
  wp_apply wp_SwapPointer.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  iStructNamed "Haddr". simpl. iFrame.
  iModIntro. iNext. iIntros "Hv".
  iMod ("HΦ" with "[_0 _1 Hv]") as "HΦ".
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro. wp_auto. wp_end.
Qed.

Lemma wp_Pointer__Store u v' :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Pointer u (DfracOwn 1) v ∗ (own_Pointer u (DfracOwn 1) v' ={∅,⊤}=∗ Φ #())) -∗
  WP u @! (go.PointerType (atomic.Pointer T)) @! "Store" #v' {{ Φ }}.
Proof.
  wp_start as "_". wp_auto.
  wp_apply wp_StorePointer.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  iStructNamed "Haddr". simpl. iFrame.
  iModIntro. iNext. iIntros "Hv".
  iMod ("HΦ" with "[_0 _1 Hv]") as "HΦ".
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro.
  wp_pures.
  done.
Qed.

Lemma wp_Pointer__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v dq, own_Pointer u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Pointer u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @! (go.PointerType (atomic.Pointer T)) @! "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_". wp_auto.
  wp_apply wp_CompareAndSwapPointer.
  iMod "HΦ" as (??) "(>Hown & >-> & HΦ)".
  iStructNamed "Hown". simpl. iFrame.
  iModIntro. iNext. iSplitR.
  { by destruct decide. }
  iIntros "Hv". iMod ("HΦ" with "[_0 _1 Hv]") as "HΦ".
  { iApply typed_pointsto_combine. iFrame. }
  iModIntro. wp_auto. wp_end.
Qed.

End pointer.

End wps.
