From New.proof Require Import proof_prelude.
From iris.bi.lib Require Import fractional.

Require Export New.code.sync.atomic.
Require Export New.generatedproof.sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!atomic.GlobalAddrs}.

#[global]
Program Instance is_pkg_init_atomic : IsPkgInit atomic :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_atomic.
#[local] Transparent is_pkg_init_atomic.


Lemma wp_LoadUint64 (addr : loc) dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP atomic @ "LoadUint64" #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
Qed.

Lemma wp_StoreUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP atomic @ "StoreUint64" #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
Qed.

Lemma wp_AddUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
  WP atomic @ "AddUint64" #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  rewrite typed_pointsto_unseal /typed_pointsto_def /=.
  rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
  iApply (wp_atomic_op with "Haddr"); first done.
  iFrame.
Qed.

Lemma wp_CompareAndSwapUint64 (addr : loc) (old : w64) (new : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=>
     ∃ (v: w64) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP atomic @ "CompareAndSwapUint64" #addr #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(? & -> & HΦ)".
  rewrite bool_decide_decide.
  destruct decide.
  {
    subst.
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_auto.
  }
  {
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve; try done.
    { naive_solver. }
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_auto.
  }
Qed.

Lemma wp_LoadInt32 (addr : loc) dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (v : w32), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP atomic @ "LoadInt32" #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
Qed.

Lemma wp_StoreInt32 (addr : loc) (v : w32) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP atomic @ "StoreInt32" #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
Qed.

Lemma wp_AddInt32 (addr : loc) (v : w32) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
  WP atomic @ "AddInt32" #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  rewrite typed_pointsto_unseal /typed_pointsto_def /=.
  rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
  iApply (wp_atomic_op with "Haddr"); first done.
  iFrame.
Qed.

Lemma wp_CompareAndSwapInt32 (addr : loc) (old : w32) (new : w32) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=>
     ∃ (v: w32) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP atomic @ "CompareAndSwapInt32" #addr #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(? & -> & HΦ)".
  rewrite bool_decide_decide.
  destruct decide.
  {
    subst.
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_auto.
  }
  {
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve; try done.
    { naive_solver. }
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_auto.
  }
Qed.

Definition own_Uint64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Uint64.mk (default_val _) (default_val _) v.
#[global] Opaque own_Uint64.
#[local] Transparent own_Uint64.
Global Instance own_Uint64_timeless a b c : Timeless (own_Uint64 a b c) := _.
Global Instance own_Uint64_fractional u v : Fractional (λ q, own_Uint64 u (DfracOwn q) v) := _.
Global Instance own_Uint64_as_fractional u q v :
  AsFractional (own_Uint64 u (DfracOwn q) v) (λ q, own_Uint64 u (DfracOwn q) v) q := _.
Global Instance own_Uint64_combines_gives u v v' dq dq' :
  CombineSepGives (own_Uint64 u dq v) (own_Uint64 u dq' v') (⌜ ✓(dq⋅dq') ∧ v = v'⌝).
Proof. unfold CombineSepGives.
  iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
  rewrite go_type_size_unseal. iDestruct "H" as %?. iModIntro. iPureIntro.
  naive_solver.
Qed.

Lemma wp_Uint64__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Uint64 u dq v ∗ (own_Uint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @ atomic @ "Uint64'ptr" @ "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.


Lemma wp_Uint64__Store u v :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ old, own_Uint64 u (DfracOwn 1) old ∗ (own_Uint64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @ atomic @ "Uint64'ptr" @ "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_StoreUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__Add u delta :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ old, own_Uint64 u (DfracOwn 1) old ∗
  (own_Uint64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
   Φ #(word.add old delta))) -∗
  WP u @ atomic @ "Uint64'ptr" @ "Add" #delta {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_AddUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v dq, own_Uint64 u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Uint64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @ atomic @ "Uint64'ptr" @ "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_CompareAndSwapUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iSplitR.
  { by destruct decide. }
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Definition own_Int32 (u : loc) dq (v : w32) : iProp Σ :=
  u ↦{dq} atomic.Int32.mk (default_val _) v.
#[global] Opaque own_Int32.
#[local] Transparent own_Int32.
Global Instance own_Int32_timeless a b c : Timeless (own_Int32 a b c) := _.
Global Instance own_Int32_fractional u v : Fractional (λ q, own_Int32 u (DfracOwn q) v) := _.
Global Instance own_Int32_as_fractional u q v :
  AsFractional (own_Int32 u (DfracOwn q) v) (λ q, own_Int32 u (DfracOwn q) v) q := _.
Global Instance own_Int32_combines_gives u v v' dq dq' :
  CombineSepGives (own_Int32 u dq v) (own_Int32 u dq' v') (⌜ ✓(dq⋅dq') ∧ v = v'⌝).
Proof. unfold CombineSepGives.
  iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
  rewrite go_type_size_unseal. iDestruct "H" as %?. iModIntro. iPureIntro.
  naive_solver.
Qed.

Lemma wp_Int32__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Int32 u dq v ∗ (own_Int32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @ atomic @ "Int32'ptr" @ "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadInt32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Int32.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.


Lemma wp_Int32__Store u v :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ old, own_Int32 u (DfracOwn 1) old ∗ (own_Int32 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @ atomic @ "Int32'ptr" @ "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_StoreInt32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Int32.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Int32__Add u delta :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ old, own_Int32 u (DfracOwn 1) old ∗
  (own_Int32 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
   Φ #(word.add old delta))) -∗
  WP u @ atomic @ "Int32'ptr" @ "Add" #delta {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_AddInt32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Int32.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Int32__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v dq, own_Int32 u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Int32 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @ atomic @ "Int32'ptr" @ "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_CompareAndSwapInt32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iSplitR.
  { by destruct decide. }
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Int32.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

End wps.
