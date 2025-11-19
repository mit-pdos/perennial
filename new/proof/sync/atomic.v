From New.proof Require Import proof_prelude.
From iris.bi.lib Require Import fractional.

Require Export New.code.sync.atomic.
Require Export New.generatedproof.sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit atomic := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf atomic := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop atomic get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined atomic }}}
    atomic.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init atomic }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto. wp_call.
  iEval (rewrite is_pkg_init_unfold /=). wp_auto.
  wp_bind.
  simpl.
  eapply (tac_wp_pure_wp []).
  (* FIXME: generics where type argument is used under pointer *)
  { Fail apply _. simple apply atomic.wp_struct_make_Pointer. }
  { done. }
  { apply _. }
  simpl fill. wp_auto.
  wp_alloc _unused as "_".
  wp_auto. iFrame "∗#". done.
Qed.

Lemma noCopy_emp l dq :
  ⊢ l ↦{dq} atomic.noCopy.mk.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_def /=.
  replace (flatten_struct (# _)) with ([] : list val).
  - auto.
  - rewrite to_val_unseal /=.
    rewrite struct.val_aux_nil to_val_unseal //.
Qed.

Lemma align_emp l dq :
  ⊢ l ↦{dq} atomic.align64.mk.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_def /=.
  replace (flatten_struct (#_)) with ([] : list val).
  - auto.
  - rewrite to_val_unseal /=.
    rewrite struct.val_aux_nil to_val_unseal //.
Qed.

(* 64-bit structs have an extra field (align64) *)
Definition own_Uint64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Uint64.mk (default_val _) (default_val _) v.
Definition own_Int64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Int64.mk (default_val _) (default_val _) v.
Definition own_Uint32 (u : loc) dq (v : w32) : iProp Σ :=
  u ↦{dq} atomic.Uint32.mk (default_val _) v.
Definition own_Int32 (u : loc) dq (v : w32) : iProp Σ :=
  u ↦{dq} atomic.Int32.mk (default_val _) v.

(* BEGIN TEMPLATE *)
Lemma wp_LoadUint64 (addr : loc) dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP @! atomic.LoadUint64 #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
Qed.

Lemma wp_StoreUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP @! atomic.StoreUint64 #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[>Haddr HΦ]".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
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
  rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
  iApply (wp_atomic_op with "Haddr"); first done.
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

Lemma Uint64_unfold l dq (x: w64) :
  own_Uint64 l dq x ⊣⊢
  l ↦s[atomic.Uint64 :: "v"]{dq} x.
Proof.
  iSplit.
  - iIntros "H".
    iApply struct_fields_split in "H". iNamed "H".
    iFrame.
  - iIntros "Hl".
    iApply @struct_fields_combine.
    iFrame "Hl".
    simpl.
    rewrite -?noCopy_emp -?align_emp.
    done.
Qed.

Lemma wp_Uint64__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v, own_Uint64 u dq v ∗ (own_Uint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @ (ptrT.id atomic.Uint64.id) @ "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
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
  (|={⊤,∅}=> ▷ ∃ old, own_Uint64 u (DfracOwn 1) old ∗ (own_Uint64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @ (ptrT.id atomic.Uint64.id) @ "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_StoreUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__Add u delta :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ old, own_Uint64 u (DfracOwn 1) old ∗
  (own_Uint64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
   Φ #(word.add old delta))) -∗
  WP u @ (ptrT.id atomic.Uint64.id) @ "Add" #delta {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_AddUint64 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Uint64__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v dq, own_Uint64 u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Uint64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @ (ptrT.id atomic.Uint64.id) @ "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_CompareAndSwapUint64 with "[$]").
  iMod "HΦ". iModIntro. iNext.
  iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iSplitR.
  { by destruct decide. }
  iIntros "Hv".

  iMod ("HΦ" with "[-]").
  {
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
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
    unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
  Qed.

  Lemma wp_StoreInt64 (addr : loc) (v : w64) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreInt64 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
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
    rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
    iApply (wp_atomic_op with "Haddr"); first done.
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

  #[global] Opaque own_Int64.
  #[local] Transparent own_Int64.
  Global Instance own_Int64_timeless a b c : Timeless (own_Int64 a b c) := _.
  Global Instance own_Int64_fractional u v : Fractional (λ q, own_Int64 u (DfracOwn q) v) := _.
  Global Instance own_Int64_as_fractional u q v :
    AsFractional (own_Int64 u (DfracOwn q) v) (λ q, own_Int64 u (DfracOwn q) v) q := _.
  Global Instance own_Int64_combines_gives u v v' dq dq' :
    CombineSepGives (own_Int64 u dq v) (own_Int64 u dq' v') (⌜ ✓(dq⋅dq') ∧ v = v'⌝).
  Proof. unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
    rewrite go_type_size_unseal. iDestruct "H" as %?. iModIntro. iPureIntro.
    naive_solver.
  Qed.

  Lemma Int64_unfold l dq (x: w64) :
    own_Int64 l dq x ⊣⊢
    l ↦s[atomic.Int64 :: "v"]{dq} x.
  Proof.
    iSplit.
    - iIntros "H".
      iApply struct_fields_split in "H". iNamed "H".
      iFrame.
    - iIntros "Hl".
      iApply @struct_fields_combine.
      iFrame "Hl".
      simpl.
      rewrite -?noCopy_emp -?align_emp.
      done.
  Qed.

  Lemma wp_Int64__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Int64 u dq v ∗ (own_Int64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @ (ptrT.id atomic.Int64.id) @ "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
      iApply (struct_fields_combine (V:=atomic.Int64.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int64 u (DfracOwn 1) old ∗ (own_Int64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @ (ptrT.id atomic.Int64.id) @ "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int64.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int64 u (DfracOwn 1) old ∗
    (own_Int64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @ (ptrT.id atomic.Int64.id) @ "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddInt64 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int64.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int64__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Int64 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Int64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @ (ptrT.id atomic.Int64.id) @ "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapInt64 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int64.t)).
      iFrame.
    }
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
    unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
  Qed.

  Lemma wp_StoreUint32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreUint32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
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
    rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
    iApply (wp_atomic_op with "Haddr"); first done.
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

  #[global] Opaque own_Uint32.
  #[local] Transparent own_Uint32.
  Global Instance own_Uint32_timeless a b c : Timeless (own_Uint32 a b c) := _.
  Global Instance own_Uint32_fractional u v : Fractional (λ q, own_Uint32 u (DfracOwn q) v) := _.
  Global Instance own_Uint32_as_fractional u q v :
    AsFractional (own_Uint32 u (DfracOwn q) v) (λ q, own_Uint32 u (DfracOwn q) v) q := _.
  Global Instance own_Uint32_combines_gives u v v' dq dq' :
    CombineSepGives (own_Uint32 u dq v) (own_Uint32 u dq' v') (⌜ ✓(dq⋅dq') ∧ v = v'⌝).
  Proof. unfold CombineSepGives.
    iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
    rewrite go_type_size_unseal. iDestruct "H" as %?. iModIntro. iPureIntro.
    naive_solver.
  Qed.

  Lemma Uint32_unfold l dq (x: w32) :
    own_Uint32 l dq x ⊣⊢
    l ↦s[atomic.Uint32 :: "v"]{dq} x.
  Proof.
    iSplit.
    - iIntros "H".
      iApply struct_fields_split in "H". iNamed "H".
      iFrame.
    - iIntros "Hl".
      iApply @struct_fields_combine.
      iFrame "Hl".
      simpl.
      rewrite -?noCopy_emp -?align_emp.
      done.
  Qed.

  Lemma wp_Uint32__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Uint32 u dq v ∗ (own_Uint32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @ (ptrT.id atomic.Uint32.id) @ "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
      iApply (struct_fields_combine (V:=atomic.Uint32.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__Store u v :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Uint32 u (DfracOwn 1) old ∗ (own_Uint32 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @ (ptrT.id atomic.Uint32.id) @ "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Uint32.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Uint32 u (DfracOwn 1) old ∗
    (own_Uint32 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @ (ptrT.id atomic.Uint32.id) @ "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddUint32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Uint32.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Uint32__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Uint32 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Uint32 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @ (ptrT.id atomic.Uint32.id) @ "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapUint32 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Uint32.t)).
      iFrame.
    }
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
    unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
  Qed.

  Lemma wp_StoreInt32 (addr : loc) (v : w32) :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ (oldv : w32), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP @! atomic.StoreInt32 #addr #v {{ Φ }}.
  Proof.
    wp_start as "_".
    iMod "HΦ" as (?) "[>Haddr HΦ]".
    unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
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
    rewrite to_val_unseal /=. rewrite loc_add_0 !right_id.
    iApply (wp_atomic_op with "Haddr"); first done.
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

  Lemma Int32_unfold l dq (x: w32) :
    own_Int32 l dq x ⊣⊢
    l ↦s[atomic.Int32 :: "v"]{dq} x.
  Proof.
    iSplit.
    - iIntros "H".
      iApply struct_fields_split in "H". iNamed "H".
      iFrame.
    - iIntros "Hl".
      iApply @struct_fields_combine.
      iFrame "Hl".
      simpl.
      rewrite -?noCopy_emp -?align_emp.
      done.
  Qed.

  Lemma wp_Int32__Load u dq :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v, own_Int32 u dq v ∗ (own_Int32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP u @ (ptrT.id atomic.Int32.id) @ "Load" #() {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_LoadInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
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
    (|={⊤,∅}=> ▷ ∃ old, own_Int32 u (DfracOwn 1) old ∗ (own_Int32 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP u @ (ptrT.id atomic.Int32.id) @ "Store" #v {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_StoreInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int32.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int32__Add u delta :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ old, own_Int32 u (DfracOwn 1) old ∗
    (own_Int32 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
     Φ #(word.add old delta))) -∗
    WP u @ (ptrT.id atomic.Int32.id) @ "Add" #delta {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_AddInt32 with "[$]").
    iMod "HΦ". iModIntro.
    iDestruct "HΦ" as (?) "[Hown HΦ]".

    iNext. iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int32.t)).
      iFrame.
    }
    iModIntro.
    wp_auto. done.
  Qed.

  Lemma wp_Int32__CompareAndSwap u old new :
    ∀ Φ,
    is_pkg_init atomic -∗
    (|={⊤,∅}=> ▷ ∃ v dq, own_Int32 u dq v ∗
                      ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
    (own_Int32 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
    WP u @ (ptrT.id atomic.Int32.id) @ "CompareAndSwap" #old #new {{ Φ }}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_CompareAndSwapInt32 with "[$]").
    iMod "HΦ". iModIntro. iNext.
    iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

    iDestruct (struct_fields_split with "Hown") as "Hl".
    iNamed "Hl". simpl.
    iExists _. iFrame.
    iSplitR.
    { by destruct decide. }
    iIntros "Hv".

    iMod ("HΦ" with "[-]").
    {
      iApply (struct_fields_combine (V:=atomic.Int32.t)).
      iFrame.
    }
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
  u ↦{dq} atomic.Bool.mk (default_val _) (b32 v).
#[global] Opaque own_Bool.
#[local] Transparent own_Bool.
Global Instance own_Bool_timeless a b c : Timeless (own_Bool a b c) := _.
Global Instance own_Bool_fractional u v : Fractional (λ q, own_Bool u (DfracOwn q) v) := _.
Global Instance own_Bool_as_fractional u q v :
  AsFractional (own_Bool u (DfracOwn q) v) (λ q, own_Bool u (DfracOwn q) v) q := _.
Global Instance own_Bool_combines_gives u v v' dq dq' :
  CombineSepGives (own_Bool u dq v) (own_Bool u dq' v') (⌜ ✓(dq⋅dq') ∧ v = v'⌝).
Proof. unfold CombineSepGives.
  iIntros "?". iDestruct (combine_sep_gives with "[$]") as "#H".
  rewrite go_type_size_unseal. iDestruct "H" as %?. iModIntro. iPureIntro.
  destruct H as [? H2].
  assert (b32 v = b32 v') by congruence.
  naive_solver.
Qed.

Lemma Bool_unfold l dq (x: bool) :
  own_Bool l dq x ⊣⊢
  l ↦s[atomic.Bool :: "v"]{dq} b32 x.
Proof.
  iSplit.
  - iIntros "H".
    iApply struct_fields_split in "H". iNamed "H".
    simpl.
    iFrame.
  - iIntros "Hl".
    iApply @struct_fields_combine.
    iFrame "Hl".
    simpl.
    rewrite -?noCopy_emp -?align_emp.
    done.
Qed.

Lemma wp_Bool__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Bool u dq v ∗ (own_Bool u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @ (ptrT.id atomic.Bool.id) @ "Load" #() {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_LoadUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  {
    (* FIXME: StructFieldsSplit typeclass is shelved unless something is specified up front. *)
    iApply (struct_fields_combine (V:=atomic.Bool.t)).
    iFrame.
  }
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
  (|={⊤,∅}=> ∃ old, own_Bool u (DfracOwn 1) old ∗ (own_Bool u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP u @ (ptrT.id atomic.Bool.id) @ "Store" #v {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_b32.
  wp_apply (wp_StoreUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (?) "[Hown HΦ]".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  {
    iApply (struct_fields_combine (V:=atomic.Bool.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.

Lemma wp_Bool__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v dq, own_Bool u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Bool u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @ (ptrT.id atomic.Bool.id) @ "CompareAndSwap" #old #new {{ Φ }}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_b32.
  wp_apply wp_b32.
  wp_apply (wp_CompareAndSwapUint32 with "[$]").
  iMod "HΦ". iModIntro.
  iDestruct "HΦ" as (??) "(Hown & -> & HΦ)".

  iDestruct (struct_fields_split with "Hown") as "Hl".
  iNamed "Hl". simpl.
  iExists _. iFrame.
  iSplitR.
  { destruct v, old; auto. }
  iIntros "!> Hv".

  iMod ("HΦ" with "[-]").
  {
    iApply (struct_fields_combine (V:=atomic.Bool.t)).
    iFrame.
    simpl.
    rewrite /named.
    iExactEq "Hv".
    f_equal.
    destruct v, old; auto.
  }
  iModIntro.
  wp_auto.
  destruct v, old; auto.
Qed.

(** Pointer *)
Section pointer.
Context `{!IntoVal T'} `{!IntoValTyped T' T} `{!BoundedTypeSize T}.

Definition own_Pointer (u : loc) dq (v : loc) : iProp Σ :=
  u ↦{dq} atomic.Pointer.mk (T:=T) (T':=T') (default_val _) (default_val _) v.
#[global] Opaque own_Pointer.
#[local] Transparent own_Pointer.
Global Instance own_Pointer_timeless a b c : Timeless (own_Pointer a b c) := _.

Lemma wp_Pointer__Load u dq :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Pointer u dq v ∗ (own_Pointer u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP u @ (ptrT.id atomic.Pointer.id) @ "Load" #T {{ Φ }}.
Proof using BoundedTypeSize0.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]"; try tc_solve.
  rewrite /own_Pointer.
  iApply struct_fields_split in "Haddr"; simpl.
  iNamed "Haddr".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve.
  { done. }
  iModIntro.
  iIntros "Hv".
  iMod ("HΦ" with "[H_0 H_1 Hv]") as "HΦ".
  {
    iApply @struct_fields_combine; simpl.
    iFrame.
  }
  done.
Qed.

Lemma wp_Pointer__Store u v' :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ v, own_Pointer u (DfracOwn 1) v ∗ (own_Pointer u (DfracOwn 1) v' ={∅,⊤}=∗ Φ #())) -∗
  WP u @ (ptrT.id atomic.Pointer.id) @ "Store" #T #v' {{ Φ }}.
Proof using BoundedTypeSize0.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]"; try tc_solve.
  rewrite /own_Pointer.
  iApply struct_fields_split in "Haddr"; simpl.
  iNamed "Haddr".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve.
  { done. }
  iModIntro.
  iIntros "Hv".
  iMod ("HΦ" with "[H_0 H_1 Hv]") as "HΦ".
  {
    iApply @struct_fields_combine; simpl.
    iFrame.
  }
  done.
Qed.

Lemma wp_Pointer__CompareAndSwap u old new :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ▷ ∃ v dq, own_Pointer u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Pointer u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP u @ (ptrT.id atomic.Pointer.id) @ "CompareAndSwap" #T #old #new {{ Φ }}.
Proof using BoundedTypeSize0.
  wp_start as "_".
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(>Hown & >-> & HΦ)".
  rewrite /own_Pointer.
  iApply struct_fields_split in "Hown"; simpl.
  iNamed "Hown".
  rewrite bool_decide_decide.
  destruct decide.
  {
    subst.
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iIntros "!> Hv".
    iMod ("HΦ" with "[-]") as "HΦ".
    {
      iApply @struct_fields_combine; simpl.
      iFrame.
    }
    iModIntro.
    by wp_auto.
  }
  {
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve; try done.
    { naive_solver. }
    iIntros "!> Hv".
    iMod ("HΦ" with "[-]") as "HΦ".
    {
      iApply @struct_fields_combine; simpl.
      iFrame.
    }
    iModIntro.
    by wp_auto.
  }
Qed.


End pointer.


End wps.
