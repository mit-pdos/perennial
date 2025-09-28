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
  (|={⊤,∅}=> ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP @! atomic.LoadUint64 #addr {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
Qed.

Lemma wp_StoreUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP @! atomic.StoreUint64 #addr #v {{ Φ }}.
Proof.
  wp_start as "_".
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
Qed.

Lemma wp_AddUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_pkg_init atomic -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
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
     ∃ (v: w64) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP @! atomic.CompareAndSwapUint64 #addr #old #new {{ Φ }}.
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
  WP u @ (ptrT.id atomic.Uint64.id) @ "Load" #() {{ Φ }}.
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
  WP u @ (ptrT.id atomic.Uint64.id) @ "Store" #v {{ Φ }}.
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
  WP u @ (ptrT.id atomic.Uint64.id) @ "Add" #delta {{ Φ }}.
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
  WP u @ (ptrT.id atomic.Uint64.id) @ "CompareAndSwap" #old #new {{ Φ }}.
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
    iApply (struct_fields_combine (V:=atomic.Uint64.t)).
    iFrame.
  }
  iModIntro.
  wp_auto. done.
Qed.
(* END TEMPLATE *)

End wps.
