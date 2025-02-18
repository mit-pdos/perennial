From New.proof Require Import proof_prelude.

Require Export New.code.sync.atomic.
Require Export New.generatedproof.sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!atomic.GlobalAddrs}.

Definition is_initialized : iProp Σ :=
  "#?" ∷ atomic.is_defined.

Lemma wp_LoadUint64 (addr : loc) dq :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
  WP func_call #atomic.pkg_name' #"LoadUint64" #addr {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_func_call. wp_call.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_Load with "[$]"); try tc_solve; done.
Qed.

Lemma wp_StoreUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
  WP func_call #atomic.pkg_name' #"StoreUint64" #addr #v {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_func_call. wp_call.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  unshelve iApply (wp_typed_AtomicStore with "[$]"); try tc_solve; done.
Qed.

Lemma wp_AddUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
  WP func_call #atomic.pkg_name' #"AddUint64" #addr #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_CompareAndSwapUint64 (addr : loc) (old : w64) (new : w64) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=>
     ∃ (v: w64) dq,
     addr ↦{dq} v ∗
     ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
     (addr ↦{dq} (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))
  ) -∗
  WP func_call #atomic.pkg_name' #"CompareAndSwapUint64" #addr #old #new {{ Φ }}.
Proof.
  iIntros "* #? HΦ".
  wp_func_call. wp_call.
  wp_bind (CmpXchg _ _ _).
  iMod "HΦ" as (??) "(? & -> & HΦ)".
  rewrite bool_decide_decide.
  destruct decide.
  {
    subst.
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_pures.
  }
  {
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve; try done.
    { naive_solver. }
    iIntros "!> ?". iMod ("HΦ" with "[$]"). iModIntro.
    by wp_pures.
  }
Qed.

Definition own_Uint64 (u : loc) dq (v : w64) : iProp Σ :=
  u ↦{dq} atomic.Uint64.mk (default_val _) (default_val _) v.

Lemma wp_Uint64__Load u dq :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ v, own_Uint64 u dq v ∗ (own_Uint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
  WP method_call #atomic.pkg_name' #"Uint64'ptr" #"Load" #u #() {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_method_call. wp_call.
  wp_alloc x_ptr as "Hx_ptr".
  wp_pures. wp_load. wp_pures.
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
  wp_pures. done.
Qed.

Lemma wp_Uint64__Store u v :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ old, own_Uint64 u (DfracOwn 1) old ∗ (own_Uint64 u (DfracOwn 1) v ={∅,⊤}=∗ Φ #())) -∗
  WP method_call #atomic.pkg_name' #"Uint64'ptr" #"Store" #u #v {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_method_call. wp_call.
  wp_alloc x_ptr as "Hx_ptr". wp_pures.
  wp_alloc val_ptr as "Hval_ptr".
  wp_pures. wp_load. wp_pures.
  wp_load. wp_pures.
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
  wp_pures. done.
Qed.

Lemma wp_Uint64__Add u delta :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ old, own_Uint64 u (DfracOwn 1) old ∗
  (own_Uint64 u (DfracOwn 1) (word.add old delta) ={∅,⊤}=∗
   Φ #(word.add old delta))) -∗
  WP method_call #atomic.pkg_name' #"Uint64'ptr" #"Add" #u #delta {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_method_call. wp_call.
  rewrite -default_val_eq_zero_val.
  wp_alloc new_ptr as "Hnew_ptr". wp_pures.
  wp_alloc x_ptr as "Hx_ptr". wp_pures.
  wp_alloc delta_ptr as "Hdelta_ptr". wp_pures.
  wp_load. wp_pures. wp_load. wp_pures.
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
  wp_pures. done.
Qed.

Lemma wp_Uint64__CompareAndSwap u old new :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ v dq, own_Uint64 u dq v ∗
                    ⌜ dq = if decide (v = old) then DfracOwn 1 else dq ⌝ ∗
  (own_Uint64 u dq (if decide (v = old) then new else v) ={∅,⊤}=∗ Φ #(bool_decide (v = old)))) -∗
  WP method_call #atomic.pkg_name' #"Uint64'ptr" #"CompareAndSwap" #u #old #new {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_method_call. wp_call.
  rewrite -default_val_eq_zero_val.
  wp_alloc swapped_ptr as "Hswapped_ptr". wp_pures.
  wp_alloc x_ptr as "Hx_ptr". wp_pures.
  wp_alloc new_ptr as "Hnew_ptr". wp_pures.
  wp_alloc old_ptr as "Hold_ptr". wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures.
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
  wp_pures. done.
Qed.

End wps.
