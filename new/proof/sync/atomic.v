From New.proof Require Import proof_prelude.

Require Export New.code.sync.atomic.
Require Export New.generatedproof.sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!atomic.GlobalAddrs}.

Definition is_initialized : iProp Σ :=
  "#?" ∷ atomic.is_defined.

Definition own_Uint64 (u : loc) (v : w64) : iProp Σ :=
  u ↦ atomic.Uint64.mk atomic.noCopy.mk atomic.align64.mk v.

Lemma wp_LoadUint64 (addr : loc) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ (v : w64), addr ↦ v ∗ (addr ↦ v ={∅,⊤}=∗ Φ #v)) -∗
  WP func_call #atomic.pkg_name' #"LoadUint64" #addr {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  wp_func_call. wp_call.
  iMod "HΦ" as (?) "[Haddr HΦ]".
  rewrite to_val_unseal.
  iApply (wp_load with "[Haddr]").
  { rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /= right_id loc_add_0 //. }
  iNext. iIntros "H". iApply "HΦ".
  rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /= right_id loc_add_0 //.
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
  rewrite to_val_unseal.
  iApply (wp_atomic_store with "[Haddr]").
  { rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /= right_id loc_add_0 //. }
  iNext. iIntros "H". iApply "HΦ".
  rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /= right_id loc_add_0 //.
Qed.

Lemma wp_AddUint64 (addr : loc) (v : w64) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ (oldv : w64), addr ↦ oldv ∗ (addr ↦ (word.add oldv v) ={∅,⊤}=∗ Φ #(word.add oldv v))) -∗
  WP func_call #atomic.pkg_name' #"AddUint64" #addr #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_Uint64__Load u :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ v, own_Uint64 u v ∗ (own_Uint64 u v ={∅,⊤}=∗ Φ #v)) -∗
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
  (|={⊤,∅}=> ∃ oldv, own_Uint64 u oldv ∗ (own_Uint64 u v ={∅,⊤}=∗ Φ #())) -∗
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
  (|={⊤,∅}=> ∃ oldv, own_Uint64 u oldv ∗ (own_Uint64 u (word.add oldv delta) ={∅,⊤}=∗ Φ #(word.add oldv delta))) -∗
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

End wps.
