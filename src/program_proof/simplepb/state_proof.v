From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import state.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.

Section state_proof.

Context `{!heapGS Σ, !pbG Σ}.

Implicit Type σ : list (list u8).

Context `{!pbG Σ}.
Context `{!ghost_mapG Σ u64 (list u8)}.

Definition compute_state σ : (gmap u64 (list u8)) :=
  foldl (λ m' op, <[op.1 := (default [] (m' !! op.1)) ++ op.2 ]>m') ∅ ops.

Definition own_kvs (γkv:gname) σ : iProp Σ :=
  ∃ m (ops:list (u64 * (list u8))),
  ⌜σ = map (λ op, (u64_le op.1) ++ op.2) ops⌝ ∗
  ghost_map_auth γkv 1 m ∗
  ⌜m = foldl (λ m' op, <[op.1 := (default [] (m' !! op.1)) ++ op.2 ]>m') ∅ ops⌝
.

Definition stateN := nroot .@ "state".

Definition sys_inv γ γkv : iProp Σ :=
  inv stateN ( ∃ ops, own_log γ σ ∗ own_kvs γkv σ).

Definition kv_ptsto γkv (k:u64) (v:list u8): iProp Σ :=
  k ↪[γkv] v.

Definition is_Clerk ck : iProp Σ :=
  ∃ (cl:loc),
    "#Hcl" ∷ readonly (ck ↦[state.Clerk :: "cl"] #cl).

(* FIXME: this belongs in pb *)
Context `{!urpc_proof.urpcregG Σ}.
Context `{!stagedG Σ}.
Lemma wp_Clerk__PrimaryApply γ ck op_sl op (Φ:val → iProp Σ) :
is_slice op_sl byteT 1 op -∗
(|={⊤∖↑pbN,∅}=> ∃ σ, own_log γ σ ∗
  (own_log γ (σ ++ [op]) ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, is_slice reply_sl byteT 1 (replyFn σ op) -∗ Φ (#(U64 0), slice_val reply_sl)%V)))
∧
(∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ) -∗
WP Clerk__PrimaryApply #ck (slice_val op_sl) {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__FetchAndAppend ck γ γkv key val_sl value Φ:
  sys_inv γ γkv -∗
  is_Clerk ck -∗
  is_slice val_sl byteT 1 value -∗
  (|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (old_value ++ value) ={↑stateN,⊤∖↑pbN}=∗
    (∀ reply_sl, is_slice reply_sl byteT 1 old_value -∗
      Φ (#(U64 0), slice_val reply_sl)%V ))) ∧
  (∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ) -∗
  WP state.Clerk__FetchAndAppend #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "#Hinv #Hck Hval_sl Hupd".
  wp_call.
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (op) "Hop_sl".
  set op_sl:=(Slice.mk _ _ _).
  wp_apply (wp_ref_to).
  { done. }
  replace (int.nat 0%Z) with (0) by word.
  simpl.
  iIntros (op_ptr) "Hop_ptr".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "Hop_sl").
  iIntros (op_sl') "Hop_sl".
  wp_store.
  clear op_sl.
  simpl.

  wp_load.
  wp_apply (wp_WriteBytes with "[$Hop_sl Hval_sl]").
  {
    iDestruct (is_slice_to_small with "Hval_sl") as "$".
  }
  iIntros (op_sl) "[Hop_sl Hval_sl]".
  wp_store.
  clear op_sl'.
  wp_load.
  iNamed "Hck".
  wp_loadField.

  wp_apply (wp_Clerk__PrimaryApply with "Hop_sl").
  iSplit.
  { (* case: successful response *)
    iLeft in "Hupd".
    iMod "Hupd".
    iInv "Hinv" as ">Hown" "Hclose".
    replace (↑_∖_) with (∅:coPset); last set_solver.
    iModIntro.

    iDestruct "Hupd" as (?) "[Hkvptsto Hupd]".
    iDestruct "Hown" as (?) "[Hown Hkvs]".
    iExists _.
    iFrame.

    iIntros "Hghost".
    iDestruct "Hkvs" as (m ops) "(%Hσ_ops & Hkvs & %Hstate)".
    iDestruct (ghost_map_lookup with "Hkvs Hkvptsto") as %Hold_value.
    iMod (ghost_map_update (old_value ++ value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

    iMod ("Hclose" with "[Hghost Hkvs]") as "_".
    {
      iNext.
      iExists _; iFrame "Hghost".
      iExists _, (ops ++ [(key, value)]).
      iFrame "Hkvs".
      iPureIntro.
      split.
      {
        rewrite map_app.
        f_equal.
        done.
      }
      {
        rewrite foldl_snoc.
        simpl.
        rewrite Hstate.
        f_equal.
        rewrite -Hstate.
        rewrite Hold_value.
        simpl.
        done.
      }
    }
    iMod ("Hupd" with "Hkvptsto") as "Hupd".
    iModIntro.
    iIntros (reply_sl) "Hreply_sl".
    iApply "Hupd".
    iFrame.
    iExactEq "Hreply_sl".
    f_equal.
    admit. (* FIXME: need to define replyFn *)
  }
  {
    iIntros.
    iRight in "Hupd".
    iApply "Hupd".
    done.
  }
Admitted.

End state_proof.
