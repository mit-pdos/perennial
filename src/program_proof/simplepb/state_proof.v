From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import state.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.

Section state_proof.
Context `{!heapGS Σ}.

Definition compute_state ops : (gmap u64 (list u8)) :=
  foldl (λ m' op, <[op.1 := (default [] (m' !! op.1)) ++ op.2 ]>m') ∅ ops.

Program Definition pb_record : PBRecord :=
  {|
    pb_OpType := (u64 * list u8) ;
    pb_has_op_encoding := λ op_bytes op, (u64_le op.1 ++ op.2) = op_bytes ;
    pb_has_snap_encoding := λ snap_bytes ops , True ;
    pb_compute_reply :=  λ ops op, default [] ((compute_state ops) !! op.1) ;
  |}.
Obligation 1.
Admitted.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Implicit Type σ : list (list u8).

Context `{!pbG Σ}.
Context `{!ghost_mapG Σ u64 (list u8)}.

Definition own_kvs (γkv:gname) ops : iProp Σ :=
  ghost_map_auth γkv 1 (compute_state ops)
.

Definition stateN := nroot .@ "state".

Definition sys_inv γ γkv : iProp Σ :=
  inv stateN ( ∃ ops, own_log γ ops ∗ own_kvs γkv ops).

Definition kv_ptsto γkv (k:u64) (v:list u8): iProp Σ :=
  k ↪[γkv] v.

Definition is_Clerk γ ck : iProp Σ :=
  ∃ (pb_ck:loc) γsys γsrv,
    "#Hpb_ck" ∷ readonly (ck ↦[state.Clerk :: "cl"] #pb_ck) ∗
    "#His_ck" ∷ is_Clerk pb_ck γsys γsrv ∗
    "#His_inv" ∷ is_inv γ γsys
.

Context `{!urpc_proof.urpcregG Σ}.
Context `{!stagedG Σ}.

Lemma wp_Clerk__FetchAndAppend ck γ γkv key val_sl value Φ:
  sys_inv γ γkv -∗
  is_Clerk γ ck -∗
  is_slice val_sl byteT 1 value -∗
  □((|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (old_value ++ value) ={↑stateN,⊤∖↑pbN}=∗
    (∀ reply_sl, is_slice_small reply_sl byteT 1 old_value -∗
      Φ (#(U64 0), slice_val reply_sl)%V ))) ∗
  (∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ))-∗
  WP state.Clerk__FetchAndAppend #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "#Hinv #Hck Hval_sl #Hupd".
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

  wp_apply (wp_Clerk__Apply with "[] [] Hop_sl").
  { instantiate (1:=(key,value)). done. }
  { iFrame "#". }
  { iFrame "#". }
  iModIntro.
  iSplitL.
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
    iDestruct (ghost_map_lookup with "Hkvs Hkvptsto") as %Hold_value.
    iMod (ghost_map_update (old_value ++ value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

    iMod ("Hclose" with "[Hghost Hkvs]") as "_".
    {
      iNext.
      iExists _; iFrame "Hghost".
      iExactEq "Hkvs".
      unfold own_kvs.
      f_equal.
      unfold compute_state.

      rewrite foldl_snoc.
      simpl.
      f_equal.
      rewrite Hold_value.
      simpl.
      done.
    }
    iMod ("Hupd" with "Hkvptsto") as "Hupd".
    iModIntro.
    iIntros (reply_sl) "Hreply_sl".
    iApply "Hupd".
    iFrame.
    iExactEq "Hreply_sl".
    f_equal.
    unfold compute_reply.
    simpl.
    rewrite Hold_value.
    done.
  }
  {
    iIntros.
    iRight in "Hupd".
    iApply "Hupd".
    done.
  }
Qed.

End state_proof.
