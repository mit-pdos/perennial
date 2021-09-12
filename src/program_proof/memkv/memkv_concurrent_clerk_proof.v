From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_logic Require Import atomic_fupd.
From Perennial.program_proof.memkv Require Export common_proof memkv_coord_definitions memkv_clerk_proof.

Section memkv_concurrent_clerk_proof.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !rpcG Σ ShardReplyC, !rpcregG Σ, !kvMapG Σ}.

Local Definition own_ConcMemKVClerk (p:loc) (γ:memkv_coord_names) : iProp Σ :=
  ∃ (freeClerks_sl:Slice.t) (freeClerks:list loc),
  "HfreeClerks" ∷ p ↦[KVClerkPool :: "freeClerks"] (slice_val freeClerks_sl) ∗
  "HfreeClerks_sl" ∷ is_slice_small (V:=loc) freeClerks_sl MemKVClerkPtr 1 freeClerks ∗
  "HfreeClerks_own" ∷ [∗ list] ck ∈ freeClerks, own_MemKVClerk ck γ.(coord_kv_gn)
.

(* FIXME: imports are screwed somewhere, [val] is shadowed the wrong way. *)
Definition is_ConcMemKVClerk (p_ptr:loc) (γ:memkv_coord_names) : iProp Σ :=
  ∃ (coord:u64) mu,
  "#Hmu" ∷ readonly (p_ptr ↦[KVClerkPool :: "mu"] mu) ∗
  "#Hcoord" ∷ readonly (p_ptr ↦[KVClerkPool :: "coord"] #coord) ∗
  "#Hiscoord" ∷ is_coord_server coord γ ∗
  "#Hinv" ∷ is_lock nroot mu (own_ConcMemKVClerk p_ptr γ)
.

Local Lemma wp_KVClerkPool__getClerk p γ :
  is_ConcMemKVClerk p γ -∗
  {{{ True }}}
    KVClerkPool__getClerk #p
  {{{ (ck:loc), RET #ck; own_MemKVClerk ck γ.(coord_kv_gn) }}}.
Proof.
  iIntros "#Hcck !> %Φ _ HΦ".
  Opaque zero_val.
  wp_lam.
  iNamed "Hcck".
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]". iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (cl_ptr) "Hcl_ptr".
  Transparent zero_val.
  simpl.
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (decide (int.nat freeClerks_sl.(Slice.sz) = 0)) as [Hzero|Hnzero].
  - (* creating new clerk *)
    rewrite bool_decide_true; last first.
    { do 2 f_equal. word. }
    wp_loadField.
    wp_apply (release_spec'' with "Hinv [-HΦ Hcl_ptr]").
    { iFrame. rewrite /own_ConcMemKVClerk. eauto with iFrame. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_MakeMemKVClerk with "Hiscoord").
    iIntros (ck) "Hck".
    wp_store.
    wp_load.
    iApply "HΦ".
    eauto.
  - (* using existing clerk *)
    rewrite bool_decide_false; last first.
    { intros [=Hz]. apply Hnzero. rewrite Hz. word. }
    wp_loadField.
    iDestruct (is_slice_small_sz with "HfreeClerks_sl") as %Hlen.
    destruct freeClerks as [|Hck freeClerks].
    { exfalso. apply Hnzero. done. }
    wp_apply (wp_SliceGet (V:=loc) with "[$HfreeClerks_sl]").
    { iPureIntro. done. }
    iIntros "HfreeClerks_sl".
    wp_store.

    wp_loadField.
    wp_apply wp_SliceSkip'.
    { iPureIntro. word. }
    wp_bind (struct.storeF _ _ _ _).
    (* FIXME why do we have to apply storeField by hand here? *)
    iApply (wp_storeField with "HfreeClerks").
    { rewrite /field_ty. simpl. val_ty. }
    iIntros "!> HfreeClerks".
    iDestruct "HfreeClerks_own" as "[Hck HfreeClerks_own]".
    wp_loadField.
    wp_apply (release_spec'' with "Hinv [$Hlocked HfreeClerks_own HfreeClerks_sl HfreeClerks]").
    { rewrite /own_ConcMemKVClerk. iModIntro. iExists _, _. iFrame.
      iDestruct (slice_small_split _ 1 with "HfreeClerks_sl") as "[_ $]".
      simpl. word. }
    wp_load.
    iApply "HΦ".
    eauto.
Qed.

End memkv_concurrent_clerk_proof.
