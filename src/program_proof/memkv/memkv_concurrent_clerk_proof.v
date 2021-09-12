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
  "HfreeClerks_sl" ∷ is_slice (V:=loc) freeClerks_sl MemKVClerkPtr 1 freeClerks ∗
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
  wp_lam.
  iNamed "Hcck".
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]". iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (decide (int.nat freeClerks_sl.(Slice.sz) = 0)) as [Hzero|Hnzero].
  - (* creating new clerk *)
    rewrite bool_decide_true; last first.
    { do 2 f_equal. word. }
    wp_loadField.
    wp_apply (release_spec'' with "Hinv [-HΦ]").
    { iFrame. rewrite /own_ConcMemKVClerk. eauto with iFrame. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_MakeMemKVClerk with "Hiscoord").
    iIntros (ck) "Hck".
    iApply "HΦ".
    eauto.
  - (* using existing clerk *)
    rewrite bool_decide_false; last first.
    { intros [=Hz]. apply Hnzero. rewrite Hz. word. }
    wp_loadField.
    iDestruct (is_slice_sz with "HfreeClerks_sl") as %Hlen.
    destruct freeClerks as [|freeClerks Hck _] using rev_ind.
    { exfalso. apply Hnzero. done. }
    rewrite app_length in Hlen. simpl in Hlen.
    rewrite big_sepL_snoc.
    iDestruct (is_slice_small_read with "HfreeClerks_sl") as "[HfreeClerks_sl HfreeClerks_close]".
    wp_apply (wp_SliceGet (V:=loc) with "[$HfreeClerks_sl]").
    { iPureIntro.
      replace (int.nat (word.sub freeClerks_sl.(Slice.sz) 1%Z)) with (int.nat freeClerks_sl.(Slice.sz) - 1) by word.
      rewrite lookup_app_r; last by word. rewrite -Hlen.
      replace (length Hck + 1 - 1 - length Hck) with 0 by lia.
      done. }
    iIntros "HfreeClerks_sl".

    wp_loadField.
    wp_apply wp_SliceTake.
    { word. }
    wp_bind (struct.storeF _ _ _ _).
    (* FIXME why do we have to apply storeField by hand here? *)
    iApply (wp_storeField with "HfreeClerks").
    { rewrite /field_ty. simpl. val_ty. }
    iIntros "!> HfreeClerks".
    iDestruct "HfreeClerks_own" as "[HfreeClerks_own Hck]".
    wp_loadField.
    iDestruct ("HfreeClerks_close" with "HfreeClerks_sl") as "HfreeClerks_sl".
    wp_apply (release_spec'' with "Hinv [$Hlocked HfreeClerks_own HfreeClerks_sl HfreeClerks]").
    { rewrite /own_ConcMemKVClerk. iModIntro. iExists _, _. iFrame.
      (* FIXME need typed slice lemma *)
      iClear "#".
      rewrite /is_slice.
      iDestruct (is_slice_take_cap _ _ _ (length Hck) with "HfreeClerks_sl") as "HfreeClerks_sl".
      { rewrite /list.untype fmap_length app_length /=. word. }
      rewrite /list.untype fmap_app take_app_alt; last first.
      { rewrite fmap_length. word. }
      replace (word.sub freeClerks_sl.(Slice.sz) 1%Z) with (length Hck : u64) by word.
      iFrame. }
    wp_pures. iApply "HΦ".
    eauto.
Qed.

Local Lemma wp_KVClerkPool__putClerk p γ ck :
  is_ConcMemKVClerk p γ -∗
  {{{ own_MemKVClerk ck γ.(coord_kv_gn) }}}
    KVClerkPool__putClerk #p #ck
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hcck !> %Φ Hck HΦ". wp_lam.
  wp_apply (wp_fork with "[Hck]").
  { iModIntro.
    iNamed "Hcck".
    wp_loadField.
    wp_apply (acquire_spec with "Hinv").
    iIntros "[Hlocked Hown]". iNamed "Hown".
    wp_loadField.
Abort.

End memkv_concurrent_clerk_proof.
