From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export common_proof memkv_coord_definitions memkv_seq_clerk_proof.

Local Open Scope nat_scope.

Section memkv_concurrent_clerk_proof.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ, !kvMapG Σ}.

Local Definition own_KVClerk (p:loc) (γ:gname) : iProp Σ :=
  ∃ (freeClerks_sl:Slice.t) (freeClerks:list loc),
  "HfreeClerks" ∷ p ↦[KVClerk :: "freeClerks"] (slice_val freeClerks_sl) ∗
  "HfreeClerks_sl" ∷ own_slice (V:=loc) freeClerks_sl ptrT (DfracOwn 1) freeClerks ∗
  "HfreeClerks_own" ∷ [∗ list] ck ∈ freeClerks, own_SeqKVClerk ck γ
.

(* FIXME: imports are screwed somewhere, [val] is shadowed the wrong way. *)
Definition is_KVClerk (p_ptr:loc) (γ:gname) : iProp Σ :=
  ∃ (coord:u64) mu (cm:loc) (γcoord:server_chan_gnames),
  "#Hmu" ∷ readonly (p_ptr ↦[KVClerk :: "mu"] mu) ∗
  "#Hcoord" ∷ readonly (p_ptr ↦[KVClerk :: "coord"] #coord) ∗
  "#Hcm" ∷ readonly (p_ptr ↦[KVClerk :: "cm"] #cm) ∗
  "#Hiscoord" ∷ is_coord_server coord (Build_memkv_coord_names γcoord γ) ∗
  "#Hinv" ∷ is_lock nroot mu (own_KVClerk p_ptr γ) ∗
  "#Hiscm" ∷ is_ConnMan cm
.

Local Lemma wp_KVClerk__getSeqClerk p γ :
  is_KVClerk p γ -∗
  {{{ True }}}
    KVClerk__getSeqClerk #p
  {{{ (ck:loc), RET #ck; own_SeqKVClerk ck γ }}}.
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
  destruct (decide (uint.nat freeClerks_sl.(Slice.sz) = 0)) as [Hzero|Hnzero].
  - (* creating new clerk *)
    rewrite bool_decide_true; last first.
    { do 2 f_equal. word. }
    wp_loadField.
    wp_apply (release_spec'' with "Hinv [-HΦ]").
    { iFrame. }
    wp_pures.
    wp_apply (wp_MakeConnMan).
    iIntros (cm2) "Hcm2".
    wp_loadField.
    wp_apply (wp_MakeSeqKVClerk with "[$Hiscoord $Hcm2]").
    iIntros (ck) "Hck".
    iApply "HΦ".
    eauto.
  - (* using existing clerk *)
    rewrite bool_decide_false; last first.
    { intros [=Hz]. apply Hnzero. rewrite Hz. word. }
    wp_loadField.
    iDestruct (own_slice_sz with "HfreeClerks_sl") as %Hlen.
    iDestruct (own_slice_wf with "HfreeClerks_sl") as %Hwf.
    destruct freeClerks as [|freeClerks Hck _] using rev_ind.
    { exfalso. apply Hnzero. done. }
    rewrite app_length in Hlen. simpl in Hlen.
    rewrite big_sepL_snoc.
    iDestruct (own_slice_small_read with "HfreeClerks_sl") as "[HfreeClerks_sl HfreeClerks_close]".
    wp_apply (wp_SliceGet (V:=loc) with "[$HfreeClerks_sl]").
    { iPureIntro.
      replace (uint.nat (word.sub freeClerks_sl.(Slice.sz) 1%Z)) with (uint.nat freeClerks_sl.(Slice.sz) - 1) by word.
      rewrite lookup_app_r; last by word. rewrite -Hlen.
      replace (length Hck + 1 - 1 - length Hck) with 0 by lia.
      done. }
    iIntros "HfreeClerks_sl".

    wp_loadField.
    wp_apply wp_SliceTake.
    { word. }
    wp_bind (struct.storeF _ _ _ _).
    wp_storeField.
    iDestruct "HfreeClerks_own" as "[HfreeClerks_own Hck]".
    wp_loadField.
    iDestruct ("HfreeClerks_close" with "HfreeClerks_sl") as "HfreeClerks_sl".
    wp_apply (release_spec'' with "Hinv [$Hlocked HfreeClerks_own HfreeClerks_sl HfreeClerks]").
    { rewrite /own_KVClerk. iModIntro. iExists _, _. iFrame.
      (* FIXME need typed slice lemma *)
      iClear "#".
      rewrite /own_slice.
      iDestruct (own_slice_take_cap _ _ _ (length Hck) with "HfreeClerks_sl") as "HfreeClerks_sl".
      { rewrite /list.untype fmap_length app_length /=. word. }
      rewrite /list.untype fmap_app take_app_length'; last first.
      { rewrite fmap_length. word. }
      replace (word.sub freeClerks_sl.(Slice.sz) 1%Z) with (length Hck : u64) by word.
      iFrame. }
    wp_pures. iApply "HΦ".
    eauto.
Qed.

Local Lemma wp_KVClerk__putSeqClerk p γ ck :
  is_KVClerk p γ -∗
  {{{ own_SeqKVClerk ck γ }}}
    KVClerk__putSeqClerk #p #ck
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
    wp_apply (wp_SliceAppend with "HfreeClerks_sl").
    iIntros (freeClerks_sl') "HfreeClerks_sl".
    wp_bind (struct.storeF _ _ _ _).
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec'' with "Hinv [$Hlocked HfreeClerks_own HfreeClerks_sl HfreeClerks Hck]").
    { rewrite /own_KVClerk. iModIntro. iExists _, _. iFrame.
      rewrite big_sepL_singleton. done. }
    done.
  }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_MakeKVClerk coord cm γ :
  is_coord_server coord γ -∗
  is_ConnMan cm -∗
  {{{ True }}}
    MakeKVClerk #coord #cm
  {{{ (p:loc), RET #p; is_KVClerk p γ.(coord_kv_gn) }}}.
Proof.
  iIntros "#Hcoord #Hcm !> %Φ _ HΦ". wp_lam.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH". iNamed "HH".
  wp_apply wp_new_free_lock.
  iIntros (mu) "Hfreelock".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_apply (wp_NewSlice (V:=loc)).
  iIntros (freeClerks_sl) "HfreeClerks_sl".
  wp_storeField.
  iMod (alloc_lock with "Hfreelock [freeClerks HfreeClerks_sl]") as "Hlock"; last first.
  { wp_pures. iApply "HΦ". rewrite /is_KVClerk.
    iExists coord, #mu, _, γ.(coord_urpc_gn). iFrame "Hcoord Hlock".
    iMod (readonly_alloc_1 with "mu") as "$".
    iMod (readonly_alloc_1 with "coord") as "$".
    iMod (readonly_alloc_1 with "cm") as "$".
    eauto with iFrame. }
  rewrite /own_KVClerk. iExists _, _. iFrame.
  rewrite big_sepL_nil. done.
Qed.

Lemma wp_KVClerk__Get (p:loc) (γ:gname) (key:u64) :
⊢ {{{ is_KVClerk p γ }}}
  <<< ∀∀ v, kvptsto γ key v >>>
    KVClerk__Get #p #key @ ∅
  <<< kvptsto γ key v >>>
  {{{ val_sl q, RET slice_val val_sl;
      own_slice_small val_sl byteT q%Qp v
  }}}.
Proof.
  iIntros "!#" (Φ) "#Hp Hatomic". wp_lam.
  wp_apply (wp_KVClerk__getSeqClerk with "Hp").
  iIntros (ck) "Hck".
  wp_apply (wp_SeqKVClerk__Get with "Hck").
  iMod "Hatomic" as (v) "[Hkv HΦ]".
  iModIntro. iExists v. iFrame "Hkv".
  iIntros "Hkv". iMod ("HΦ" with "Hkv") as "HΦ".
  iIntros "!> %val_sl %q [Hck Hsl]".
  wp_apply (wp_KVClerk__putSeqClerk with "Hp Hck").
  wp_pures. iApply "HΦ". done.
Qed.

(* Sequential spec (for when you have full ownership of the [kvptsto]) *)
Lemma wp_KVClerk__Get_seq (p:loc) (γ:gname) (key:u64) (v:list u8) :
  {{{ is_KVClerk p γ ∗ kvptsto γ key v }}}
    KVClerk__Get #p #key @ ⊤
  {{{ val_sl q, RET slice_val val_sl;
      kvptsto γ key v ∗ own_slice_small val_sl byteT q%Qp v
  }}}.
Proof.
  iIntros (Φ) "(Hclerk & Hkey) HΦ".
  iApply (wp_KVClerk__Get with "Hclerk").
  iApply fupd_mask_intro; first done. iNext.
  iIntros "Hclose". iExists _. iFrame "Hkey".
  iIntros "Hkey". iMod "Hclose" as "_". iModIntro.
  iIntros (??) "Hsl". iApply "HΦ". iFrame.
Qed.

Lemma wp_KVClerk__Put (p:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v:list u8) :
⊢ {{{ is_KVClerk p γ ∗ own_slice_small val_sl byteT DfracDiscarded v }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    KVClerk__Put #p #key (slice_val val_sl) @ ∅
  <<< kvptsto γ key v >>>
  {{{ RET #(); True }}}.
Proof.
  iIntros "!#" (Φ) "#[Hp Hsl] Hatomic". wp_lam.
  wp_apply (wp_KVClerk__getSeqClerk with "Hp").
  iIntros (ck) "Hck".
  wp_apply (wp_SeqKVClerk__Put with "[$Hck $Hsl]").
  iMod "Hatomic" as (oldv) "[Hkv HΦ]".
  iModIntro. iExists oldv. iFrame "Hkv".
  iIntros "Hkv". iMod ("HΦ" with "Hkv") as "HΦ".
  iIntros "!> Hck".
  wp_apply (wp_KVClerk__putSeqClerk with "Hp Hck").
  wp_pures. iApply "HΦ". done.
Qed.

Lemma wp_KVClerk__Put_seq (p:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v oldv:list u8) :
  {{{ is_KVClerk p γ ∗ own_slice_small val_sl byteT DfracDiscarded v ∗ kvptsto γ key oldv }}}
    KVClerk__Put #p #key (slice_val val_sl) @ ⊤
  {{{ RET #(); kvptsto γ key v }}}.
Proof.
  iIntros (Φ) "(Hclerk & Hsl & Hkey) HΦ".
  iApply (wp_KVClerk__Put with "[$Hclerk $Hsl]").
  iApply fupd_mask_intro; first done. iNext.
  iIntros "Hclose". iExists _. iFrame "Hkey".
  iIntros "Hkey". iMod "Hclose" as "_". iModIntro.
  iIntros "_". iApply "HΦ". iFrame.
Qed.

Lemma wp_KVClerk__ConditionalPut (p:loc) (γ:gname) (key:u64) (expv_sl newv_sl:Slice.t) (expv newv:list u8):
⊢ {{{ is_KVClerk p γ ∗
      own_slice_small expv_sl byteT DfracDiscarded expv ∗
      own_slice_small newv_sl byteT DfracDiscarded newv }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    KVClerk__ConditionalPut #p #key (slice_val expv_sl) (slice_val newv_sl) @ ∅
  <<< kvptsto γ key (if bool_decide (expv = oldv) then newv else oldv) >>>
  {{{ RET #(bool_decide (expv = oldv)); True }}}.
Proof.
  iIntros "!#" (Φ) "#[Hp Hsl] Hatomic". wp_lam.
  wp_apply (wp_KVClerk__getSeqClerk with "Hp").
  iIntros (ck) "Hck".
  wp_apply (wp_SeqKVClerk__ConditionalPut with "[$Hck $Hsl]").
  iMod "Hatomic" as (oldv) "[Hkv HΦ]".
  iModIntro. iExists oldv. iFrame "Hkv".
  iIntros "Hkv". iMod ("HΦ" with "Hkv") as "HΦ".
  iIntros "!> Hck".
  wp_apply (wp_KVClerk__putSeqClerk with "Hp Hck").
  wp_pures. iApply "HΦ". done.
Qed.

Lemma wp_KVClerk__Add (p:loc) γkv γ (dst : u64) :
  {{{
       is_KVClerk p γkv ∗
       is_shard_server dst γ ∗
       ⌜γ.(kv_gn) = γkv⌝
  }}}
    KVClerk__Add #p #dst
  {{{RET #(); True }}}
.
Proof.
  iIntros (Φ) "#(Hp & Hshard & %) HΦ". wp_lam. subst γkv.
  wp_apply (wp_KVClerk__getSeqClerk with "Hp").
  iIntros (ck) "Hck".
  wp_apply (wp_SeqKVClerk__Add with "[$Hck $Hshard //]").
  iIntros "Hck".
  wp_apply (wp_KVClerk__putSeqClerk with "Hp Hck").
  wp_pures. iApply "HΦ". done.
Qed.

Lemma wp_KVClerk__MGet (p:loc) (γ:gname) (keys_sl:Slice.t) (keys_vals:list (u64 * list u8)) q :
  {{{ is_KVClerk p γ ∗
      own_slice_small keys_sl uint64T q (keys_vals.*1) ∗
      [∗ list] key_val ∈ keys_vals, kvptsto γ key_val.1 key_val.2
  }}}
    KVClerk__MGet #p (slice_val keys_sl) @ ⊤
  {{{ (vals_sl:Slice.t) (val_sls:list Slice.t), RET slice_val vals_sl;
      own_slice_small keys_sl uint64T q (keys_vals.*1) ∗
      own_slice_small vals_sl (slice.T byteT) (DfracOwn 1) val_sls ∗
      [∗ list] key_val;sl ∈ keys_vals;val_sls, kvptsto γ key_val.1 key_val.2 ∗
        own_slice_small sl byteT DfracDiscarded key_val.2
  }}}.
Proof using Type*.
  iIntros (Φ) "(#Hclerk & Hkeys_sl & Hkeys) HΦ". wp_lam.
  wp_apply wp_slice_len.
  wp_apply (wp_NewSlice (V:=Slice.t)).
  iIntros (vals_sl) "Hvals_sl".
  wp_apply wp_slice_len.

  iDestruct (own_slice_small_sz with "Hkeys_sl") as %Hlen.
  rewrite fmap_length in Hlen.
  iDestruct (own_slice_to_small with "Hvals_sl") as "Hvals_sl".
  iEval (rewrite /own_slice_small /slice.own_slice_small ?untype_replicate ?replicate_length)
    in "Hkeys_sl Hvals_sl".
  iDestruct "Hkeys_sl" as "[Hkeys_sl %Hkeys_sl_len]".
  iDestruct "Hvals_sl" as "[Hvals_sl %Hvals_sl_len]".
  wp_apply (wp_Multipar (X:=(u64 * list u8))
    (λ i '(key, val),
      (keys_sl.(Slice.ptr) +ₗ[uint64T] i) ↦[uint64T]{q} #key ∗
      kvptsto γ key val ∗
      (vals_sl.(Slice.ptr) +ₗ[slice.T byteT] i) ↦[slice.T byteT] slice_val Slice.nil)%I
    (λ i kv, ∃ (val_sl:Slice.t), let '(key, val) := kv in
      (keys_sl.(Slice.ptr) +ₗ[uint64T] i) ↦[uint64T]{q} #key ∗
      kvptsto γ key val ∗
      (vals_sl.(Slice.ptr) +ₗ[slice.T byteT] i) ↦[slice.T byteT] slice_val val_sl ∗
      own_slice_small val_sl byteT DfracDiscarded val)%I
    keys_sl.(Slice.sz)
    keys_vals
    with "[] [Hkeys_sl Hkeys Hvals_sl]").
  { done. }
  {
    iIntros "!> %i %kv %Hi Hpre". destruct kv as [key val].
    iDestruct "Hpre" as "(Hkey_l & Hkey & Hval_l)".
    wp_pures.

    (* Breaking the SLiceGet (and later SliceSet) abstraction -- we only
       own that one element, not the entire slice! *)
    rewrite /SliceGet. wp_pures.
    wp_apply wp_slice_ptr. wp_pures.
    replace (uint.nat i : Z) with (uint.Z i) by word.
    wp_load.

    wp_apply (wp_KVClerk__Get_seq with "[$Hkey //]").
    iIntros (val_sl qval_sl) "(Hkey & Hval_sl)".

    rewrite /SliceSet. wp_pures.
    wp_apply wp_slice_ptr. wp_pures.
    wp_store.

    iExists _.
    iMod (own_slice_small_persist with "Hval_sl") as "$".
    eauto with iFrame. }
  { rewrite /array /list.untype !big_sepL_fmap.
    iDestruct (big_sepL2_sepL_2 with "Hkeys_sl Hvals_sl") as "Hsl".
    { rewrite Hlen replicate_length //. }
    rewrite big_sepL2_replicate_r //.
    iCombine "Hkeys Hsl" as "H". rewrite -big_sepL_sep.
    iApply (big_sepL_impl with "H").
    iIntros "!> %i %kv %Hi (Hkey & Hkey_sl & Hval_sl)".
    destruct kv as [key value].
    iFrame. }
  iIntros "H".
  wp_pures.
  iDestruct (big_sepL_exists_to_sepL2 with "H") as (xs) "H".
  iDestruct (big_sepL2_length with "H") as %Hlenxs.
  iApply ("HΦ" $! vals_sl xs). iModIntro.
  iEval (rewrite {1 2}/own_slice_small /slice.own_slice_small).
  rewrite /array /list.untype !big_sepL_fmap !fmap_length.
  iEval (rewrite [(_ ∗ ⌜length keys_vals = _ ∧ _⌝)%I]comm -!assoc).
  iSplit; first naive_solver.
  iEval (rewrite !assoc [(_ ∗ ⌜length xs = _ ∧ _⌝)%I]comm -!assoc).
  rewrite -Hlenxs Hlen. iSplit; first done.
  iEval (rewrite [(([∗ list] k↦y ∈ xs, _) ∗ _)%I]comm).
  rewrite -big_sepL2_sep_sepL_r.
  rewrite -big_sepL2_sep_sepL_l.
  iApply (big_sepL2_impl with "H").
  iIntros "!> %i %kv %val_sl %Hi1 %Hi2". destruct kv as [key val].
  iIntros "(Hkeys_sl & Hkey & Hvals_sl & Hval_sl)". iFrame.
Qed.

End memkv_concurrent_clerk_proof.
