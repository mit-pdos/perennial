From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Export paxos.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module applyAsFollowerArgs.
Section applyAsFollowerArgs.
Context `{!heapGS Σ}.

Record C :=
mkC {
  epoch : u64 ;
  nextIndex : u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le args.(nextIndex)) ++ args.(state).

Context `{!heapGS Σ}.

Definition own args_ptr args : iProp Σ :=
  ∃ state_sl,
  "#Hargs_epoch" ∷ readonly (args_ptr ↦[applyAsFollowerArgs :: "epoch"] #args.(epoch)) ∗
  "#Hargs_index" ∷ readonly (args_ptr ↦[applyAsFollowerArgs :: "nextIndex"] #args.(nextIndex)) ∗
  "#Hargs_state" ∷ readonly (args_ptr ↦[applyAsFollowerArgs :: "state"] (slice_val state_sl)) ∗
  "#Hargs_state_sl" ∷ readonly (own_slice_small state_sl byteT (DfracOwn 1) args.(state))
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    encodeApplyAsFollowerArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_pures.
  wp_loadField. wp_apply (wp_slice_len).
  iMod (readonly_load with "Hargs_state_sl") as (?) "Hstate_sl".
  iDestruct (own_slice_small_sz with "[$]") as %Hsz.
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (?) "Hptr".
  wp_pures. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hstate_sl]").
  iIntros (?) "[Hsl _]". wp_store.
  wp_load. iApply "HΦ". iFrame. iPureIntro. done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    decodeApplyAsFollowerArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ".
  wp_lam. wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures. wp_load.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH". rewrite Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?". wp_pures. wp_storeField.
  wp_store. wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hstate_sl". wp_pures. wp_storeField. wp_store.
  wp_load. wp_storeField.
  iMod (readonly_alloc_1 with "Hstate_sl") as "#Hstate_sl".
  iMod (readonly_alloc_1 with "state") as "#?".
  iMod (readonly_alloc_1 with "epoch") as "#?".
  iMod (readonly_alloc_1 with "nextIndex") as "#?".
  iApply "HΦ". iModIntro. repeat iExists _; iFrame "∗#".
Qed.

End applyAsFollowerArgs.
End applyAsFollowerArgs.

Module applyAsFollowerReply.
Section applyAsFollowerReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err: u64 ;
}.

Definition has_encoding (encoded:list u8) (reply:C) : Prop :=
  encoded = (u64_le reply.(err)).

Context `{!heapGS Σ}.

Definition own reply_ptr reply q : iProp Σ :=
  "Hreply_err" ∷ reply_ptr ↦[applyAsFollowerReply :: "err"]{q} #reply.(err)
  .

Lemma wp_Encode (reply_ptr:loc) (reply:C) q :
  {{{
        own reply_ptr reply q
  }}}
    encodeApplyAsFollowerReply #reply_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc reply⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  wp_lam. wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl". wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl".
  wp_store. wp_load.
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_Decode enc enc_sl (reply:C) :
  {{{
        ⌜has_encoding enc reply⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    decodeApplyAsFollowerReply (slice_val enc_sl)
  {{{
        reply_ptr, RET #reply_ptr; own reply_ptr reply (DfracOwn 1)
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ".
  wp_lam. wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH". rewrite Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?". wp_pures. wp_storeField.
  iApply "HΦ". iModIntro. repeat iExists _; iFrame "∗#".
Qed.

End applyAsFollowerReply.
End applyAsFollowerReply.

Module applyReply.
Section applyReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err: u64 ;
  ret: list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(err)) ++ args.(ret).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  ∃ ret_sl,
  "Hreply_epoch" ∷ args_ptr ↦[applyReply :: "err"]{q} #args.(err) ∗
  "Hreply_ret" ∷ args_ptr ↦[applyReply :: "ret"]{q} (slice_val ret_sl) ∗
  "Hreply_ret_sl" ∷ own_slice_small ret_sl byteT q args.(ret)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    encodeApplyReply #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_lam. wp_pures. wp_loadField. wp_apply (wp_slice_len).
  iDestruct (own_slice_small_sz with "[$]") as %Hsz.
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (?) "Hptr".
  wp_pures. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteBytes with "[$]").
  iIntros (?) "[Hsl _]". wp_store.
  wp_load. iApply "HΦ". iFrame. iPureIntro. done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    decodeApplyReply (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ".
  wp_lam. wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (?) "Herr". wp_pures. wp_load.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH". rewrite Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?". wp_pures. wp_store.
  wp_store. wp_load. wp_storeField.
  wp_load. wp_storeField.
  iApply "HΦ". iModIntro. repeat iExists _; iFrame "∗#".
Qed.

End applyReply.
End applyReply.

Module enterNewEpochArgs.
Section enterNewEpochArgs.
Context `{!heapGS Σ}.

Record C :=
mkC {
  epoch: u64 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  "Hargs_epoch" ∷ args_ptr ↦[enterNewEpochArgs :: "epoch"]{q} #args.(epoch)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    encodeEnterNewEpochArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  wp_lam. wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl". wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl".
  wp_store. wp_load.
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    decodeEnterNewEpochArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ".
  wp_lam. wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH". rewrite Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?". wp_pures. wp_storeField. wp_pures.
  iApply "HΦ". iModIntro. repeat iExists _; iFrame "∗#".
Qed.

End enterNewEpochArgs.
End enterNewEpochArgs.

Module enterNewEpochReply.
Section enterNewEpochReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err: u64 ;
  acceptedEpoch: u64 ;
  nextIndex: u64 ;
  state: list u8;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(err)) ++ (u64_le args.(acceptedEpoch)) ++ (u64_le args.(nextIndex))  ++ args.(state).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  ∃ state_sl,
  "Hreply_err" ∷ args_ptr ↦[enterNewEpochReply :: "err"]{q} #args.(err) ∗
  "Hreply_nextIndex" ∷ args_ptr ↦[enterNewEpochReply :: "nextIndex"]{q} #args.(nextIndex) ∗
  "Hreply_acceptedEpoch" ∷ args_ptr ↦[enterNewEpochReply :: "acceptedEpoch"]{q} #args.(acceptedEpoch) ∗
  "Hreply_ret" ∷ args_ptr ↦[enterNewEpochReply :: "state"]{q} (slice_val state_sl) ∗
  "Hreply_ret_sl" ∷ readonly (own_slice_small state_sl byteT (DfracOwn 1) args.(state))
.

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    encodeEnterNewEpochReply #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) enc
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_pures.
  wp_loadField. wp_apply (wp_slice_len).
  iMod (readonly_load with "Hreply_ret_sl") as (?) "Hstate_sl".
  iDestruct (own_slice_small_sz with "[$]") as %Hsz.
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (?) "Hptr".
  wp_pures. wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl". wp_store. wp_loadField.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hstate_sl]").
  iIntros (?) "[Hsl _]". wp_store.
  wp_load. iApply "HΦ". iFrame. iPureIntro. done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT (DfracOwn 1) enc
  }}}
    decodeEnterNewEpochReply (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args (DfracOwn 1)
  }}}.
Proof.
  iIntros (?) "[%Henc Hsl] HΦ".
  wp_lam. wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". wp_pures. wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures. wp_apply wp_ref_of_zero; first done.
  iIntros (?) "Herr". wp_pures. wp_load.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH". rewrite Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?". wp_pures. wp_store. wp_store.
  wp_load. wp_storeField.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hstate_sl". wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hstate_sl". wp_pures. wp_storeField. wp_store.
  wp_load. wp_storeField.
  iMod (readonly_alloc_1 with "Hstate_sl") as "#Hstate_sl".
  iApply "HΦ". iModIntro. repeat iExists _; iFrame "∗#".
Qed.

End enterNewEpochReply.
End enterNewEpochReply.


Module paxosState.
Section paxosState.
Record t :=
  mk {
      epoch : u64;
      acceptedEpoch : u64 ;
      nextIndex : u64 ;
      state : list u8 ;
      isLeader : bool ;
    }.

Definition encode (st:t) : list u8 :=
  u64_le st.(epoch) ++
  u64_le st.(acceptedEpoch) ++
  u64_le st.(nextIndex) ++
  u64_le (if st.(isLeader) then W64 1 else W64 0) ++
  st.(state)
.

#[global]
Instance encode_inj : Inj (=) (=) encode.
Proof.
  intros ???. destruct x, y.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  simpl in *.
  apply (f_equal le_to_u64) in H0, H1, H2.
  repeat rewrite u64_le_to_word in H0, H1, H2.
  subst. f_equal. destruct isLeader0, isLeader1; done.
Qed.

Context `{!heapGS Σ}.
Definition own_vol (s:loc) (st: paxosState.t) : iProp Σ :=
  ∃ state_sl,
  "Hepoch" ∷ s ↦[paxosState :: "epoch"] #st.(epoch) ∗
  "HaccEpoch" ∷ s ↦[paxosState :: "acceptedEpoch"] #st.(acceptedEpoch) ∗
  "HnextIndex" ∷ s ↦[paxosState :: "nextIndex"] #st.(nextIndex) ∗
  "Hstate" ∷ s ↦[paxosState :: "state"] (slice_val state_sl) ∗
  "#Hstate_sl" ∷ readonly (own_slice_small state_sl byteT (DfracOwn 1) st.(state)) ∗
  "HisLeader" ∷ s ↦[paxosState :: "isLeader"] #st.(isLeader)
.
Lemma wp_boolToU64 (b:bool) :
  {{{ True }}}
    boolToU64 #b
  {{{ RET #((if b then W64 1 else W64 0) : u64); True }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam. wp_if_destruct; by iApply "HΦ".
Qed.

Lemma wp_encode s st :
  {{{
        own_vol s st
  }}}
    encodePaxosState #s
  {{{
        sl, RET (slice_val sl);
        own_vol s st ∗
        own_slice sl byteT (DfracOwn 1) (encode st)
  }}}
.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_lam. wp_apply (wp_NewSlice).
  iIntros (?) "Hsl". wp_apply (wp_ref_to); first done.
  iIntros (?) "Hptr". wp_pures.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl". wp_store.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl". wp_store.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl". wp_store.
  wp_loadField. wp_apply wp_boolToU64. wp_load.
  wp_apply (wp_WriteInt with "[$]"). iIntros (?) "Hsl". wp_store.
  iMod (readonly_load with "Hstate_sl") as (?) "Hstate_sl2".
  wp_loadField. wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hstate_sl2]").
  iIntros (?) "[Hsl _]". wp_store. wp_load.
  iApply "HΦ".
  by iFrame.
Qed.

Lemma wp_decode sl st q :
  {{{
        own_slice_small sl byteT (DfracOwn q) (encode st)
  }}}
    decodePaxosState (slice_val sl)
  {{{
        s, RET #s; own_vol s st
  }}}
.
Proof.
  iIntros (?) "Hsl HΦ".
  wp_lam. wp_apply wp_ref_to; first done.
  iIntros (?) "He". wp_pures. wp_apply wp_ref_of_zero; first done.
  iIntros (?) "HleaderInt". wp_pures. wp_apply (wp_allocStruct); first by val_ty.
  iIntros (?) "Hs". iDestruct (struct_fields_split with "Hs") as "HH". iNamed "HH".
  wp_pures. wp_load. wp_apply (wp_ReadInt with "[$]"). iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]"). iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]"). iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]"). iIntros (?) "Hsl".
  iMod (readonly_alloc (own_slice_small s'2 byteT (DfracOwn 1) st.(state)) with "[Hsl]") as "#Hsl".
  { done. }
  wp_pures. wp_store. wp_storeField. wp_load. wp_pures. wp_storeField.
  iApply "HΦ".
  iModIntro. repeat iExists _; iFrame "∗#".
  iApply to_named. iExactEq "isLeader".
  repeat f_equal. destruct st, isLeader; simpl.
  { by rewrite bool_decide_eq_true. }
  { by rewrite bool_decide_eq_false. }
Qed.

End paxosState.
End paxosState.
