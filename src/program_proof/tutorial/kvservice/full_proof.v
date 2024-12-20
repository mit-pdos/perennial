From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import kvservice.
From Perennial.program_proof.grove_shared Require Import urpc_spec urpc_proof monotonic_pred.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof Require Import std_proof.
From iris.base_logic.lib Require Import ghost_map.
From Perennial.program_logic Require Import atomic_fupd.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(********************************************************************************)

Module putArgs.
Record t :=
  mk {
      opId: u64 ;
      key: byte_string ;
      val: byte_string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ (u64_le $ length a.(key)) ++
      a.(key) ++ a.(val)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[putArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[putArgs :: "key"] #(str args.(key)) ∗
  "Hval" ∷ a ↦[putArgs :: "val"] #(str args.(val))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodePutArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT (DfracOwn 1) enc_args
  }}}
.
Proof.
  iIntros (Φ) "Hargs HΦ".
  iNamed "Hargs".
  wp_rec.
  wp_apply wp_NewSlice.
  iIntros (sl) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (e) "He".

  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl".
  rewrite replicate_0 /=.
  wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes.
  iIntros (key_sl) "Hkey_sl".
  wp_pures.

  wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "Hkey_sl") as "%Hsz".
  wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_store.

  wp_load.
  iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl".
  wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]").
  iIntros (?) "[Hsl Hkey_sl]".
  wp_store.

  wp_loadField.
  wp_apply (wp_StringToBytes).
  iIntros (?) "Hval_sl".
  iDestruct (own_slice_to_small with "Hval_sl") as "Hval_sl".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Hval_sl]").
  iIntros (?) "[Hsl Hval_sl]".
  wp_store.

  wp_load.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold encodes.
  repeat rewrite -assoc.
  rewrite Hsz.
  repeat f_equal.
  word.
Qed.

Lemma wp_decode  sl enc_args args q :
  {{{
        "%Henc" ∷ ⌜encodes enc_args args⌝ ∗
        "Hsl" ∷ own_slice_small sl byteT q enc_args
  }}}
    decodePutArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply wp_ref_to.
  { done. }
  iIntros (e) "He".
  wp_pures.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".

  wp_pures.
  wp_load.
  rewrite Henc; clear dependent enc_args.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hsl".
  wp_pures.
  wp_storeField.
  wp_store.
  wp_load.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hsl".
  wp_pures.
  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in Hsz. word. }
  iIntros (??) "[Hkey Hval]".
  wp_pures.
  wp_apply (wp_StringFromBytes with "[$Hkey]").
  iIntros "Hkey".
  wp_storeField.
  wp_apply (wp_StringFromBytes with "[$Hval]").
  iIntros "Hval".
  wp_storeField.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End local_defs.
End putArgs.

Module conditionalPutArgs.
Record t :=
  mk {
      opId: u64 ;
      key: byte_string ;
      expectedVal: byte_string ;
      newVal: byte_string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ (u64_le $ length a.(key)) ++ a.(key) ++
      (u64_le $ length a.(expectedVal)) ++ a.(expectedVal) ++ a.(newVal)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[conditionalPutArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[conditionalPutArgs :: "key"] #(str args.(key)) ∗
  "HexpectedVal" ∷ a ↦[conditionalPutArgs :: "expectedVal"] #(str args.(expectedVal)) ∗
  "Hval" ∷ a ↦[conditionalPutArgs :: "newVal"] #(str args.(newVal))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodeConditionalPutArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT (DfracOwn 1) enc_args
  }}}
.
Proof.
  iIntros (Φ) "Hargs HΦ".
  iNamed "Hargs".
  wp_rec.
  wp_apply wp_NewSlice.
  iIntros (sl) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (e) "He".
  wp_pures.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl".
  rewrite replicate_0 /=.
  wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes.
  iIntros (key_sl) "Hkey_sl".
  wp_pures.
  wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "Hkey_sl") as "%Hsz".
  wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_store.

  wp_load.
  iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl".
  wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]").
  iIntros (?) "[Hsl Hkey_sl]".
  wp_store.

  wp_loadField.
  wp_apply (wp_StringToBytes).
  iIntros (?) "Hexpect_sl".
  iDestruct (own_slice_to_small with "Hexpect_sl") as "Hexpect_sl".
  wp_pures.

  wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "Hexpect_sl") as %?.
  wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_store.

  wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Hexpect_sl]").
  iIntros (?) "[Hsl Hexpect_sl]".
  wp_store.

  wp_loadField.
  wp_apply (wp_StringToBytes).
  iIntros (?) "Hval_sl".
  wp_load.
  iDestruct (own_slice_to_small with "Hval_sl") as "Hval_sl".
  wp_apply (wp_WriteBytes with "[$Hsl $Hval_sl]").
  iIntros (?) "[Hsl Hval_sl]".
  wp_store.

  wp_load.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold encodes.
  repeat rewrite -assoc.
  rewrite Hsz.
  repeat f_equal; word.
Qed.

Lemma wp_decode  sl enc_args args q :
  {{{
        "%Henc" ∷ ⌜encodes enc_args args⌝ ∗
        "Hsl" ∷ own_slice_small sl byteT q enc_args
  }}}
    decodeConditionalPutArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply wp_ref_to.
  { done. }
  iIntros (?) "He".
  wp_pures.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_load.
  rewrite Henc.

  wp_apply (wp_ReadInt with "Hsl").
  iIntros (?) "Hsl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_ReadInt with "Hsl").
  iIntros (?) "Hsl".
  wp_pures.

  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_ReadBytes with "[$Hsl]").
  { rewrite length_app in Hsz. word. }
  iIntros (??) "[Hkey Hsl]".
  wp_pures.
  wp_apply (wp_StringFromBytes with "[$Hkey]").
  iIntros "_".
  wp_storeField.

  wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_pures.

  wp_apply (wp_ReadBytes with "[$Hsl]").
  { repeat rewrite length_app in Hsz. word. }
  iIntros (??) "[Hexpect Hval]".
  wp_pures.

  wp_apply (wp_StringFromBytes with "[$Hexpect]").
  iIntros "_".
  wp_storeField.
  wp_apply (wp_StringFromBytes with "[$Hval]").
  iIntros "_".
  wp_storeField.
  iModIntro. iApply "HΦ".
  iFrame.
Qed.

End local_defs.
End conditionalPutArgs.

Module getArgs.
Record t :=
  mk {
      opId: u64 ;
      key: byte_string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ a.(key)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own `{!heapGS Σ} (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[getArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[getArgs :: "key"] #(str args.(key))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodeGetArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT (DfracOwn 1) enc_args
  }}}
.
Proof.
  iIntros (Φ) "Hargs HΦ".
  iNamed "Hargs".
  wp_rec.
  wp_apply wp_NewSlice.
  iIntros (?) "Hsl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (?) "He".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Hsl").
  iIntros (?) "Hsl".
  wp_store.
  wp_loadField.
  wp_apply (wp_StringToBytes).
  iIntros (?) "Hkey_sl".
  wp_load.
  iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl".
  wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]").
  iIntros (?) "[Hsl _]".
  wp_store.
  wp_load.
  iModIntro. iApply "HΦ".
  iFrame.
  iPureIntro. done.
Qed.

Lemma wp_decode  sl enc_args args q :
  {{{
        "%Henc" ∷ ⌜encodes enc_args args⌝ ∗
        "Hsl" ∷ own_slice_small sl byteT q enc_args
  }}}
    decodeGetArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (?) "He".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "HkeyBytes".
  wp_pures.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_load.
  rewrite Henc.
  wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_StringFromBytes with "[$Hsl]").
  iIntros "_".
  wp_storeField.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End local_defs.

End getArgs.

(********************************************************************************)

Section marshal_proof.
Context `{!heapGS Σ}.

(* TODO: copied this naming convention from "u64_le". What does le actually
   mean? *)
Definition bool_le (b:bool) : list u8 := if b then [W8 1] else [W8 0].

Lemma wp_EncodeBool (b:bool) :
  {{{ True }}}
    EncodeBool #b
  {{{ sl, RET (slice_val sl); own_slice sl byteT (DfracOwn 1) (bool_le b) }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_if_destruct.
  {
    wp_apply wp_NewSlice. iIntros (?) "?".
    wp_apply (wp_SliceAppend with "[$]").
    iIntros (?) "?".
    by iApply "HΦ".
  }
  {
    wp_apply wp_NewSlice. iIntros (?) "?".
    wp_apply (wp_SliceAppend with "[$]").
    iIntros (?) "?".
    by iApply "HΦ".
  }
Qed.

Lemma wp_DecodeBool sl b q :
  {{{ own_slice_small sl byteT q (bool_le b) }}}
    DecodeBool (slice_val sl)
  {{{ RET #b; True }}}
.
Proof.
  iIntros (?) "Hsl HΦ".
  wp_rec.
  unfold bool_le.
  destruct b.
  {
    wp_apply (wp_SliceGet with "[$Hsl]").
    { done. }
    iIntros "_".
    wp_pures.
    iModIntro. by iApply "HΦ".
  }
  {
    wp_apply (wp_SliceGet with "[$Hsl]").
    { done. }
    iIntros "_".
    wp_pures.
    iModIntro. by iApply "HΦ".
  }
Qed.

Lemma wp_EncodeUint64 x:
  {{{ True }}}
    EncodeUint64 #x
  {{{ sl, RET (slice_val sl); own_slice sl byteT (DfracOwn 1) (u64_le x) }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply wp_NewSlice.
  iIntros (?) "Hsl".
  wp_apply (wp_WriteInt with "Hsl").
  iIntros (?) "Hsl".
  by iApply "HΦ".
Qed.

Lemma wp_DecodeUint64 sl x q :
  {{{ own_slice_small sl byteT q (u64_le x) }}}
    DecodeUint64 (slice_val sl)
  {{{ RET #x; True }}}
.
Proof.
  iIntros (Φ) "Hsl HΦ".
  wp_rec.
  wp_apply (wp_ReadInt with "Hsl").
  iIntros (?) "Hsl".
  wp_pures.
  by iApply "HΦ".
Qed.

End marshal_proof.

Section escrow_library.

Context `{!invGS Σ}.

Definition reqN := nroot .@ "req".

Record erpc_names :=
  {
    req_gn : gname ;
    reply_gn : gname ;
  }.

Implicit Types γ:erpc_names.

Class erpcG Σ := {
    #[global] receiptG :: ghost_mapG Σ u64 byte_string ;
    #[global] tokenG :: ghost_mapG Σ u64 unit ;
    #[global] clientTokenG :: inG Σ dfracR ;
}.

Context `{!erpcG Σ}.

Definition own_unexecuted_token γ (opId:u64) : iProp Σ :=
  opId ↪[γ.(req_gn)] ().

Definition is_executed_witness γ (opId:u64) : iProp Σ :=
  opId ↪[γ.(req_gn)]□ ().

Definition is_request_receipt γ (opId:u64) (r:byte_string) : iProp Σ :=
  opId ↪[γ.(reply_gn)]□ r.

Definition own_client_token γcl : iProp Σ :=
  own γcl (DfracOwn 1).

Definition is_request_inv γ γcl (opId:u64) (pre:iProp Σ) (post:byte_string → iProp Σ) : iProp Σ :=
  inv reqN (own_unexecuted_token γ opId ∗
            pre ∨
            is_executed_witness γ opId ∗
              (∃ r, is_request_receipt γ opId r ∗
                    (post r ∨ own_client_token γcl))).

Definition own_erpc_server γ (nextFreshId:u64) (lastReplies:gmap u64 byte_string) : iProp Σ :=
  ∃ (usedIds:gset u64),
  "Htoks" ∷ ghost_map_auth γ.(req_gn) 1 (gset_to_gmap () usedIds) ∗
  "Hreplies" ∷ ghost_map_auth γ.(reply_gn) 1 lastReplies ∗
  "#Hwits" ∷ ([∗ map] opId ↦ r ∈ lastReplies, is_executed_witness γ opId ∗ is_request_receipt γ opId r) ∗
  "%Htoks" ∷ ⌜ set_Forall (λ id, uint.nat id < uint.nat nextFreshId) usedIds ⌝
.

Lemma alloc_erpc_server :
  ⊢ |==> ∃ γ, own_erpc_server γ 0 ∅.
Proof.
  iMod (ghost_map_alloc_empty (V:=())) as (γreq) "Htoks".
  iMod (ghost_map_alloc_empty (V:=byte_string)) as (γreply) "Hreplies".
  iModIntro.
  iExists {| req_gn := _ ; reply_gn := _ |}.
  iExists ∅.
  iFrame "∗#".
  iSplit.
  { by iApply big_sepM_empty. }
  iPureIntro.
  apply set_Forall_empty.
Qed.

Lemma server_fresh_id_step γ nextFreshId lastReplies :
  uint.nat (word.add nextFreshId 1) = uint.nat nextFreshId + 1 →
  own_erpc_server γ nextFreshId lastReplies ==∗
  own_erpc_server γ (word.add nextFreshId 1) lastReplies ∗
  own_unexecuted_token γ nextFreshId
.
Proof.
  intros Hoverflow.
  iNamed 1.
  iMod (ghost_map_insert with "Htoks") as "[Htoks $]".
  {
    apply lookup_gset_to_gmap_None.
    intros Hin.
    specialize (Htoks nextFreshId Hin).
    word.
  }
  rewrite -gset_to_gmap_union_singleton.
  repeat iExists _; iFrame "∗#".
  iPureIntro.
  apply set_Forall_union.
  {
    apply set_Forall_singleton.
    word.
  }
  {
    eapply set_Forall_impl; first done.
    intros.
    word.
  }
Qed.

Lemma client_allocate_step opId γ pre post :
  pre -∗
  own_unexecuted_token γ opId ={⊤}=∗
  ∃ γcl,
    is_request_inv γ γcl opId pre post ∗
    own_client_token γcl
.
Proof.
  iIntros "Hpre Hunexec".
  iMod (own_alloc (DfracOwn 1)) as (γcl) "Htok".
  { done. }
  iExists γcl.
  iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iLeft.
  iFrame.
Qed.

Lemma server_duplicate_request_step opId r γ (lastReplies:gmap u64 byte_string) nextFreshId:
  lastReplies !! opId = Some r →
  own_erpc_server γ nextFreshId lastReplies -∗
  is_executed_witness γ opId ∗
  is_request_receipt γ opId r.
Proof.
  intros Hlookup.
  iNamed 1.
  by iDestruct (big_sepM_lookup_acc with "Hwits") as "[$ HH]".
Qed.

Lemma server_execute_step opId γ γcl pre post (lastReplies:gmap u64 byte_string) nextFreshId:
  lastReplies !! opId = None →
  £ 1 -∗
  is_request_inv γ γcl opId pre post -∗
  own_erpc_server γ nextFreshId lastReplies ={⊤,⊤∖↑reqN}=∗
  pre ∗
  (∀ r, post r ={⊤∖↑reqN,⊤}=∗
        own_erpc_server γ nextFreshId (<[opId := r]> lastReplies) ∗
        is_executed_witness γ opId ∗
        is_request_receipt γ opId r)
.
Proof.
  intros.
  iIntros "Hlc #HreqInv Hsrv".
  iInv "HreqInv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hsrv".
  iDestruct "Hown" as "[Hpre | [_ Hbad]]".
  2:{
    iDestruct "Hbad" as (?) "[Hbad _]".
    iDestruct (ghost_map_lookup with "Hreplies Hbad") as %Hbad.
    exfalso.
    by rewrite Hbad in H.
  }
  iDestruct "Hpre" as "[Htok Hpre]".
  iMod (ghost_map_elem_persist with "Htok") as "#Hexec".
  iModIntro.
  iFrame "Hpre".
  iIntros (?) "Hpost".
  iMod (ghost_map_insert_persist opId r with "Hreplies") as "[Hreplies #Hreceipt]".
  { done. }
  iMod ("Hclose" with "[-Hreplies Htoks]").
  {
    iRight. iNext.
    iFrame "#".
    iLeft. iFrame.
  }
  iModIntro.
  iFrame "∗#".
  repeat iExists _.
  iFrame "∗#%".
  rewrite big_sepM_insert; last done.
  iFrame "#".
Qed.

Lemma client_claim_step opId γ γcl pre post ret:
  £ 1 -∗
  is_request_inv γ γcl opId pre post -∗
  is_executed_witness γ opId -∗
  is_request_receipt γ opId ret -∗
  own_client_token γcl ={⊤}=∗
  post ret.
Proof.
  iIntros "Hlc #HreqInv #Hexec #Hrec Htok".
  iInv "HreqInv" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iDestruct "Hown" as "[[Hbad _] | [_ Hpost]]".
  {
    iDestruct (ghost_map_elem_valid_2 with "Hbad Hexec") as %[Hbad _].
    by exfalso.
  }
  iDestruct "Hpost" as (?) "[Hrec2 [Hpost|Hbad]]".
  2:{
    iDestruct (own_valid_2 with "Hbad Htok") as %Hbad.
    by exfalso.
  }
  iDestruct (ghost_map_elem_agree with "Hrec Hrec2") as %?; subst.
  iMod ("Hclose" with "[-Hpost]").
  {
    iNext.
    iRight.
    iFrame "#".
    iRight; iFrame.
  }
  iModIntro.
  iFrame.
Qed.

End escrow_library.

Section ghost_proof.

Record kvservice_names :=
  {
    erpc_gn : erpc_names ;
    kv_gn : gname ;
  }.

Class kvserviceG Σ :=
  {
    #[global] erpc_inG :: erpcG Σ ;
    #[global] kvs_inG :: ghost_mapG Σ byte_string byte_string ;
  }.

End ghost_proof.

Section rpc_definitions.
(* NOTE: "global" context because RPC specs are known by multiple machines. *)
Context `{!gooseGlobalGS Σ}.
Context `{!kvserviceG Σ}.

Context (γ:kvservice_names).

Definition getFreshNum_core_pre : iProp Σ :=
  True.

Definition getFreshNum_core_post : u64 → iProp Σ :=
  λ opId, own_unexecuted_token γ.(erpc_gn) opId.

Definition put_core_pre (args : putArgs.t) : iProp Σ :=
  ∃ γcl Q, is_request_inv γ.(erpc_gn) γcl args.(putArgs.opId)
    (|={⊤∖↑reqN,∅}=> ∃ oldv, args.(putArgs.key) ↪[γ.(kv_gn)] oldv ∗
                            (args.(putArgs.key) ↪[γ.(kv_gn)] args.(putArgs.val) ={∅,⊤∖↑reqN}=∗
                             Q))%I
    (λ _, Q).

Definition put_core_post (args : putArgs.t) : iProp Σ :=
  ∃ r, is_executed_witness γ.(erpc_gn) args.(putArgs.opId) ∗
       is_request_receipt γ.(erpc_gn) args.(putArgs.opId) r.

Definition conditionalPut_core_pre (args:conditionalPutArgs.t) : iProp Σ :=
  ∃ γcl Q, is_request_inv γ.(erpc_gn) γcl args.(conditionalPutArgs.opId)
    (|={⊤∖↑reqN,∅}=> ∃ oldv, args.(conditionalPutArgs.key) ↪[γ.(kv_gn)] oldv ∗
                (args.(conditionalPutArgs.key) ↪[γ.(kv_gn)]
                (if bool_decide (oldv = args.(conditionalPutArgs.expectedVal)) then
                  args.(conditionalPutArgs.newVal)
                else oldv) ={∅,⊤∖↑reqN}=∗
                 (Q (bool_decide (oldv = args.(conditionalPutArgs.expectedVal))))))
    (λ r, if decide (r = "ok"%go) then Q true else Q false)
.

Definition conditionalPut_core_post (args:conditionalPutArgs.t) r : iProp Σ :=
  is_executed_witness γ.(erpc_gn) args.(conditionalPutArgs.opId) ∗
  is_request_receipt γ.(erpc_gn) args.(conditionalPutArgs.opId) r.

Definition get_core_pre (args:getArgs.t) : iProp Σ :=
  ∃ γcl Q, is_request_inv γ.(erpc_gn) γcl args.(getArgs.opId)
    (|={⊤∖↑reqN,∅}=> ∃ v, args.(getArgs.key) ↪[γ.(kv_gn)] v ∗
                (args.(getArgs.key) ↪[γ.(kv_gn)] v ={∅,⊤∖↑reqN}=∗
                (Q v)))
    Q.

Definition get_core_post (args:getArgs.t) r : iProp Σ :=
  is_executed_witness γ.(erpc_gn) args.(getArgs.opId) ∗
  is_request_receipt γ.(erpc_gn) args.(getArgs.opId) r.

End rpc_definitions.

Module server.
Record t :=
  mk {
      nextFreshId : u64 ;
      lastReplies : gmap u64 byte_string ;
      kvs : gmap byte_string byte_string ;
    }.

Global Instance etaServer : Settable _ :=
  settable! (mk) <nextFreshId; lastReplies; kvs>.

Definition gauge_eq : relation (gmap byte_string byte_string) :=
  λ m1 m2, ∀ k, default ""%go (m1 !! k) = default ""%go (m2 !! k).

Global Instance gauge_eq_Equivalence: Equivalence (gauge_eq).
Proof.
  repeat constructor.
  - intros ????k. symmetry. apply H.
  - intros ??????k. etrans.
    { apply H. }
    { apply H0. }
Qed.

Global Instance gauge_proper_insert k v :
  Proper (gauge_eq ==> gauge_eq) (insert k v).
Proof. intros ????. destruct (decide (k = k0)).
       - subst. do 2 rewrite lookup_insert. done.
       - do 2 (rewrite lookup_insert_ne; last done). done.
Qed.

Global Instance gauge_proper_default_lookup (k:byte_string) :
  Proper (gauge_eq ==> eq) (λ m, default ""%go (lookup k m)).
Proof. intros ???. apply H. Qed.

Section local_defns.
Context `{!heapGS Σ}.
Definition own_mem (s:loc) (st:t) : iProp Σ :=
  ∃ (lastReplies_loc kvs_loc:loc) (kvs_phys:gmap byte_string byte_string),
  "HnextFreshId" ∷ s ↦[Server :: "nextFreshId"] #st.(nextFreshId) ∗
  "HlastReplies" ∷ s ↦[Server :: "lastReplies"] #lastReplies_loc ∗
  "Hkvs" ∷ s ↦[Server :: "kvs"] #kvs_loc ∗
  "HlastRepliesM" ∷ own_map lastReplies_loc (DfracOwn 1) st.(lastReplies) ∗
  "HkvsM" ∷ own_map kvs_loc (DfracOwn 1) kvs_phys ∗
  "%Hrel_phys" ∷ ⌜ gauge_eq kvs_phys st.(kvs) ⌝
.

Context `{!kvserviceG Σ}.
Definition own_ghost γ (st:t) : iProp Σ :=
  ∃ kvs_ghost,
  "Herpc" ∷ own_erpc_server γ.(erpc_gn) st.(nextFreshId) st.(lastReplies) ∗
  "Hkvs" ∷ ghost_map_auth γ.(kv_gn) 1 kvs_ghost ∗
  "%Hrel_ghost" ∷ ⌜ gauge_eq kvs_ghost st.(kvs) ⌝
.

Definition own s γ : iProp Σ :=
  ∃ st,
  ("Hghost" ∷ own_ghost γ st) ∗
  own_mem s st
.
End local_defns.

End server.

Section rpc_server_proofs.
Context `{!heapGS Σ}.
Context `{!kvserviceG Σ}.

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ s ↦[Server :: "mu"]□ mu ∗
  "#HmuInv" ∷ is_lock nroot mu (server.own s γ)
.

Lemma ghost_getFreshNum γ st :
  uint.nat (word.add st.(server.nextFreshId) 1) = uint.nat st.(server.nextFreshId) + 1 →
  server.own_ghost γ st ==∗
  server.own_ghost γ (st <|(server.nextFreshId) := word.add st.(server.nextFreshId) 1|>) ∗
  getFreshNum_core_post γ st.(server.nextFreshId)
.
Proof.
  intros Hoverflow.
  iNamed 1.
  iMod (server_fresh_id_step with "Herpc") as "[Herpc Htok]".
  { done. }
  iFrame. done.
Qed.

Lemma wp_Server__getFreshNum (s:loc) γ :
  {{{
        "#Hsrv" ∷ is_Server s γ ∗
        "Hpre" ∷ getFreshNum_core_pre
  }}}
    Server__getFreshNum #s
  {{{ (n:u64), RET #n; getFreshNum_core_post γ n }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  repeat iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (wp_SumAssumeNoOverflow).
  iIntros (Hoverflow).
  wp_storeField.
  wp_loadField.
  iMod (ghost_getFreshNum with "Hghost") as "[Hghost Hspec]".
  { word. }
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _.
    iFrame.
    repeat iExists _.
    iFrame "∗%".
  }
  wp_pures.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma ghost_put_dup γ st r args :
  st.(server.lastReplies) !! args.(putArgs.opId) = Some r →
  put_core_pre γ args -∗
  server.own_ghost γ st -∗
  server.own_ghost γ st ∗
  put_core_post γ args.
Proof.
  intros.
  iIntros "Hspec". iNamed 1.
  iDestruct (server_duplicate_request_step with "Herpc") as "#Hrec".
  { done. }
  iFrame "∗#%".
Qed.

Lemma ghost_put γ st args :
  st.(server.lastReplies) !! args.(putArgs.opId) = None →
  £ 1 -∗
  put_core_pre γ args -∗
  server.own_ghost γ st ={⊤}=∗
  server.own_ghost γ
        (st <|server.lastReplies := <[args.(putArgs.opId) := ""%go]> st.(server.lastReplies)|>
            <|server.kvs := <[args.(putArgs.key) := args.(putArgs.val)]> st.(server.kvs)|>) ∗
  put_core_post γ args.
Proof.
  intros.
  iIntros "Hlc Hspec". iNamed 1.
  iDestruct "Hspec" as (??) "#Hinv".
  iMod (server_execute_step with "Hlc Hinv Herpc") as "[Hau Hclose]".
  { done. }
  iMod "Hau" as (?) "[Hptsto Hau]".
  iMod (ghost_map_update with "Hkvs Hptsto") as "[Hkvs Hptsto]".
  iMod ("Hau" with "Hptsto") as "HQ".
  iMod ("Hclose" with "HQ") as "[Herpc #Hwit]".
  iModIntro.
  iFrame "∗#%".
  iPureIntro. simpl. by f_equiv.
Qed.

Lemma wp_Server__put (s:loc) γ args_ptr (args:putArgs.t) :
  {{{
        "#Hsrv" ∷ is_Server s γ ∗
        "Hspec" ∷ put_core_pre γ args ∗
        "Hargs" ∷ putArgs.own args_ptr args
  }}}
  Server__put #s #args_ptr
  {{{
        RET #(); put_core_post γ args
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  repeat iNamed "Hown".
  wp_pures.
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HlastRepliesM").
  iIntros (??) "[%HlastReply HlastRepliesM]".
  wp_pures.
  wp_if_destruct.
  { (* case: this is a duplicate request *)
    wp_loadField.
    apply map_get_true in HlastReply.
    iDestruct (ghost_put_dup with "Hspec Hghost") as "[Hghost Hspec]".
    { done. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _; iFrame "Hghost".
      repeat iExists _; iFrame "∗%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "Hspec".
  }
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsM").
  { done. }
  iIntros "HkvsM".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapInsert with "HlastRepliesM").
  { done. }
  iIntros "HlastRepliesM".
  wp_pure_credit "Hlc".
  wp_loadField.
  iMod (ghost_put with "Hlc Hspec Hghost") as "[Hghost Hspec]".
  { apply map_get_false in HlastReply as [? _]. done. }
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _; iFrame "Hghost".
    repeat iExists _; iFrame "∗%".
    iPureIntro. simpl. unfold typed_map.map_insert. by f_equiv.
  }
  wp_pures.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma ghost_conditionalPut_dup γ st r args :
  st.(server.lastReplies) !! args.(conditionalPutArgs.opId) = Some r →
  conditionalPut_core_pre γ args -∗
  server.own_ghost γ st -∗
  server.own_ghost γ st ∗
  conditionalPut_core_post γ args r.
Proof.
  intros.
  iIntros "Hspec". iNamed 1.
  iDestruct (server_duplicate_request_step with "Herpc") as "#Hrec".
  { done. }
  eauto with iFrame.
Qed.

Local Definition cond_put_ok st args :=
  (st
     <|server.lastReplies :=
        <[args.(conditionalPutArgs.opId) := "ok"%go]> st.(server.lastReplies)|>
     <|server.kvs :=
        <[args.(conditionalPutArgs.key) := args.(conditionalPutArgs.newVal)]> st.(server.kvs)|>)
.

Local Definition cond_put_not_ok st args :=
  (st <|server.lastReplies := <[args.(conditionalPutArgs.opId) := ""%go]>
                                st.(server.lastReplies)|>)
.

Lemma ghost_conditionalPut_ok γ st args :
  st.(server.lastReplies) !! args.(conditionalPutArgs.opId) = None →
  default ""%go (st.(server.kvs) !! args.(conditionalPutArgs.key)) = args.(conditionalPutArgs.expectedVal) →
  £ 1 -∗
  conditionalPut_core_pre γ args -∗
  server.own_ghost γ st ={⊤}=∗
  server.own_ghost γ (cond_put_ok st args) ∗
  conditionalPut_core_post γ args "ok".
Proof.
  intros.
  iIntros "Hlc Hspec". iNamed 1.
  iDestruct "Hspec" as (??) "#Hinv".
  iMod (server_execute_step with "Hlc Hinv Herpc") as "[Hau Hclose]".
  { done. }
  iMod "Hau" as (?) "[Hptsto Hau]".
  iDestruct (ghost_map_lookup with "Hkvs Hptsto") as %?.
  iMod (ghost_map_update with "Hkvs Hptsto") as "[Hkvs Hptsto]".
  iMod ("Hau" with "Hptsto") as "HQ".
  rewrite bool_decide_true.
  2:{
    rewrite -H0.
    setoid_rewrite server.gauge_proper_default_lookup; last done.
    by rewrite H1.
  }

  iMod ("Hclose" $! "ok"%go with "HQ") as "[Herpc #Hwit]".
  iModIntro.
  iFrame "∗#%". iPureIntro. simpl. by f_equiv.
Qed.

Lemma ghost_conditionalPut_not_ok γ st args :
  st.(server.lastReplies) !! args.(conditionalPutArgs.opId) = None →
  default ""%go (st.(server.kvs) !! args.(conditionalPutArgs.key)) ≠ args.(conditionalPutArgs.expectedVal) →
  £ 1 -∗
  conditionalPut_core_pre γ args -∗
  server.own_ghost γ st ={⊤}=∗
  server.own_ghost γ (cond_put_not_ok st args) ∗
  conditionalPut_core_post γ args ""%go.
Proof.
  intros.
  iIntros "Hlc Hspec". iNamed 1.
  iDestruct "Hspec" as (??) "#Hinv".
  iMod (server_execute_step with "Hlc Hinv Herpc") as "[Hau Hclose]".
  { done. }
  iMod "Hau" as (?) "[Hptsto Hau]".
  iDestruct (ghost_map_lookup with "Hkvs Hptsto") as %?.
  rewrite bool_decide_false.
  2:{
    intros Heq. apply H0.
    subst. setoid_rewrite <- (server.gauge_proper_default_lookup _ _ _ Hrel_ghost).
    by rewrite H1.
  }
  iMod ("Hau" with "Hptsto") as "HQ".
  iMod ("Hclose" $! ""%go with "HQ") as "[Herpc #Hwit]".
  iModIntro.
  iFrame "∗#%" .
Qed.

Lemma wp_Server__conditionalPut γ (s:loc) args_ptr (args:conditionalPutArgs.t) :
  {{{
        "#Hsrv" ∷ is_Server s γ ∗
        "Hspec" ∷ conditionalPut_core_pre γ args ∗
        "Hargs" ∷ conditionalPutArgs.own args_ptr args
  }}}
    Server__conditionalPut #s #args_ptr
  {{{ r, RET #(str r); conditionalPut_core_post γ args r }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  repeat iNamed "Hown".
  wp_pures.
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HlastRepliesM").
  iIntros (??) "[%HlastReply HlastRepliesM]".
  wp_pures.
  wp_if_destruct.
  { (* case: this is a duplicate request *)
    wp_loadField.
    iDestruct (ghost_conditionalPut_dup with "Hspec Hghost") as "[Hghost Hspec]".
    { by apply map_get_true in HlastReply. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _; iFrame "Hghost".
      repeat iExists _; iFrame "∗%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "Hspec".
  }
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (ret2_ptr) "Hret".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsM").
  iIntros (??) "[%Hlookup HkvsM]".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  { (* case: the old value matches the expected value *)
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "HkvsM").
    { done. }
    iIntros "HkvsM".
    (* FIXME: delete typed_map.map_insert *)
    rewrite /typed_map.map_insert.
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlastRepliesM").
    { done. }
    iIntros "HlastRepliesM".
    wp_pure_credit "Hlc".
    wp_loadField.

    iMod (ghost_conditionalPut_ok with "Hlc Hspec Hghost") as "[Hghost Hspec]".
    { apply map_get_false in HlastReply as [? _]. done. }
    { apply (f_equal fst) in Hlookup. rewrite /map_get /= in Hlookup.
      rewrite -Hlookup.
      by apply server.gauge_proper_default_lookup. }
    (* simplify by unfolding some of the cond_put stuff *)

    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec Hret]").
    {
      iFrame "∗#". iNext.
      repeat iExists _; iFrame "Hghost".
      repeat iExists _; iFrame "∗%".
      iPureIntro.
      rewrite /cond_put_ok /=.
      by f_equiv.
    }
    wp_pures.
    wp_load.
    iModIntro.
    iApply "HΦ".
    iApply "Hspec".
  }

  wp_pures.
  wp_load.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapInsert with "HlastRepliesM").
  { done. }
  iIntros "HlastRepliesM".
  wp_pure_credit "Hlc".
  wp_loadField.

  iMod (ghost_conditionalPut_not_ok with "Hlc Hspec Hghost") as "[Hghost Hspec]".
  { apply map_get_false in HlastReply as [? _]. done. }
  { intros Heq.
    apply (f_equal fst) in Hlookup.
    rewrite /map_get /= in Hlookup.
    subst. apply Heqb0.
    repeat f_equal. rewrite -Heq.
    by apply server.gauge_proper_default_lookup. }
  (* simplify by unfolding some of the cond_put stuff *)

  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec Hret]").
  {
    iFrame "∗#". iNext.
    repeat iExists _; iFrame "Hghost".
    repeat iExists _; iFrame "∗%".
  }
  wp_pures.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma ghost_get_dup γ st r args :
  st.(server.lastReplies) !! args.(getArgs.opId) = Some r →
  get_core_pre γ args -∗
  server.own_ghost γ st -∗
  server.own_ghost γ st ∗
  get_core_post γ args r.
Proof.
  intros.
  iIntros "Hspec". iNamed 1.
  iDestruct (server_duplicate_request_step with "Herpc") as "#Hrec".
  { done. }
  iFrame "∗#%".
Qed.

Lemma ghost_get γ st args :
  st.(server.lastReplies) !! args.(getArgs.opId) = None →
  £ 1 -∗
  get_core_pre γ args -∗
  server.own_ghost γ st ={⊤}=∗
  server.own_ghost γ
        (st <|server.lastReplies :=
        <[args.(getArgs.opId) := (default ""%go (st.(server.kvs) !! args.(getArgs.key)))]>
          st.(server.lastReplies)|>) ∗
  get_core_post γ args (default ""%go (st.(server.kvs) !! args.(getArgs.key))).
Proof.
  intros.
  iIntros "Hlc Hspec". iNamed 1.
  iDestruct "Hspec" as (??) "#Hinv".
  iMod (server_execute_step with "Hlc Hinv Herpc") as "[Hau Hclose]".
  { done. }
  iMod "Hau" as (?) "[Hptsto Hau]".
  iDestruct (ghost_map_lookup with "Hkvs Hptsto") as %Hlookup.
  iMod ("Hau" with "Hptsto") as "HQ".
  iMod ("Hclose" with "HQ") as "[Herpc #Hwit]".
  iModIntro.
  erewrite <- (server.gauge_proper_default_lookup _ _ st.(server.kvs) Hrel_ghost).
  rewrite Hlookup /=.
  iFrame "∗#%".
Qed.

Lemma wp_Server__get (s:loc) γ args_ptr (args:getArgs.t) :
  {{{
        "#Hsrv" ∷ is_Server s γ ∗
        "Hspec" ∷ get_core_pre γ args ∗
        "Hargs" ∷ getArgs.own args_ptr args
  }}}
    Server__get #s #args_ptr
  {{{
        r, RET #(str r); get_core_post γ args r
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  repeat iNamed "Hown".
  wp_pures.
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HlastRepliesM").
  iIntros (??) "[%HlastReply HlastRepliesM]".
  wp_pures.
  wp_if_destruct.
  { (* case: this is a duplicate request *)
    wp_loadField.
    iDestruct (ghost_get_dup with "Hspec Hghost") as "[Hghost Hspec]".
    { by apply map_get_true in HlastReply. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _; iFrame "Hghost".
      repeat iExists _; iFrame "∗%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "Hspec".
  }
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsM").
  iIntros (?? )"[%Hlookup HkvsM]".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapInsert with "HlastRepliesM").
  { done. }
  iIntros "HlastRepliesM".
  wp_pure_credit "Hlc".
  wp_loadField.
  iMod (ghost_get with "Hlc Hspec Hghost") as "[Hghost Hspec]".
  { apply map_get_false in HlastReply as [? _]. done. }
  apply (f_equal fst) in Hlookup.
  simpl in *.
  subst.
  (* FIXME: better map_get *)
  erewrite <- (server.gauge_proper_default_lookup _ _ st.(server.kvs) Hrel_phys).
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _; iFrame "Hghost".
    repeat iExists _; iFrame "∗%".
  }
  wp_pures.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma ghost_make γkv kvs :
  server.gauge_eq kvs ∅ →
  ghost_map_auth γkv 1 kvs ==∗
  ∃ γrpc, server.own_ghost {| erpc_gn := γrpc ; kv_gn := γkv |} (server.mk 0 ∅ ∅)
.
Proof.
  intros.
  iIntros "Hkvs".
  iMod alloc_erpc_server as (γerpc) "Herpc".
  iModIntro.
  repeat iExists _; iFrame.
  iPureIntro.
  done.
Qed.

(* Technically, the points-tos will have to be allocated a level above this. *)
Lemma wp_MakeServer γkv kvs :
  {{{
        "%Hkvs_empty" ∷ ⌜ server.gauge_eq kvs ∅ ⌝ ∗
        "Hauth" ∷ ghost_map_auth γkv 1 kvs
  }}}
    MakeServer #()
  {{{
        (s:loc) γrpc, RET #s; is_Server s {| erpc_gn := γrpc ; kv_gn := γkv|}
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.
  wp_apply (wp_NewMap byte_string).
  iIntros (kvs_loc) "HkvsM".
  wp_storeField.
  wp_apply (wp_NewMap u64).
  iIntros (lastReplies_loc) "HlastRepliesM".
  wp_storeField.
  iMod (ghost_make with "Hauth") as (?) "Hghost".
  { done. }
  iApply "HΦ".
  iMod (struct_field_pointsto_persist with "mu") as "#Hmu".
  iExists _; iFrame "#".
  iMod (alloc_lock with "HmuInv [-]") as "$"; last done.
  iNext.
  repeat iExists _; iFrame "Hghost".
  repeat iExists _; iFrame.
  iPureIntro. reflexivity.
Qed.

End rpc_server_proofs.

Section encoded_rpc_definitions.
(* This section is boilerplate. *)
Context `{!gooseGlobalGS Σ}.
Context `{!urpcregG Σ}.
Context `{!kvserviceG Σ}.

Definition getFreshNum_spec γ :=
  {|
    spec_ty := () ;
    spec_Pre := (λ _ _, getFreshNum_core_pre) ;
    spec_Post := (λ _ _ enc_reply, ∃ reply, ⌜enc_reply = u64_le reply⌝ ∗ getFreshNum_core_post γ reply)%I ;
  |}.

Program Definition put_spec γ :=
  {|
    spec_ty := putArgs.t ;
    spec_Pre := (λ args enc_args, ⌜ putArgs.encodes enc_args args ⌝ ∗ put_core_pre γ args)%I;
    spec_Post := (λ args enc_args _, put_core_post γ args)%I;
  |}.

Program Definition conditionalPut_spec γ :=
  {|
    spec_ty := conditionalPutArgs.t ;
    spec_Pre := (λ args enc_args, ⌜ conditionalPutArgs.encodes enc_args args ⌝ ∗
                                       conditionalPut_core_pre γ args)%I;
    spec_Post := (λ args enc_args enc_reply,
                     conditionalPut_core_post γ args enc_reply)%I;
  |}.

Program Definition get_spec γ :=
  {|
    spec_ty := getArgs.t ;
    spec_Pre := (λ args enc_args, ⌜ getArgs.encodes enc_args args ⌝ ∗
                                       get_core_pre γ args)%I;
    spec_Post := (λ args enc_args enc_reply,
                     get_core_post γ args enc_reply)%I;
  |}.

Definition is_kvserver_host host γ : iProp Σ :=
  ∃ γrpc,
  "#H0" ∷ is_urpc_spec γrpc host (W64 0) (getFreshNum_spec γ) ∗
  "#H1" ∷ is_urpc_spec γrpc host (W64 1) (put_spec γ) ∗
  "#H2" ∷ is_urpc_spec γrpc host (W64 2) (conditionalPut_spec γ) ∗
  "#H3" ∷ is_urpc_spec γrpc host (W64 3) (get_spec γ) ∗
  "#Hdom" ∷ is_urpc_dom γrpc {[ W64 0; W64 1; W64 2; W64 3 ]}
  .

End encoded_rpc_definitions.

Section start_server_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.
Context `{!kvserviceG Σ}.

Lemma wp_Server__Start (s:loc) (host:u64) γ :
  {{{
        "#Hsrv" ∷ is_Server s γ ∗
        "#Hhost" ∷ is_kvserver_host host γ
  }}}
    Server__Start #s #host
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* begin symbolic execution *)
  wp_rec.
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert u64 with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  iNamed "Hhost".
  wp_apply (wp_StartServer with "[$Hr]").
  { set_solver. }
  { (* Here, we show that the functions being passed in Go inside `handlers`
       satisfy the spec they should. *)
    (* First, show that the functions passed in are ALL the RPCs this host is
       suppose to provide. *)
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    { iExactEq "Hdom". f_equal. set_solver. }

    (* Now show the RPC specs, one at a time *)
    iApply (big_sepM_insert_2 with "").
    { (* get *)
      iExists _; iFrame "#".
      clear Φ.
      iIntros "%*%* !# (Hreq_sl & Hrep_sl & Hpre) HΦ".
      iDestruct "Hpre" as (?) "[% Hpre]".
      wp_pures.
      wp_apply (getArgs.wp_decode with "[$Hreq_sl //]").
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__get with "[$]").
      iIntros (?) "HΨ".
      wp_pures. wp_apply wp_StringToBytes.
      iIntros (ret_sl) "Hret_sl".
      iDestruct (own_slice_to_small with "Hret_sl") as "Hret_sl".
      wp_store.
      iModIntro. iApply "HΦ".
      by iFrame.
    }
    iApply (big_sepM_insert_2 with "").
    { (* conditionalPut *)
      iExists _; iFrame "#".
      clear Φ.
      iIntros "%*%* !# (Hreq_sl & Hrep_sl & Hpre) HΦ".
      iDestruct "Hpre" as (?) "[% Hpre]".
      wp_pures.
      wp_apply (conditionalPutArgs.wp_decode with "[$Hreq_sl //]").
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__conditionalPut with "[$]").
      iIntros (?) "HΨ".
      wp_pures. wp_apply wp_StringToBytes.
      iIntros (ret_sl) "Hret_sl".
      iDestruct (own_slice_to_small with "Hret_sl") as "Hret_sl".
      wp_store.
      iModIntro. iApply "HΦ".
      by iFrame.
    }
    iApply (big_sepM_insert_2 with "").
    { (* put *)
      iExists _; iFrame "#".
      clear Φ.
      iIntros "%*%* !# (Hreq_sl & Hrep_sl & Hpre) HΦ".
      iDestruct "Hpre" as (?) "[% Hpre]".
      wp_pures.
      wp_apply (putArgs.wp_decode with "[$Hreq_sl //]").
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__put with "[$]").
      iIntros "HΨ".
      wp_pures.
      iModIntro. iApply "HΦ".
      iFrame.
      by iApply (own_slice_small_nil _ (DfracOwn 1)).
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      iIntros "%*%* !# (Hreq_sl & Hrep & Hpre) HΦ".
      wp_pures.
      wp_apply (wp_Server__getFreshNum with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_EncodeUint64.
      iIntros (?) "Henc_req".
      wp_store.
      iDestruct (own_slice_to_small with "Henc_req") as "?".
      iApply "HΦ". by iFrame.
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_server_proof.

Section client_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ, !urpcregG Σ, !kvserviceG Σ}.
Definition is_Client (cl:loc) γ : iProp Σ :=
  ∃ (urpcCl:loc) host,
  "#Hcl" ∷ cl ↦[Client :: "cl"]□ #urpcCl ∗
  "#HurpcCl" ∷ is_uRPCClient urpcCl host ∗
  "#Hhost" ∷ is_kvserver_host host γ
.

Lemma wp_makeClient (host:u64) γ:
  {{{
        "#Hhost" ∷ is_kvserver_host host γ
  }}}
    makeClient #host
  {{{
        (cl:loc), RET #cl; is_Client cl γ
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply wp_MakeClient.
  iIntros (?) "#?".
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  iMod (struct_field_pointsto_persist with "cl") as "#?".
  iModIntro.
  iApply "HΦ".
  repeat iExists _.
  iFrame "#".
Qed.

Lemma wp_Client__getFreshNumRpc cl γ :
  {{{
        "#Hcl" ∷ is_Client cl γ ∗
        "#Hspec" ∷ □ getFreshNum_core_pre
  }}}
    Client__getFreshNumRpc #cl
  {{{
        (err id:u64), RET (#id, #err); if decide (err = 0) then getFreshNum_core_post γ id else True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hreq_sl".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call with "[$Hreq_sl $Hrep $H0 $Hspec]"); first iFrame "HurpcCl".
  instantiate (1:=tt).
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  { (* case: got a reply *)
    destruct err; try by exfalso.
    { simpl in Heqb. destruct c; done. }
    iDestruct "Hpost" as "(? & H)".
    iDestruct "H" as (??) "(? & ? & (% & % & Hpost))".
    wp_load. subst.
    wp_apply (wp_DecodeUint64 with "[$]").
    wp_pures.
    by iApply "HΦ".
  }
  { (* case: Call returns error *)
    wp_pures.
    iApply "HΦ". rewrite decide_False //.
  }
Qed.

Lemma wp_Client__putRpc cl args args_ptr γ :
  {{{
        "Hargs" ∷ putArgs.own args_ptr args ∗
        "#Hcl" ∷ is_Client cl γ ∗
        "#Hspec" ∷ □ put_core_pre γ args
  }}}
    Client__putRpc #cl #args_ptr
  {{{
        (err:u64), RET #err; if decide (err = 0) then put_core_post γ args else True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (putArgs.wp_encode with "[$]").
  iIntros (??) "(Hargs & %Henc & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_apply (wp_Client__Call with "[$Hreq_sl $Hrep $H1 $Hspec]"); first iFrame "HurpcCl".
  { done. }
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  {
    destruct err.
    { destruct c; by exfalso. }
    iModIntro. iApply "HΦ".
    iDestruct "Hpost" as "(? & (% & % & ? & ? & (% & ? & ?)))".
    iExists _; iFrame.
  }
  { iApply "HΦ". rewrite decide_False //. }
Qed.

Lemma wp_Client__conditionalPutRpc γ cl args args_ptr :
  {{{
        "Hargs" ∷ conditionalPutArgs.own args_ptr args ∗
        "#Hcl" ∷ is_Client cl γ ∗
        "#Hspec" ∷ □ conditionalPut_core_pre γ args
  }}}
    Client__conditionalPutRpc #cl #args_ptr
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then
                                                    conditionalPut_core_post γ args s
                                                  else True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (conditionalPutArgs.wp_encode with "[$]").
  iIntros (??) "(Hargs & %Henc & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call with "[$Hreq_sl $Hrep $H2 $Hspec]"); first iFrame "HurpcCl".
  { done. }
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  {
    destruct err.
    { destruct c; by exfalso. }
    iDestruct "Hpost" as "(? & (% & % & ? & ? & ?))".
    subst.
    wp_load.
    wp_apply (wp_StringFromBytes with "[$]").
    iIntros "?".
    wp_pures. iApply "HΦ".
    iModIntro. iFrame.
  }
  { wp_pures. iApply "HΦ". rewrite decide_False //. }
Qed.

Lemma wp_Client__getRpc γ cl args args_ptr :
  {{{
        "Hargs" ∷ getArgs.own args_ptr args ∗
        "#Hcl" ∷ is_Client cl γ ∗
        "#Hspec" ∷ □ get_core_pre γ args
  }}}
    Client__getRpc #cl #args_ptr
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then get_core_post γ args s else True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (getArgs.wp_encode with "[$]").
  iIntros (??) "(Hargs & %Henc & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call with "[$Hreq_sl $Hrep $H3 $Hspec]"); first iFrame "HurpcCl".
  { done. }
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  {
    destruct err.
    { destruct c; by exfalso. }
    iDestruct "Hpost" as "(? & (% & % & ? & ? & ?))".
    subst.
    wp_load.
    wp_apply (wp_StringFromBytes with "[$]").
    iIntros "?".
    wp_pures. iApply "HΦ".
    iModIntro. iFrame.
  }
  { wp_pures. iApply "HΦ". rewrite decide_False //. }
Qed.

End client_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.
Context `{!kvserviceG Σ}.

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc),
  "#Hcl" ∷ ck ↦[Clerk :: "rpcCl"]□ #cl ∗
  "#HisCl" ∷ is_Client cl γ
.

Lemma wp_Clerk__Put (ck:loc) γ k v :
  ⊢ {{{ is_Clerk ck γ }}}
  <<< ∀∀ oldv, k ↪[γ.(kv_gn)] oldv >>>
    Clerk__Put #ck #(str k) #(str v) @ ↑reqN
  <<< k ↪[γ.(kv_gn)] v >>>
  {{{ RET #(); True }}}
.
Proof.
  iIntros "!#" (Φ) "#Hck Hatomic". wp_rec.
  (* symbolic execution *)
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc with "[$HisCl]").
  { done. }
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    rewrite decide_False //.
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  iMod (client_allocate_step with "[Hatomic] Hpost") as (?) "[#Hreq Htok]".
  { shelve. }
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__putRpc with "[Hcl opId key val]").
  { instantiate (1:=putArgs.mk _ _ _). iFrame "∗#". }
  Unshelve.
  2:{ iFrame. }
  iIntros (err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pure_credit "Hlc".
  wp_pures.
  erewrite decide_True; last done.
  iDestruct "Hpost" as (?) "#[??]".
  iMod (client_claim_step with "Hlc Hreq [$] [$] Htok") as "HΦ".
  iModIntro. iApply "HΦ". done.
Qed.

Lemma wp_Clerk__ConditionalPut (ck:loc) k expectV newV γ :
  ⊢ {{{ is_Clerk ck γ }}}
  <<< ∀∀ oldv, k ↪[γ.(kv_gn)] oldv >>>
    Clerk__ConditionalPut #ck #(str k) #(str expectV) #(str newV) @ ↑reqN
  <<< k ↪[γ.(kv_gn)] if bool_decide (oldv = expectV) then newV else oldv >>>
  {{{ RET #(bool_decide (oldv = expectV)); True }}}
.
Proof.
  iIntros "!#" (Φ) "#Hck Hatomic". wp_rec.
  (* symbolic execution *)
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc with "[$HisCl]").
  { done. }
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (ret_ptr) "Hret".
  wp_pures.

  iMod (client_allocate_step with "[Hatomic] Hpost") as (?) "[#Hreq Htok]".
  { shelve. }
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__conditionalPutRpc with "[Hcl opId key expectedVal newVal]").
  { instantiate (1:=conditionalPutArgs.mk _ _ _ _). iFrame "∗#". }
  Unshelve.
  2:{
    instantiate (1:=(λ x, True -∗ Φ #x)%I).
    (* FIXME: why doesn't the proof context get updated? *)
    iFrame.
  }
  iIntros (ret err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error, so retry *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  wp_store.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pure_credit "Hlc".
  wp_load.
  erewrite decide_True; last done.
  iDestruct "Hpost" as "#[? ?]".
  iMod (client_claim_step with "Hlc Hreq [$] [$] Htok") as "HΦ".
  iModIntro.
  destruct (decide _).
  { subst. simpl. by iApply "HΦ". }
  { rewrite bool_decide_false; last naive_solver. by iApply "HΦ". }
Qed.

Lemma wp_Clerk__Get (ck:loc) γ k :
  ⊢ {{{ is_Clerk ck γ }}}
  <<< ∀∀ oldv, k ↪[γ.(kv_gn)] oldv >>>
    Clerk__Get #ck #(str k) @ ↑reqN
  <<< k ↪[γ.(kv_gn)] oldv >>>
  {{{ RET #(str oldv); True }}}
.
Proof.
  iIntros "!#" (Φ) "#Hck Hatomic". wp_rec.
  (* symbolic execution *)
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc with "[$HisCl]").
  { done. }
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (ret_ptr) "Hret".
  wp_pures.

  iMod (client_allocate_step with "[Hatomic] Hpost") as (?) "[#Hreq Htok]".
  { shelve. }
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__getRpc with "[Hcl opId key]").
  { instantiate (1:=getArgs.mk _ _). iFrame "∗#". }
  Unshelve.
  3:{ iFrame. }
  iIntros (ret err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error, so retry *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  wp_store.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pure_credit "Hlc".
  wp_load.
  erewrite decide_True; last done.
  iDestruct "Hpost" as "#[? ?]".
  iMod (client_claim_step with "Hlc Hreq [$] [$] Htok") as "HΦ".
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_MakeClerk (host:u64) γ :
  {{{ is_kvserver_host host γ }}}
    MakeClerk #host
  {{{ ck, RET #ck; is_Clerk ck γ }}}
.
Proof.
  iIntros (Φ) "#Hhost HΦ".
  wp_rec.
  wp_apply (wp_makeClient with "Hhost").
  iIntros (?) "#?".
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  iApply "HΦ".
  iMod (struct_field_pointsto_persist with "rpcCl") as "#?".
  iModIntro.
  iExists _; iFrame "#".
Qed.

End clerk_proof.
