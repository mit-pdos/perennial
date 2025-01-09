From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import kvservice.
From Perennial.program_proof.grove_shared Require Import urpc_proof monotonic_pred.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang Require Import proofmode.

From Perennial.program_proof.tutorial.kvservice Require Import get_proof.
From Perennial.program_proof.tutorial.kvservice Require Import conditionalput_proof.
From Perennial.program_proof.tutorial.kvservice Require Import put_proof.

Unset Printing Projections.

(********************************************************************************)

(* Module putArgs. *)
(* Record t := *)
(*   mk { *)
(*       opId: u64 ; *)
(*       key: string ; *)
(*       val: string ; *)
(*   }. *)

(* Definition encodes (x:list u8) (a:t) : Prop := *)
(*   x = u64_le a.(opId) ++ (u64_le $ length $ string_to_bytes a.(key)) ++ *)
(*       string_to_bytes a.(key) ++ string_to_bytes a.(val) *)
(* . *)

(* Section local_defs. *)
(* Context `{!heapGS Σ}. *)
(* Definition own (a:loc) (args:t) : iProp Σ := *)
(*   "HopId" ∷ a ↦[putArgs :: "opId"] #args.(opId) ∗ *)
(*   "Hkey" ∷ a ↦[putArgs :: "key"] #(str args.(key)) ∗ *)
(*   "Hval" ∷ a ↦[putArgs :: "val"] #(str args.(val)) *)
(* . *)

(* Lemma wp_encode args_ptr args : *)
(*   {{{ *)
(*         own args_ptr args *)
(*   }}} *)
(*     encodePutArgs #args_ptr *)
(*   {{{ *)
(*         (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗ *)
(*           ⌜encodes enc_args args⌝ ∗ *)
(*           own_slice sl byteT (DfracOwn 1) enc_args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hargs HΦ". *)
(*   iNamed "Hargs". *)
(*   wp_rec. *)
(*   wp_apply wp_NewSlice. *)
(*   iIntros (sl) "Hsl". *)
(*   wp_apply wp_ref_to. *)
(*   { done. } *)
(*   iIntros (e) "He". *)

(*   wp_pures. *)
(*   wp_loadField. *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "[$]"). *)
(*   iIntros (?) "Hsl". *)
(*   rewrite replicate_0 /=. *)
(*   wp_store. *)

(*   wp_loadField. *)
(*   wp_apply wp_StringToBytes. *)
(*   iIntros (key_sl) "Hkey_sl". *)
(*   wp_pures. *)

(*   wp_apply wp_slice_len. *)
(*   iDestruct (own_slice_sz with "Hkey_sl") as "%Hsz". *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "[$Hsl]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_store. *)

(*   wp_load. *)
(*   iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl". *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]"). *)
(*   iIntros (?) "[Hsl Hkey_sl]". *)
(*   wp_store. *)

(*   wp_loadField. *)
(*   wp_apply (wp_StringToBytes). *)
(*   iIntros (?) "Hval_sl". *)
(*   iDestruct (own_slice_to_small with "Hval_sl") as "Hval_sl". *)
(*   wp_load. *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hval_sl]"). *)
(*   iIntros (?) "[Hsl Hval_sl]". *)
(*   wp_store. *)

(*   wp_load. *)
(*   iApply "HΦ". *)
(*   iFrame. *)
(*   iPureIntro. *)
(*   unfold encodes. *)
(*   repeat rewrite -assoc. *)
(*   rewrite Hsz. *)
(*   repeat f_equal. *)
(*   word. *)
(* Qed. *)

(* Lemma wp_decode  sl enc_args args q : *)
(*   {{{ *)
(*         "%Henc" ∷ ⌜encodes enc_args args⌝ ∗ *)
(*         "Hsl" ∷ own_slice_small sl byteT q enc_args *)
(*   }}} *)
(*     decodePutArgs (slice_val sl) *)
(*   {{{ *)
(*         (args_ptr:loc), RET #args_ptr; own args_ptr args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hpre HΦ". *)
(*   iNamed "Hpre". *)
(*   wp_rec. *)
(*   wp_apply wp_ref_to. *)
(*   { done. } *)
(*   iIntros (e) "He". *)
(*   wp_pures. *)
(*   wp_apply wp_allocStruct. *)
(*   { repeat econstructor. } *)
(*   iIntros (args_ptr) "Hargs". *)
(*   iDestruct (struct_fields_split with "Hargs") as "HH". *)
(*   iNamed "HH". *)

(*   wp_pures. *)
(*   wp_load. *)
(*   rewrite Henc; clear dependent enc_args. *)
(*   wp_apply (wp_ReadInt with "[$]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)
(*   wp_storeField. *)
(*   wp_store. *)
(*   wp_load. *)
(*   wp_apply (wp_ReadInt with "[$]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)
(*   iDestruct (own_slice_small_sz with "Hsl") as %Hsz. *)
(*   wp_apply (wp_ReadBytes with "[$]"). *)
(*   { rewrite length_app in Hsz. word. } *)
(*   iIntros (??) "[Hkey Hval]". *)
(*   wp_pures. *)
(*   wp_apply (wp_StringFromBytes with "[$Hkey]"). *)
(*   iIntros "Hkey". *)
(*   wp_storeField. *)
(*   wp_apply (wp_StringFromBytes with "[$Hval]"). *)
(*   iIntros "Hval". *)
(*   wp_storeField. *)
(*   iModIntro. *)
(*   iApply "HΦ". *)
(*   do 2 rewrite string_to_bytes_to_string. *)
(*   iFrame. *)
(* Qed. *)

(* End local_defs. *)
(* End putArgs. *)

(* Module conditionalPutArgs. *)
(* Record t := *)
(*   mk { *)
(*       opId: u64 ; *)
(*       key: string ; *)
(*       expectedVal: string ; *)
(*       newVal: string ; *)
(*   }. *)

(* Definition encodes (x:list u8) (a:t) : Prop := *)
(*   x = u64_le a.(opId) ++ (u64_le $ length $ string_to_bytes a.(key)) ++ string_to_bytes a.(key) ++ *)
(*       (u64_le $ length $ string_to_bytes a.(expectedVal)) ++ string_to_bytes a.(expectedVal) ++ string_to_bytes a.(newVal) *)
(* . *)

(* Section local_defs. *)
(* Context `{!heapGS Σ}. *)
(* Definition own (a:loc) (args:t) : iProp Σ := *)
(*   "HopId" ∷ a ↦[conditionalPutArgs :: "opId"] #args.(opId) ∗ *)
(*   "Hkey" ∷ a ↦[conditionalPutArgs :: "key"] #(str args.(key)) ∗ *)
(*   "HexpectedVal" ∷ a ↦[conditionalPutArgs :: "expectedVal"] #(str args.(expectedVal)) ∗ *)
(*   "Hval" ∷ a ↦[conditionalPutArgs :: "newVal"] #(str args.(newVal)) *)
(* . *)

(* Lemma wp_encode args_ptr args : *)
(*   {{{ *)
(*         own args_ptr args *)
(*   }}} *)
(*     encodeConditionalPutArgs #args_ptr *)
(*   {{{ *)
(*         (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗ *)
(*           ⌜encodes enc_args args⌝ ∗ *)
(*           own_slice sl byteT (DfracOwn 1) enc_args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hargs HΦ". *)
(*   iNamed "Hargs". *)
(*   wp_rec. *)
(*   wp_apply wp_NewSlice. *)
(*   iIntros (sl) "Hsl". *)
(*   wp_apply wp_ref_to. *)
(*   { done. } *)
(*   iIntros (e) "He". *)
(*   wp_pures. *)

(*   wp_loadField. *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "[$]"). *)
(*   iIntros (?) "Hsl". *)
(*   rewrite replicate_0 /=. *)
(*   wp_store. *)

(*   wp_loadField. *)
(*   wp_apply wp_StringToBytes. *)
(*   iIntros (key_sl) "Hkey_sl". *)
(*   wp_pures. *)
(*   wp_apply wp_slice_len. *)
(*   iDestruct (own_slice_sz with "Hkey_sl") as "%Hsz". *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "[$Hsl]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_store. *)

(*   wp_load. *)
(*   iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl". *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]"). *)
(*   iIntros (?) "[Hsl Hkey_sl]". *)
(*   wp_store. *)

(*   wp_loadField. *)
(*   wp_apply (wp_StringToBytes). *)
(*   iIntros (?) "Hexpect_sl". *)
(*   iDestruct (own_slice_to_small with "Hexpect_sl") as "Hexpect_sl". *)
(*   wp_pures. *)

(*   wp_apply wp_slice_len. *)
(*   iDestruct (own_slice_small_sz with "Hexpect_sl") as %?. *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "[$Hsl]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_store. *)

(*   wp_load. *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hexpect_sl]"). *)
(*   iIntros (?) "[Hsl Hexpect_sl]". *)
(*   wp_store. *)

(*   wp_loadField. *)
(*   wp_apply (wp_StringToBytes). *)
(*   iIntros (?) "Hval_sl". *)
(*   wp_load. *)
(*   iDestruct (own_slice_to_small with "Hval_sl") as "Hval_sl". *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hval_sl]"). *)
(*   iIntros (?) "[Hsl Hval_sl]". *)
(*   wp_store. *)

(*   wp_load. *)
(*   iApply "HΦ". *)
(*   iFrame. *)
(*   iPureIntro. *)
(*   unfold encodes. *)
(*   repeat rewrite -assoc. *)
(*   rewrite Hsz. *)
(*   repeat f_equal; word. *)
(* Qed. *)

(* Lemma wp_decode  sl enc_args args q : *)
(*   {{{ *)
(*         "%Henc" ∷ ⌜encodes enc_args args⌝ ∗ *)
(*         "Hsl" ∷ own_slice_small sl byteT q enc_args *)
(*   }}} *)
(*     decodeConditionalPutArgs (slice_val sl) *)
(*   {{{ *)
(*         (args_ptr:loc), RET #args_ptr; own args_ptr args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hpre HΦ". *)
(*   iNamed "Hpre". *)
(*   wp_rec. *)
(*   wp_apply wp_ref_to. *)
(*   { done. } *)
(*   iIntros (?) "He". *)
(*   wp_pures. *)
(*   wp_apply wp_allocStruct. *)
(*   { repeat econstructor. } *)
(*   iIntros (args_ptr) "Hargs". *)
(*   wp_pures. *)
(*   iDestruct (struct_fields_split with "Hargs") as "HH". *)
(*   iNamed "HH". *)
(*   wp_load. *)
(*   rewrite Henc. *)

(*   wp_apply (wp_ReadInt with "Hsl"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)
(*   wp_storeField. *)
(*   wp_store. *)

(*   wp_load. *)
(*   wp_apply (wp_ReadInt with "Hsl"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)

(*   iDestruct (own_slice_small_sz with "Hsl") as %Hsz. *)
(*   wp_apply (wp_ReadBytes with "[$Hsl]"). *)
(*   { rewrite length_app in Hsz. word. } *)
(*   iIntros (??) "[Hkey Hsl]". *)
(*   wp_pures. *)
(*   wp_apply (wp_StringFromBytes with "[$Hkey]"). *)
(*   iIntros "_". *)
(*   wp_storeField. *)

(*   wp_apply (wp_ReadInt with "[$Hsl]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)

(*   wp_apply (wp_ReadBytes with "[$Hsl]"). *)
(*   { repeat rewrite length_app in Hsz. word. } *)
(*   iIntros (??) "[Hexpect Hval]". *)
(*   wp_pures. *)

(*   wp_apply (wp_StringFromBytes with "[$Hexpect]"). *)
(*   iIntros "_". *)
(*   wp_storeField. *)
(*   wp_apply (wp_StringFromBytes with "[$Hval]"). *)
(*   iIntros "_". *)
(*   wp_storeField. *)
(*   iModIntro. iApply "HΦ". *)
(*   repeat rewrite string_to_bytes_to_string. *)
(*   iFrame. *)
(* Qed. *)

(* End local_defs. *)
(* End conditionalPutArgs. *)

(* Module getArgs. *)
(* Record t := *)
(*   mk { *)
(*       opId: u64 ; *)
(*       key: string ; *)
(*   }. *)

(* Definition encodes (x:list u8) (a:t) : Prop := *)
(*   x = u64_le a.(opId) ++ string_to_bytes a.(key) *)
(* . *)

(* Section local_defs. *)
(* Context `{!heapGS Σ}. *)
(* Definition own `{!heapGS Σ} (a:loc) (args:t) : iProp Σ := *)
(*   "HopId" ∷ a ↦[getArgs :: "opId"] #args.(opId) ∗ *)
(*   "Hkey" ∷ a ↦[getArgs :: "key"] #(str args.(key)) *)
(* . *)

(* Lemma wp_encode args_ptr args : *)
(*   {{{ *)
(*         own args_ptr args *)
(*   }}} *)
(*     encodeGetArgs #args_ptr *)
(*   {{{ *)
(*         (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗ *)
(*           ⌜encodes enc_args args⌝ ∗ *)
(*           own_slice sl byteT (DfracOwn 1) enc_args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hargs HΦ". *)
(*   iNamed "Hargs". *)
(*   wp_rec. *)
(*   wp_apply wp_NewSlice. *)
(*   iIntros (?) "Hsl". *)
(*   wp_apply (wp_ref_to). *)
(*   { done. } *)
(*   iIntros (?) "He". *)
(*   wp_pures. *)
(*   wp_loadField. *)
(*   wp_load. *)
(*   wp_apply (wp_WriteInt with "Hsl"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_store. *)
(*   wp_loadField. *)
(*   wp_apply (wp_StringToBytes). *)
(*   iIntros (?) "Hkey_sl". *)
(*   wp_load. *)
(*   iDestruct (own_slice_to_small with "Hkey_sl") as "Hkey_sl". *)
(*   wp_apply (wp_WriteBytes with "[$Hsl $Hkey_sl]"). *)
(*   iIntros (?) "[Hsl _]". *)
(*   wp_store. *)
(*   wp_load. *)
(*   iModIntro. iApply "HΦ". *)
(*   iFrame. *)
(*   iPureIntro. done. *)
(* Qed. *)

(* Lemma wp_decode  sl enc_args args q : *)
(*   {{{ *)
(*         "%Henc" ∷ ⌜encodes enc_args args⌝ ∗ *)
(*         "Hsl" ∷ own_slice_small sl byteT q enc_args *)
(*   }}} *)
(*     decodeGetArgs (slice_val sl) *)
(*   {{{ *)
(*         (args_ptr:loc), RET #args_ptr; own args_ptr args *)
(*   }}} *)
(* . *)
(* Proof. *)
(*   iIntros (Φ) "Hpre HΦ". *)
(*   iNamed "Hpre". *)
(*   wp_rec. *)
(*   wp_apply (wp_ref_to). *)
(*   { done. } *)
(*   iIntros (?) "He". *)
(*   wp_pures. *)
(*   wp_apply (wp_ref_of_zero). *)
(*   { done. } *)
(*   iIntros (?) "HkeyBytes". *)
(*   wp_pures. *)
(*   wp_apply wp_allocStruct. *)
(*   { repeat econstructor. } *)
(*   iIntros (args_ptr) "Hargs". *)
(*   iDestruct (struct_fields_split with "Hargs") as "HH". *)
(*   iNamed "HH". *)
(*   wp_pures. *)
(*   wp_load. *)
(*   rewrite Henc. *)
(*   wp_apply (wp_ReadInt with "[$Hsl]"). *)
(*   iIntros (?) "Hsl". *)
(*   wp_pures. *)
(*   wp_storeField. *)
(*   wp_store. *)

(*   wp_load. *)
(*   wp_apply (wp_StringFromBytes with "[$Hsl]"). *)
(*   iIntros "_". *)
(*   wp_storeField. *)
(*   iModIntro. *)
(*   iApply "HΦ". *)
(*   repeat rewrite string_to_bytes_to_string. *)
(*   iFrame. *)
(* Qed. *)

(* End local_defs. *)

(* End getArgs. *)

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

Section rpc_definitions.
(* NOTE: "global" context because RPC specs are known by multiple machines. *)
Context `{!gooseGlobalGS Σ}.

Definition getFreshNum_core_spec (Φ:u64 → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ opId, Φ opId)%I.

Global Instance getFreshNum_core_MonotonicPred : MonotonicPred (getFreshNum_core_spec).
Proof. apply _. Qed.

Definition put_core_spec (args:put.C) (Φ:unit → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  Φ ().

Global Instance put_core_MonotonicPred args : MonotonicPred (put_core_spec args).
Proof. apply _. Qed.

Definition conditionalPut_core_spec (args:conditionalPut.C) (Φ:byte_string → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ status, Φ status)%I.

Global Instance conditionalPut_core_MonotonicPred args : MonotonicPred (conditionalPut_core_spec args).
Proof. apply _. Qed.

Definition get_core_spec (args:get.C) (Φ:byte_string → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ ret, Φ ret)%I.

Definition get_core_MonotonicPred args : MonotonicPred (get_core_spec args).
Proof. apply _. Qed.

End rpc_definitions.

Section rpc_server_proofs.
Context `{!heapGS Σ}.

Definition own_Server (s:loc) : iProp Σ :=
  ∃ (nextFreshId:u64) (lastReplies:gmap u64 byte_string) (kvs:gmap byte_string byte_string)
    (lastReplies_loc kvs_loc:loc),
  "HnextFreshId" ∷ s ↦[Server :: "nextFreshId"] #nextFreshId ∗
  "HlastReplies" ∷ s ↦[Server :: "lastReplies"] #lastReplies_loc ∗
  "Hkvs" ∷ s ↦[Server :: "kvs"] #kvs_loc ∗
  "HlastRepliesM" ∷ own_map lastReplies_loc (DfracOwn 1) lastReplies ∗
  "HkvsM" ∷ own_map kvs_loc (DfracOwn 1) kvs
.

Definition is_Server (s:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ s ↦[Server :: "mu"]□ mu ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s)
.

(* FIXME: make use of explicit spec montonicity and get rid of Ψ+Φ. *)
Lemma wp_Server__getFreshNum (s:loc) Ψ :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ getFreshNum_core_spec Ψ
  }}}
    Server__getFreshNum #s
  {{{ (n:u64), RET #n; Ψ n }}}
.
Proof.
  wp_start.
  iNamed "Hsrv".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$]") as "[Hlocked Hown]"; iNamed "Hown"; wp_auto.
  wp_apply (wp_SumAssumeNoOverflow) as (Hoverflow) "".
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _.
    iFrame.
  }
  wp_pures.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma wp_Server__put (s:loc) args__v (args:put.C) Ψ :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ put_core_spec args Ψ ∗
        "Hargs" ∷ put.own args__v args (DfracOwn 1)
  }}}
  Server__put #s args__v
  {{{
        RET #(); Ψ ()
  }}}
.
Proof.
  wp_start.
  iNamed "Hsrv".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$]") as "[Hlocked Hown]"; iNamed "Hown".
  iUnfold put.own in "Hargs". iNamed "Hargs". rewrite Hown_struct. wp_pures.
  wp_auto.
  wp_apply (wp_MapGet with "HlastRepliesM") as (??) "[%HlastReply HlastRepliesM]".
  wp_if_destruct; wp_auto.
  { (* case: this is a duplicate request *)
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _.
      iFrame.
    }
    wp_pures.
    iApply ("HΦ" with "Hspec").
  }
  wp_apply (wp_MapInsert with "HkvsM") as "HkvsM"; first done.
  wp_apply (wp_MapInsert with "HlastRepliesM") as "HlastRepliesM"; first done.
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _.
    iFrame.
  }
  wp_pures.
  iApply ("HΦ" with "Hspec").
Qed.

Lemma wp_Server__conditionalPut (s:loc) args__v (args:conditionalPut.C) Ψ :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ conditionalPut_core_spec args Ψ ∗
        "Hargs" ∷ conditionalPut.own args__v args (DfracOwn 1)
  }}}
    Server__conditionalPut #s args__v
  {{{ r, RET #(str r); Ψ r }}}
.
Proof.
  wp_start.
  iNamed "Hsrv".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$]") as "[Hlocked Hown]"; iNamed "Hown".
  iUnfold conditionalPut.own in "Hargs". iNamed "Hargs". rewrite Hown_struct.
  wp_auto.
  wp_apply (wp_MapGet with "HlastRepliesM") as (??) "[%HlastReply HlastRepliesM]".
  wp_if_destruct; wp_auto.
  { (* case: this is a duplicate request *)
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _.
      iFrame.
    }
    wp_pures.
    iApply "HΦ".
    iApply "Hspec".
  }
  wp_apply (wp_ref_to) as (ret2_ptr) "Hret"; first val_ty.
  wp_apply (wp_MapGet with "HkvsM") as (??) "[Hlookup HkvsM]".
  wp_if_destruct; wp_auto.
  { (* case: the old value matches the expected value *)
    wp_apply (wp_MapInsert with "HkvsM") as "HkvsM"; first done.
    (* FIXME: delete typed_map.map_insert *)
    rewrite /typed_map.map_insert.
    wp_apply (wp_MapInsert with "HlastRepliesM") as "HlastRepliesM"; first done.
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec Hret]").
    {
      iFrame "∗#". iNext.
      repeat iExists _.
      iFrame.
    }
    wp_auto.
    iModIntro.
    iApply ("HΦ" with "Hspec").
  }

  wp_apply (wp_MapInsert with "HlastRepliesM") as "HlastRepliesM"; first done.
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec Hret]").
  {
    iFrame "∗#". iNext.
    repeat iExists _.
    iFrame.
  }
  wp_auto.
  iModIntro.
  iApply ("HΦ" with "Hspec").
Qed.

Lemma wp_Server__get (s:loc) args__v (args:get.C) Ψ :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ get_core_spec args Ψ ∗
        "Hargs" ∷ get.own args__v args (DfracOwn 1)
  }}}
    Server__get #s args__v
  {{{
        r, RET #(str r); Ψ r
  }}}
.
Proof.
  wp_start.
  iNamed "Hsrv".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$]") as "[Hlocked Hown]"; iNamed "Hown".
  iUnfold get.own in "Hargs". iNamed "Hargs". rewrite Hown_struct.
  wp_auto.
  wp_apply (wp_MapGet with "HlastRepliesM") as (??) "[%HlastReply HlastRepliesM]".
  wp_if_destruct; wp_auto.
  { (* case: this is a duplicate request *)
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
    {
      iFrame "∗#". iNext.
      repeat iExists _.
      iFrame.
    }
    wp_pures.
    iApply "HΦ".
    iApply "Hspec".
  }
  wp_apply (wp_MapGet with "HkvsM") as (??) "[%Hlookup HkvsM]".
  wp_apply (wp_MapInsert with "HlastRepliesM") as "HlastRepliesM"; first done.
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hspec]").
  {
    iFrame "∗#". iNext.
    repeat iExists _.
    iFrame.
  }
  wp_pures.
  iApply "HΦ".
  iApply "Hspec".
Qed.

Lemma wp_MakeServer :
  {{{
        True
  }}}
    MakeServer #()
  {{{
        (s:loc), RET #s; is_Server s
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
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
  iApply "HΦ".
  iMod (struct_field_pointsto_persist with "mu") as "#Hmu".
  iExists _; iFrame "#".
  iMod (alloc_lock with "HmuInv [-]") as "$"; last done.
  iNext.
  repeat iExists _; iFrame.
Qed.

End rpc_server_proofs.

Section encoded_rpc_definitions.
(* This section is boilerplate. *)
Context `{!gooseGlobalGS Σ}.
Context `{!urpcregG Σ}.

Program Definition getFreshNum_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (
  getFreshNum_core_spec (λ (num:u64), Φ (u64_le num))
  )%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition put_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜put.has_encoding enc_args args⌝ ∗
   put_core_spec args (λ _, ∀ enc_reply, Φ enc_reply)
  )%I
.
Next Obligation.
  rewrite /put_core_spec. solve_proper.
Defined.

Program Definition conditionalPut_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜conditionalPut.has_encoding enc_args args⌝ ∗
   conditionalPut_core_spec args (λ rep, Φ rep)
  )%I
.
Next Obligation.
  rewrite /conditionalPut_core_spec. solve_proper.
Defined.

Program Definition get_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜get.has_encoding enc_args args⌝ ∗
   get_core_spec args (λ rep, Φ rep)
  )%I
.
Next Obligation.
  solve_proper.
Defined.

Definition is_kvserver_host host : iProp Σ :=
  ∃ γrpc,
  "#H0" ∷ is_urpc_spec_pred γrpc host (W64 0) getFreshNum_spec ∗
  "#H1" ∷ is_urpc_spec_pred γrpc host (W64 1) put_spec ∗
  "#H2" ∷ is_urpc_spec_pred γrpc host (W64 2) conditionalPut_spec ∗
  "#H3" ∷ is_urpc_spec_pred γrpc host (W64 3) get_spec ∗
  "#Hdom" ∷ is_urpc_dom γrpc {[ W64 0; W64 1; W64 2; W64 3 ]}
  .

End encoded_rpc_definitions.

Section start_server_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Lemma wp_Server__Start (s:loc) (host:u64) :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "#Hhost" ∷ is_kvserver_host host
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
  wp_apply (wp_StartServer_pred with "[$Hr]").
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
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (get.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. by iPureIntro. }
      iIntros (??) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__get with "[$]").
      iIntros (?) "HΨ".
      wp_pures. wp_apply wp_StringToBytes.
      iIntros (ret_sl) "Hret_sl".
      iDestruct (own_slice_to_small with "Hret_sl") as "Hret_sl".
      wp_store.
      iModIntro. iApply "HΦ"; iFrame.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (conditionalPut.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. done. }
      iIntros (??) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__conditionalPut with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_StringToBytes.
      iIntros (?) "Henc_req".
      wp_store.
      iApply "HΦ"; iFrame.
      by iDestruct (own_slice_to_small with "Henc_req") as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (put.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. done. }
      iIntros (??) "Hargs". iDestruct "Hargs" as "[Hargs _]".
      wp_apply (wp_Server__put with "[$Hsrv $Hargs Hspec //]").
      iIntros "HΨ". wp_pures.
      iApply "HΦ"; iFrame.
      by iDestruct (own_slice_small_nil _ (DfracOwn 1)) as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iEval (rewrite /getFreshNum_spec /=) in "Hspec".
      wp_apply (wp_Server__getFreshNum with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_EncodeUint64.
      iIntros (?) "Henc_req".
      wp_store.
      iApply "HΦ"; iFrame.
      by iDestruct (own_slice_to_small with "Henc_req") as "$".
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_server_proof.

Section client_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ, !urpcregG Σ}.
Definition is_Client (cl:loc) : iProp Σ :=
  ∃ (urpcCl:loc) host,
  "#Hcl" ∷ cl ↦[Client :: "cl"]□ #urpcCl ∗
  "#HurpcCl" ∷ is_uRPCClient urpcCl host ∗
  "#Hhost" ∷ is_kvserver_host host
.

Lemma wp_makeClient (host:u64) :
  {{{
        "#Hhost" ∷ is_kvserver_host host
  }}}
    makeClient #host
  {{{
        (cl:loc), RET #cl; is_Client cl
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

Lemma wp_Client__getFreshNumRpc Post cl :
  {{{
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ getFreshNum_core_spec Post
  }}}
    Client__getFreshNumRpc #cl
  {{{
        (err id:u64), RET (#id, #err); if decide (err = 0) then Post id else True
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

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  iSplit.
  { (* case: got a reply *)
    iModIntro. iModIntro.
    rewrite replicate_0.
    rewrite /getFreshNum_spec /=.
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iIntros (?) "HPost".
    iIntros "Hreq_sl % Hrep Hrep_sl".
    iNamed 1.
    wp_pures.
    wp_load. subst.
    wp_apply (wp_DecodeUint64 with "[$]").
    wp_pures.
    by iApply "HΦ".
  }
  { (* case: Call returns error *)
    iIntros (??) "Hreq_sl Hrep". iNamed 1.
    wp_pures.
    wp_if_destruct.
    wp_pures.
    iApply "HΦ".
    by rewrite decide_False.
  }
Qed.

Lemma wp_Client__putRpc Post cl args args__v:
  {{{
        "Hargs" ∷ put.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ put_core_spec args Post
  }}}
    Client__putRpc #cl args__v
  {{{
        (err:u64), RET #err; if decide (err = 0) then Post () else True
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
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply (put.wp_Encode with "[$]").
  iIntros (??) "(%Henc & Hargs_own & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /put_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iIntros (?) "HPost".
    iIntros (?) "Hreq_sl". iIntros (?) "Hrep Hrep_sl".
    iNamed 1.
    wp_pures.
    iModIntro. iApply "HΦ".
    destruct r. iFrame.
  }
  {
    iIntros (??) "Hreq_sl Hrep".
    iNamed 1.
    wp_pures.
    wp_if_destruct.
    wp_pures.
    iApply "HΦ".
    by rewrite decide_False.
  }
Qed.

Lemma wp_Client__conditionalPutRpc Post cl args args__v :
  {{{
        "Hargs" ∷ conditionalPut.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ conditionalPut_core_spec args Post
  }}}
    Client__conditionalPutRpc #cl args__v
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then Post s else True
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
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply (conditionalPut.wp_Encode with "[$]").
  iIntros (??) "(%Henc & Hargs_own & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /conditionalPut_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iIntros (?) "HPost".
    iIntros "Hreq_sl % Hrep Hrep_sl".
    iNamed 1.
    wp_pures.
    wp_load.
    wp_apply (wp_StringFromBytes with "[$]").
    iIntros "_".
    wp_pures.
    iModIntro. iApply "HΦ".
    iFrame.
  }
  {
    iIntros (??) "Hreq_sl Hrep".
    iNamed 1.
    wp_pures.
    wp_if_destruct.
    wp_pures.
    iApply "HΦ".
    by rewrite decide_False.
  }
Qed.

Lemma wp_Client__getRpc Post cl args args__v :
  {{{
        "Hargs" ∷ get.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ get_core_spec args Post
  }}}
    Client__getRpc #cl args__v
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then Post s else True
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
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply (get.wp_Encode with "[$]").
  iIntros (??) "(%Henc & Hargs_own & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /conditionalPut_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iIntros (?) "HPost".
    iIntros "Hreq_sl % Hrep Hrep_sl".
    iNamed 1.
    wp_pures.
    wp_load.
    wp_apply (wp_StringFromBytes with "[$]").
    iIntros "_".
    wp_pures.
    iModIntro. iApply "HΦ".
    iFrame.
  }
  {
    iIntros (??) "Hreq_sl Hrep".
    iNamed 1.
    wp_pures.
    wp_if_destruct.
    wp_pures.
    iApply "HΦ".
    by rewrite decide_False.
  }
Qed.


End client_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Definition is_Clerk (ck:loc) : iProp Σ :=
  ∃ (cl:loc),
  "#Hcl" ∷ ck ↦[Clerk :: "rpcCl"]□ #cl ∗
  "#HisCl" ∷ is_Client cl
.

Lemma wp_Clerk__Put (ck:loc) k v :
  {{{ is_Clerk ck }}}
    Clerk__Put #ck #(str k) #(str v)
  {{{ RET #(); True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
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
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
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

  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__putRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=put.mkC _ _ _). iFrame "∗#". done. }
  iClear "Hpost".
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
  wp_pures.
  iModIntro. iApply "HΦ". done.
Qed.

Lemma wp_Clerk__ConditionalPut (ck:loc) k expectV newV :
  {{{ is_Clerk ck }}}
    Clerk__ConditionalPut #ck #(str k) #(str expectV) #(str newV)
  {{{ (ok:bool), RET #ok; True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
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
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
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
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__conditionalPutRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=conditionalPut.mkC _ _ _ _). iFrame "∗#". done. }
  iClear "Hpost".
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
  wp_pures.
  wp_load.
  iModIntro. iApply "HΦ". done.
Qed.

Lemma wp_Clerk__Get (ck:loc) k :
  {{{ is_Clerk ck }}}
    Clerk__Get #ck #(str k)
  {{{ v, RET #(str v); True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
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
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
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
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__getRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=get.mkC _ _). iFrame "∗#". done. }
  iClear "Hpost".
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
  wp_pures.
  wp_load.
  iModIntro. iApply "HΦ". done.
Qed.

Lemma wp_MakeClerk (host:u64) :
  {{{ is_kvserver_host host }}}
    MakeClerk #host
  {{{ ck, RET #ck; is_Clerk ck }}}
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
