(*****************************************)
(* This file is autogenerated by grackle *)
(*    DO NOT MANUALLY EDIT THIS FILE     *)
(*****************************************)

From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mit_pdos.gokv.tutorial.objectstore.dir.finishwrite_gk.

Module finishWrite.
Section finishWrite.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        writeId : u64;
        keyname : byte_string;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(writeId)) ++
              (u64_le $ length $ args.(keyname)) ++ args.(keyname).

Definition own (args__v: val) (args__c: C) (dq: dfrac) : iProp Σ :=
  "%Hown_struct" ∷ ⌜ args__v = (#args__c.(writeId), (#(str args__c.(keyname)), #()))%V ⌝.


Definition to_val' (c : C) : val :=
  (#c.(writeId), (#(str c.(keyname)), #())).

Definition from_val' (v : val) : option C :=
  match v with
  | (#(LitInt writeId), (#(LitString keyname), #()))%V =>
    Some (mkC writeId keyname)
  | _ => None
  end.

#[global]
Instance finishWrite_into_val : IntoVal C.
Proof.
  refine {|
    to_val := to_val';
    from_val := from_val';
    IntoVal_def := (mkC (W64 0) "")
  |}.
  intros v. 
  destruct v as [writeId keyname]; done.
Defined.

#[global]
Instance finishWrite_into_val_for_type : IntoValForType C (struct.t finishwrite_gk.S).
Proof. constructor; auto 10. Defined.

Lemma own_to_val (v : val) (c : C) (dq : dfrac) :
  own v c dq -∗ own v c dq ∗ ⌜ v = to_val c ⌝.
Proof.
  iIntros "%Hown_struct".
  
  iUnfold own.
  iSplitL.
  + iPureIntro. done.
  +  done.
Qed.


Lemma wp_Encode (args__v : val) (args__c : C) (pre_sl : Slice.t) (prefix : list u8) (dq : dfrac):
  {{{
        own args__v args__c dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    finishwrite_gk.Marshal args__v (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜ has_encoding enc args__c ⌝ ∗
        own args__v args__c dq ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.

Proof.
  iIntros (?) "[Hown Hsl] HΦ".
  wp_rec. wp_pures.
  iUnfold own in "Hown". iNamed "Hown". rewrite Hown_struct.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.

  wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_apply wp_StringToBytes. iIntros (?) "Hargs_keyname_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_keyname_enc") as "%Hargs_keyname_sz".
  iApply own_slice_to_small in "Hargs_keyname_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_keyname_enc]").
  iIntros (?) "[Hsl _]". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. split.
  {
  
  rewrite ?string_bytes_length.
  rewrite Hargs_keyname_sz.
  rewrite ?w64_to_nat_id. exact.

  } done.
Qed.

Lemma wp_Decode (enc : list u8) (enc_sl : Slice.t) (args__c : C) (suffix : list u8) (dq : dfrac):
  {{{
        ⌜ has_encoding enc args__c ⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    finishwrite_gk.Unmarshal (slice_val enc_sl)
  {{{
        args__v suff_sl, RET (args__v, suff_sl);
        own args__v args__c (DfracOwn 1) ∗
        own_slice_small suff_sl byteT dq suffix
  }}}.

Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_ref_to; first done.
  iIntros (l__s) "Hs". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__writeId) "HwriteId". wp_pures.
  
  wp_apply wp_ref_of_zero; first done.
  iIntros (l__keyname) "Hkeyname". wp_pures.
  
  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_store. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (keynameLen) "HkeynameLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (keynameBytes) "HkeynameBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hkeyname_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hkeyname_sz. word. }
  iIntros (??) "[Hkeyname' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  iApply own_slice_to_small in "Hkeyname'".
  wp_apply (wp_StringFromBytes with "[$Hkeyname']"). iIntros "_".
  wp_store.

  wp_load. wp_load. wp_load.
  wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
  iPureIntro. reflexivity.
Qed.

End finishWrite.
End finishWrite.

