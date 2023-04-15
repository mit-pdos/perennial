From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kvee.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.simplepb Require Import pb_apply_proof clerk_proof.
From Perennial.program_proof.grove_shared Require Import erpc_lib.
From Perennial.program_proof Require Import map_marshal_proof.
From Perennial.program_proof Require Import map_marshal_proof.
From iris.algebra Require Import dfrac_agree mono_list.

From Perennial.program_proof.simplepb.apps Require Import eesm_proof kv_proof log.

Section global_proof.

Context `{!heapGS Σ}.
Definition eekv_record := (ee_record (low_record:=kv_record)).
Context `{!simplelogG (sm_record:=eekv_record) Σ}.
Context `{!kv64G Σ}.

Lemma wp_Start fname (confHost host:chan) γsys γsrv data :
  {{{
      "#Hhost" ∷ is_pb_host (pb_record:=eekv_record) host γsys γsrv ∗
      "#HconfHost" ∷ config_protocol_proof.is_pb_config_host confHost γsys ∗
      "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash (own_Server_ghost_f γsys γsrv) data)
                  (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv) data') ∗

      (* FIXME: collect these invariants *)
      "#Hsys" ∷ is_repl_inv γsys.(s_pb) ∗
      "#Hhelping" ∷ is_helping_inv γsys ∗
      "#HpreInv" ∷ is_preread_inv γsys.(s_pb) γsys.(s_prelog) γsys.(s_reads) ∗
      "#HisConfHost" ∷ config_protocol_proof.is_pb_config_host host γsys
  }}}
    Start #(LitString fname) #(host:u64) #(confHost:u64)
  {{{
        RET #(); True
  }}}
.
Proof using Type*.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_MakeKVStateMachine).
  iIntros (??) "[#His1 Hown]".
  wp_apply (wp_MakeEEKVStateMachine with "[Hown]").
  {
    iFrame.
    iFrame "His1".
  }
  iIntros (??) "[#His2 Hown]".
  wp_apply (wp_MakePbServer (sm_record:=eekv_record) with "[$Hown $Hfile_ctx]").
  { iFrame "#". }
  iIntros (?) "His".
  wp_pures.
  wp_apply (pb_start_proof.wp_Server__Serve with "[$]").
  wp_pures.
  by iApply "HΦ".
Qed.

Context `{!erpcG Σ (list u8)}.
Definition eekv_inv γ γkv : iProp Σ :=
  inv stateN (∃ ops, own_log γ ops ∗ own_kvs γkv ops).

Definition own_Clerk ck γkv : iProp Σ :=
  ∃ (eeCk:loc) γlog,
    "Hcl" ∷ ck ↦[kvee.Clerk :: "cl"] #eeCk ∗
    "#Hkvinv" ∷ kv_inv γlog γkv ∗
    "Hownck" ∷ eesm_proof.own_Clerk eeCk γlog
.

Definition is_kv_config confHost γkv : iProp Σ :=
  ∃ γpb γerpc γlog,
    "#Hee_inv" ∷ is_ee_inv γpb γlog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "#Hkv_inv" ∷ kv_inv γlog γkv ∗
    "#Hconf" ∷ is_pb_sys_host confHost γpb
.

Lemma wp_MakeClerk γkv confHost :
  {{{
      is_kv_config confHost γkv
  }}}
    kvee.MakeClerk #confHost
  {{{
        ck, RET #ck; own_Clerk ck γkv
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (eesm_proof.wp_MakeClerk with "[]").
  { iFrame "#". }
  iIntros (?) "Hck".
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".
  iApply "HΦ".
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_Clerk__Put ck γkv key val_sl value :
⊢ {{{ own_Clerk ck γkv ∗ is_slice_small val_sl byteT 1 value }}}
  <<< ∀∀ old_value, kv_ptsto γkv key old_value >>>
    Clerk__Put #ck #key (slice_val val_sl) @ (↑pbN ∪ ↑prophReadN ∪ ↑eeN ∪ ↑stateN)
  <<< kv_ptsto γkv key value >>>
  {{{ RET #(); own_Clerk ck γkv }}}.
Proof.
  iIntros "%Φ !# [Hck Hval_sl] Hupd".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_EncodePutArgs with "[$Key $Val $Hval_sl]").
  iIntros (putEncoded put_sl) "[%Henc Henc_sl]".
  wp_loadField.
  wp_apply (wp_Clerk__ApplyExactlyOnce with "Hownck Henc_sl").
  { done. }
  iInv "Hkvinv" as ">Hown" "Hclose".

  (* make this a separate lemma? *)
  iMod (fupd_mask_subseteq _) as "Hmaskclose".
  2: iMod "Hupd".
  1:{ eauto 20 with ndisj. } (* FIXME: increase search depth on solve_ndisj? *)

  iModIntro.
  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".

  rewrite /kv_record /=.
  iExists _. iSplitL "Hlog".
  { iExactEq "Hlog".
    Set Printing All.
    Print eekv_inv.
    repeat f_equal.
  }
  iIntros "Hlog".

  iMod (ghost_map_update (value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iMod "Hmaskclose" as "_".
  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame.
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl. rewrite insert_union_l.
    iFrame.
  }
  iModIntro.
  iIntros (?) "Hsl Hck".
  wp_pures.
  iApply "HH".
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_Clerk__Get ck γkv key :
⊢ {{{ own_Clerk ck γkv }}}
  <<< ∀∀ value, kv_ptsto γkv key value >>>
    Clerk__Get #ck #key @ (↑pbN ∪ ↑eeN ∪ ↑stateN)
  <<< kv_ptsto γkv key value >>>
  {{{ reply_sl, RET (slice_val reply_sl); own_Clerk ck γkv ∗ is_slice_small reply_sl byteT 1 value }}}.
Proof.
  iIntros "%Φ !# Hck Hupd".
  wp_lam.
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_EncodeGetArgs with "[//]").
  iIntros (getEncoded get_sl) "[%Henc Henc_sl]".
  wp_loadField.
  wp_apply (wp_Clerk__ApplyExactlyOnce with "Hownck Henc_sl").
  { done. }
  iInv "Hkvinv" as ">Hown" "Hclose".

  (* make this a separate lemma? *)
  iMod (fupd_mask_subseteq _) as "Hmaskclose".
  2: iMod "Hupd".
  1:{ solve_ndisj. }

  iModIntro.

  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".
  iExists _; iFrame "Hlog".
  iIntros "Hlog".

  iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.

  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iMod "Hmaskclose" as "_".
  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame "Hlog".
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl.
    iFrame.
  }
  iModIntro.
  iIntros (?) "Hsl Hck".
  iApply "HH".
  iSplitR "Hck".
  { repeat iExists _. iFrame "∗#". }
  { rewrite /kv_record//=. move:Hlook.
    rewrite lookup_union.
    destruct (compute_state ops !! key) as [x|]; simpl.
    - rewrite map.union_with_Some_l. intros [= ->]. done.
    - rewrite map.union_with_Some_r lookup_gset_to_gmap option_guard_True.
      2:{ apply elem_of_fin_to_set. }
      intros [= ->]. done. }
Qed.

End global_proof.
