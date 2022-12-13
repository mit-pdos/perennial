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

From Perennial.program_proof.simplepb.apps Require Import eesm_proof kv_proof.

Section global_proof.

Context `{!heapGS Σ}.
Definition eekv_record := (ee_record (low_record:=kv_record)).
Context `{!simplelogG (sm_record:=eekv_record) Σ}.

Lemma wp_Start fname (host:chan) γsys γsrv data :
  {{{
      "#Hhost" ∷ is_pb_host host γsys γsrv ∗
      "#Hinv" ∷ sys_inv γsys ∗
      "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash (own_Server_ghost γsys γsrv) data)
                    (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash (own_Server_ghost γsys γsrv) data')
  }}}
    Start #(host:u64) #(LitString fname)
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_MakeKVStateMachine).
  iIntros (??) "[#His1 Hown]".
  wp_apply (wp_MakeEEKVStateMachine with "[Hown]").
  {
    iFrame "His1".
    iFrame.
  }
  iIntros (??) "[#His2 Hown]".
  wp_apply (wp_MakePbServer (sm_record:=eekv_record) with "Hinv [$His2 $Hown $Hfile_ctx]").
  iIntros (?) "His".
  wp_pures.
  wp_apply (pb_start_proof.wp_Server__Serve with "[$]").
  wp_pures.
  by iApply "HΦ".
Qed.

Notation own_oplog := (own_oplog (low_record:=kv_record)).

Context `{!kv64G Σ}.
Context `{!erpcG Σ (list u8)}.
Definition eekv_inv γ γkv : iProp Σ :=
  inv stateN (∃ ops, own_oplog γ ops ∗ own_kvs γkv ops).

Definition own_Clerk ck γkv : iProp Σ :=
  ∃ (eeCk:loc) γlog,
    "Hcl" ∷ ck ↦[kvee.Clerk :: "cl"] #eeCk ∗
    "#Hkvinv" ∷ kv_inv γlog γkv ∗
    "Hownck" ∷ eesm_proof.own_Clerk eeCk γlog
.

Lemma wp_Clerk__Put ck γkv key val_sl value Φ:
  own_Clerk ck γkv -∗
  is_slice_small val_sl byteT 1 value -∗
  (|={⊤∖↑pbN∖↑eeN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (value) ={↑stateN,⊤∖↑pbN∖↑eeN}=∗
    (own_Clerk ck γkv -∗ Φ #()))) -∗
  WP Clerk__Put #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "Hck Hval_sl Hupd".
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

  (* make this a separate lemma? *)
  iMod "Hupd".

  iInv "Hkvinv" as ">Hown" "Hclose".
  replace (↑_∖_) with (∅:coPset); last set_solver.
  iModIntro.

  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".
  iExists _; iFrame "Hlog".
  iIntros "Hlog".

  iMod (ghost_map_update (value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame.
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl.
    iFrame.
  }
  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iModIntro.
  iIntros (?) "Hsl Hck".
  wp_pures.
  iApply "HH".
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
Qed.

End global_proof.
