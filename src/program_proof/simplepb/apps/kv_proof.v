From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kv64.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.simplepb Require Import pb_apply_proof clerk_proof.

Section proof.

Inductive kv64Op :=
  | putOp : u64 → list u8 → kv64Op
  | getOp : u64 → kv64Op
.

Definition apply_op (state:gmap u64 (list u8)) (op:kv64Op) :=
  match op with
    | getOp _ => state
    | putOp k v => <[k:=v]> state
  end
.

Definition compute_state ops : gmap u64 (list u8) :=
  foldl apply_op ∅ ops.

Definition compute_reply ops op : (list u8) :=
  match op with
    | getOp k => default [] ((compute_state ops) !! k)
    | putOp k v => []
  end
.

Definition encode_op op : list u8 :=
  match op with
    | getOp k => [U8 1] ++ u64_le k
    | putOp k v => [U8 0] ++ u64_le k ++ v
  end
.

Instance op_eqdec : EqDecision kv64Op.
Admitted.

Definition pb_record : PBRecord :=
  {|
    pb_OpType := kv64Op ;
    pb_has_op_encoding := λ op_bytes op, encode_op op = op_bytes ;
    pb_has_snap_encoding := λ snap_bytes ops , True ;
    pb_compute_reply :=  compute_reply ;
  |}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
(* Notation compute_reply := (pb_compute_reply pb_record). *)
Notation pbG := (pbG (pb_record:=pb_record)).
Notation is_ApplyFn := (is_ApplyFn (pb_record:=pb_record)).

Context `{!heapGS Σ}.

Lemma wp_EncodePutArgs (args_ptr:loc) (key:u64) val val_sl :
  {{{
      "Hargs_key" ∷ args_ptr ↦[kv64.PutArgs :: "Key"] #key ∗
      "Hargs_val" ∷ args_ptr ↦[kv64.PutArgs :: "Val"] (slice_val val_sl) ∗
      "Hargs_val_sl" ∷ is_slice_small val_sl byteT 1 (val)
  }}}
    kv64.EncodePutArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_op_encoding enc (putOp key val)⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_loadField.
  wp_apply (wp_slice_len).
Admitted.

Lemma wp_EncodeGetArgs (key:u64) :
  {{{
        True
  }}}
    kv64.EncodeGetArgs #key
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_op_encoding enc (getOp key)⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
Admitted.

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

Context `{!config_proof.configG Σ}.

Definition own_Clerk γ ck : iProp Σ :=
  ∃ (pb_ck:loc) γsys,
    "Hown_ck" ∷ own_Clerk pb_ck γsys ∗
    "#Hpb_ck" ∷ readonly (ck ↦[kv64.Clerk :: "cl"] #pb_ck) ∗
    "#His_inv" ∷ is_inv γ γsys
.

Context `{!urpc_proof.urpcregG Σ}.
Context `{!stagedG Σ}.

Lemma wp_Clerk__Put ck γ γkv key val_sl value Φ:
  sys_inv γ γkv -∗
  own_Clerk γ ck -∗
  is_slice val_sl byteT 1 value -∗
  □(|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (value) ={↑stateN,⊤∖↑pbN}=∗
    (own_Clerk γ ck -∗ Φ #()))) -∗
  WP Clerk__Put #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "#Hinv Hck Hval_sl #Hupd".
  wp_call.
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  iDestruct (is_slice_to_small with "Hval_sl") as "Hval_sl".
  wp_apply (wp_EncodePutArgs with "[$Key $Val $Hval_sl]").
  iIntros (putEncoded put_sl) "[%Henc Henc_sl]".
  wp_loadField.

  wp_apply (wp_Clerk__Apply with "Hown_ck His_inv Henc_sl").
  { done. }

  (* make this a separate lemma? *)
  iModIntro.
  iMod "Hupd".

  iInv "Hinv" as ">Hown" "Hclose".
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
  iExists _, _.
  iFrame "∗#".
  iModIntro.
  done.
Qed.

(* FIXME: copy/paste from old state_proof. *)

End proof.
