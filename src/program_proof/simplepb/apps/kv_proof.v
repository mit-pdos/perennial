From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kv64.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.

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

Definition is_Clerk γ ck : iProp Σ :=
  ∃ (pb_ck:loc) γsys γsrv,
    "#Hpb_ck" ∷ readonly (ck ↦[Clerk :: "cl"] #pb_ck) ∗
    "#His_ck" ∷ is_Clerk pb_ck γsys γsrv ∗
    "#His_inv" ∷ is_inv γ γsys
.

Context `{!urpc_proof.urpcregG Σ}.
Context `{!stagedG Σ}.

Lemma wp_Clerk__FetchAndAppend ck γ γkv key val_sl value Φ:
  sys_inv γ γkv -∗
  is_Clerk γ ck -∗
  is_slice val_sl byteT 1 value -∗
  □((|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (value) ={↑stateN,⊤∖↑pbN}=∗
    (∀ reply_sl, is_slice_small reply_sl byteT 1 old_value -∗
      Φ (#(U64 0), slice_val reply_sl)%V ))) ∗
  (∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ))-∗
  WP Clerk__Put #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "#Hinv #Hck Hval_sl #Hupd".
  wp_call.
  wp_pures.
Admitted.

(* FIXME: copy/paste from old state_proof. *)

End proof.
