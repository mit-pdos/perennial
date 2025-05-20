From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip.paxos Require Import base.
From Perennial.program_proof.tulip Require Import encode.
From Perennial.program_proof.rsm Require Import serialize.

(* Executing. *)

Definition execute_paxos_extend st ents :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      PaxosState termc terml lsnc (ledger ++ ents)
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_append st ent :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      PaxosState termc terml lsnc (ledger ++ [ent])
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_prepare st term :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      PaxosState term terml lsnc ledger
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_advance st term lsn ents :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      if decide (lsn ≤ length ledger)%nat
      then PaxosState termc term lsnc (take lsn ledger ++ ents)
      else PaxosStuck
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_accept st lsn ents :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      if decide (lsn ≤ length ledger)%nat
      then PaxosState termc terml lsnc (take lsn ledger ++ ents)
      else PaxosStuck
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_expand st lsn :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      PaxosState termc terml lsn ledger
  | PaxosStuck => PaxosStuck
  end.

Definition execute_paxos_cmd st c :=
  match c with
  | CmdPaxosExtend ents => execute_paxos_extend st ents
  | CmdPaxosAppend ent => execute_paxos_append st ent
  | CmdPaxosPrepare term => execute_paxos_prepare st term
  | CmdPaxosAdvance term lsn ents => execute_paxos_advance st term lsn ents
  | CmdPaxosAccept lsn ents => execute_paxos_accept st lsn ents
  | CmdPaxosExpand lsn => execute_paxos_expand st lsn
  end.

Definition init_pxst := PaxosState O O O [].

Definition execute_paxos_cmds cmds :=
  foldl execute_paxos_cmd init_pxst cmds.

Lemma execute_paxos_cmds_unfold cmds :
  foldl execute_paxos_cmd init_pxst cmds = execute_paxos_cmds cmds.
Proof. done. Qed.

Lemma execute_paxos_cmds_snoc cmds cmd :
  execute_paxos_cmds (cmds ++ [cmd]) = execute_paxos_cmd (execute_paxos_cmds cmds) cmd.
Proof. by rewrite /execute_paxos_cmds foldl_snoc. Qed.

Lemma foldl_execute_paxos_cmd_from_stuck cmds :
  foldl execute_paxos_cmd PaxosStuck cmds = PaxosStuck.
Proof.
  induction cmds as [| cmd cmds]; first done.
  simpl.
  by destruct cmd.
Qed.

Lemma execute_paxos_cmds_prefix_not_stuck cmdsp cmds :
  prefix cmdsp cmds ->
  execute_paxos_cmds cmds ≠ PaxosStuck ->
  execute_paxos_cmds cmdsp ≠ PaxosStuck.
Proof.
  intros Hprefix Hexec.
  intros Hstuck.
  destruct Hprefix as [cmdstl Hprefix].
  rewrite Hprefix /execute_paxos_cmds foldl_app execute_paxos_cmds_unfold Hstuck in Hexec.
  by rewrite foldl_execute_paxos_cmd_from_stuck in Hexec.
Qed.

Lemma execute_paxos_advance_safely_trimmed st term lsn ents :
  execute_paxos_advance st term lsn ents ≠ PaxosStuck ->
  match st with
  | PaxosState _ _ _ ledger => (lsn ≤ length ledger)%nat
  | _ => False
  end.
Proof.
  intros Hns.
  destruct st; last done.
  simpl in Hns.
  by case_decide.
Qed.

Lemma execute_paxos_accept_safely_trimmed st lsn ents :
  execute_paxos_accept st lsn ents ≠ PaxosStuck ->
  match st with
  | PaxosState _ _ _ ledger => (lsn ≤ length ledger)%nat
  | _ => False
  end.
Proof.
  intros Hns.
  destruct st; last done.
  simpl in Hns.
  by case_decide.
Qed.

(* Encoding. *)

Definition encode_paxos_extend (ents : ledger) : list u8 :=
  u64_le (U64 0) ++ encode_strings ents.

Definition encode_paxos_append (ent : byte_string) : list u8 :=
  u64_le (U64 1) ++ encode_string ent.

Definition encode_paxos_prepare (term : u64) : list u8 :=
  u64_le (U64 2) ++ u64_le term.

Definition encode_paxos_advance (term lsn : u64) (ents : ledger) : list u8 :=
  u64_le (U64 3) ++ u64_le term ++ u64_le lsn ++ encode_strings ents.

Definition encode_paxos_accept (lsn : u64) (ents : ledger) : list u8 :=
  u64_le (U64 4) ++ u64_le lsn ++ encode_strings ents.

Definition encode_paxos_expand (lsn : u64) : list u8 :=
  u64_le (U64 5) ++ u64_le lsn.

Hint Unfold encode_paxos_extend encode_paxos_append encode_paxos_prepare
  encode_paxos_advance encode_paxos_accept encode_paxos_expand : len.

Definition encode_paxos_cmd c :=
  match c with
  | CmdPaxosExtend ents => encode_paxos_extend ents
  | CmdPaxosAppend ent => encode_paxos_append ent
  | CmdPaxosPrepare term => encode_paxos_prepare term
  | CmdPaxosAdvance term lsn ents => encode_paxos_advance term lsn ents
  | CmdPaxosAccept lsn ents => encode_paxos_accept lsn ents
  | CmdPaxosExpand lsn => encode_paxos_expand lsn
  end.

Definition encode_paxos_cmds (cmds : list pxcmd) :=
  serialize encode_paxos_cmd cmds.

Lemma encode_paxos_cmds_nil_inv cmds :
  encode_paxos_cmds cmds = [] ->
  cmds = [].
Proof.
  intros Henc.
  destruct cmds as [| c tl]; first done.
  exfalso.
  rewrite /encode_paxos_cmds /= serialize_cons in Henc.
  apply (f_equal length) in Henc.
  revert Henc.
  destruct c; simpl in *; len.
Qed.

Lemma encode_paxos_cmds_snoc cmds cmd :
  encode_paxos_cmds (cmds ++ [cmd]) =
  encode_paxos_cmds cmds ++ encode_paxos_cmd cmd.
Proof. by rewrite /encode_paxos_cmds serialize_snoc. Qed.
