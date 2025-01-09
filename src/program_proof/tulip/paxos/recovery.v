From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip.paxos Require Import base.

Definition execute_paxos_extend st ents :=
  match st with
  | PaxosState termc terml lsnc ledger =>
      PaxosState termc terml lsnc (ledger ++ ents)
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

(* Definition encode_paxos_extend (ents : ledger) : list u8. *)

(* Definition encode_paxos_append (ent : string) : list u8. *)

(* Definition encode_paxos_prepare (term : u64) : list u8. *)

(* Definition encode_paxos_advance (term lsn : u64) (ents : ledger) : list u8. *)

(* Definition encode_paxos_accept (lsn : u64) (ents : ledger) : list u8. *)

(* Definition encode_paxos_expand (lsn : u64) : list u8. *)

(* Definition encode_paxos_cmd c := *)
(*   match c with *)
(*   | CmdPaxosExtend ents => encode_paxos_extend ents *)
(*   | CmdPaxosPrepare term => encode_paxos_prepare term *)
(*   | CmdPaxosAdvance term lsn ents => encode_paxos_advance term lsn ents *)
(*   | CmdPaxosAccept lsn ents => encode_paxos_accept lsn ents *)
(*   | CmdPaxosExpand lsn => encode_paxos_expand lsn *)
(*   end. *)

(* Definition encode_paxos_cmds_step p c := *)
(*   p ++ encode_paxos_cmd c. *)

Definition encode_paxos_cmds (cmds : list pxcmd) (data : list u8) := True.
  (* foldl encode_paxos_cmds_step [] cmds. *)
