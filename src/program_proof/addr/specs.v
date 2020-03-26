From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.Helpers Require Import GenHeap.
From Perennial.goose_lang.lib Require Import struct.

From Goose.github_com.mit_pdos.goose_nfsd Require Import addr.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Record addr := {
  addrBlock : u64;
  addrOff : u64;
}.

Global Instance addr_eq_dec : EqDecision addr.
Proof.
  solve_decision.
Defined.

Global Instance addr_finite : Countable addr.
Proof.
  refine (inj_countable'
            (fun a => (a.(addrBlock), a.(addrOff)))
            (fun '(b, o) => Build_addr b o) _);
    by intros [].
Qed.

Definition addr2val (a : addr) : val :=
  (#a.(addrBlock), (#a.(addrOff), #())).

Definition addr2flat (a : addr) : u64 :=
  int.val a.(addrBlock) * block_bytes * 8 + int.val a.(addrOff).

Definition valid_addr (a : addr) : Prop :=
  int.val a.(addrOff) < block_bytes*8 ∧
  int.val a.(addrBlock) * block_bytes * 8 < 2^64.

Set Implicit Arguments.

Section flatid2addr.

  Variable (T : Type).

  Definition flatid_addr_map (fm : gmap u64 T) (am : gmap addr T) : Prop :=
    ∀ (a : addr) (v : T),
      valid_addr a ->
      am !! a = Some v <-> fm !! (addr2flat a) = Some v.

  Theorem flatid_addr_lookup_u64 fm am a v :
    flatid_addr_map fm am ->
    valid_addr a ->
    fm !! (addr2flat a) = Some v ->
    am !! a = Some v.
  Proof.
    unfold flatid_addr_map; intros.
    apply H; eauto.
  Qed.

  Theorem flatid_addr_lookup_addr fm am a v :
    flatid_addr_map fm am ->
    valid_addr a ->
    am !! a = Some v ->
    fm !! (addr2flat a) = Some v.
  Proof.
    unfold flatid_addr_map; intros.
    apply H; eauto.
  Qed.

  Theorem flatid_addr_insert fm am a v :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (<[addr2flat a := v]> fm) (<[a := v]> am).
  Proof.
  Admitted.

  Theorem flatid_addr_delete fm am a :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (delete (addr2flat a) fm) (delete a am).
  Proof.
  Admitted.

  Theorem flatid_addr_empty :
    flatid_addr_map ∅ ∅.
  Proof.
    unfold flatid_addr_map; simpl; intros.
    repeat rewrite lookup_empty.
    eauto.
  Qed.

End flatid2addr.

End heap.
