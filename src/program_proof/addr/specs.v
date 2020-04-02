From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.program_proof Require Import proof_prelude.
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

Definition addr2flat_z (a : addr) : Z :=
  int.val a.(addrBlock) * block_bytes * 8 + int.val a.(addrOff).

Definition addr2flat (a : addr) : u64 :=
  addr2flat_z a.

Definition valid_addr (a : addr) : Prop :=
  int.val a.(addrOff) < block_bytes*8 ∧
  int.val a.(addrBlock) * block_bytes < 2^64 ∧
  int.val a.(addrBlock) * block_bytes * 8 < 2^64 ∧
  addr2flat_z a < 2^64.

Theorem addr2flat_z_eq `(valid_addr a0) `(valid_addr a1) :
  addr2flat a0 = addr2flat a1 →
  addr2flat_z a0 = addr2flat_z a1.
Proof.
  destruct a0, a1.
  unfold addr2flat, valid_addr, addr2flat_z, block_bytes in *.
  simpl in *; intuition.
  apply (f_equal int.val) in H.
  revert H.
  word.
Qed.

Theorem addr2flat_eq `(valid_addr a0) `(valid_addr a1) :
  addr2flat a0 = addr2flat a1 →
  a0 = a1.
Proof.
  intros.
  eapply addr2flat_z_eq in H; eauto.
  destruct a0, a1.
  unfold valid_addr, addr2flat_z, block_bytes in *.
  simpl in *.
  intuition.
  replace addrOff0 with addrOff1 in *.
  { replace addrBlock0 with addrBlock1; auto.
    assert (int.val addrBlock0 * Z.to_nat 4096 * 8 = int.val addrBlock1 * Z.to_nat 4096 * 8) by lia.
    word.
  }
  word.
Qed.

Theorem addr2flat_ne `(valid_addr a0) `(valid_addr a1) :
  a0 ≠ a1 ->
  addr2flat a0 ≠ addr2flat a1.
Proof.
  intros; intuition.
  apply H.
  eapply addr2flat_eq; eauto.
Qed.

Set Implicit Arguments.

Section flatid2addr.

  Variable (T : Type).

  Definition flatid_addr_map (fm : gmap u64 T) (am : gmap addr T) : Prop :=
    ∀ (a : addr) (v : T),
      valid_addr a ->
      am !! a = Some v <-> fm !! (addr2flat a) = Some v.

  Theorem flatid_addr_lookup fm am a :
    flatid_addr_map fm am ->
    valid_addr a ->
    fm !! (addr2flat a) = am !! a.
  Proof.
    unfold flatid_addr_map; intros.
    destruct (am !! a) eqn:Heq.
    - apply H; eauto.
    - destruct (fm !! addr2flat a) eqn:Heq2; eauto.
      apply H in Heq2; eauto. congruence.
  Qed.

  Theorem flatid_addr_insert fm am a v :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (<[addr2flat a := v]> fm) (<[a := v]> am).
  Proof.
    rewrite /flatid_addr_map /valid_addr; intros.
    destruct (decide (a = a0)); subst.
    - repeat rewrite lookup_insert; eauto.
    - rewrite -> lookup_insert_ne by eauto.
      rewrite -> lookup_insert_ne by (apply addr2flat_ne; eauto).
      eauto.
  Qed.

  Theorem flatid_addr_delete fm am a :
    flatid_addr_map fm am ->
    valid_addr a ->
    flatid_addr_map (delete (addr2flat a) fm) (delete a am).
  Proof.
    rewrite /flatid_addr_map /valid_addr; intros.
    destruct (decide (a = a0)); subst.
    - repeat rewrite lookup_delete; eauto.
    - rewrite -> lookup_delete_ne by eauto.
      rewrite -> lookup_delete_ne by (apply addr2flat_ne; eauto).
      eauto.
  Qed.

  Theorem flatid_addr_empty :
    flatid_addr_map ∅ ∅.
  Proof.
    unfold flatid_addr_map; simpl; intros.
    repeat rewrite lookup_empty.
    eauto.
  Qed.

End flatid2addr.


Hint Unfold block_bytes : word.
Hint Unfold valid_addr : word.
Hint Unfold addr2flat : word.
Hint Unfold addr2flat_z : word.

Theorem wp_Addr__Flatid a :
  {{{
    ⌜ valid_addr a ⌝
  }}}
    Addr__Flatid (addr2val a)
  {{{
    v, RET #v; ⌜ v = addr2flat a ⌝
  }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  iApply "HΦ".
  iPureIntro.

  word_cleanup.
  rewrite ?word.unsigned_mul. (* XXX why is this needed? *)
  word_cleanup.
Qed.

End heap.
