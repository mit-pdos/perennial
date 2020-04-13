From stdpp Require Export namespaces.
From Coq Require Import Min.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree namespace_map.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic Require gen_heap.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

(* This class encodes how to represent an address into a combination of
   a "block id" and an integer offset into that block *)
Class BlockAddr L1 L2 `{Countable L1, Countable L2} : Type :=
  { addr_decode : L1 → (L2 * Z);
    addr_encode : (L2 * Z) → L1;
    addr_decode_encode : ∀ x, addr_decode (addr_encode x) = x;
    addr_encode_decode : ∀ x, addr_encode (addr_decode x) = x }.

Section block_addr_defs.
  Context `{BlockAddr L1 L2}.
  Local Open Scope Z.

  Definition addr_id (x: L1) : L2 := fst (addr_decode x).
  Definition addr_offset (x: L1) : Z := snd (addr_decode x).

  Definition addr_base (x: L1) := addr_encode (addr_id x, 0%Z).
  Definition addr_plus_off (x: L1) (z: Z) :=
    addr_encode (addr_id x, (addr_offset x + z)%Z).

  Lemma addr_encode_decode' (x: L1) :
    addr_encode (addr_id x, addr_offset x) = x.
  Proof.
    rewrite /addr_id/addr_offset -{3}(addr_encode_decode x).
    destruct (addr_decode x) => //=.
  Qed.

  Lemma addr_plus_off_0 (x: L1) :
    addr_plus_off x 0%Z = x.
  Proof. rewrite /addr_plus_off Z.add_0_r. apply addr_encode_decode'. Qed.

  Lemma addr_plus_off_decode (x: L1) :
    x = addr_plus_off (addr_base x) (addr_offset x).
  Proof.
    rewrite /addr_plus_off/addr_base/addr_id//= /addr_offset ?addr_decode_encode //=.
    rewrite Z.add_0_l addr_encode_decode' //.
  Qed.

  Lemma addr_offset_of_plus (l: L1) off:
    addr_offset (addr_plus_off l off) = addr_offset l + off.
  Proof. rewrite /addr_offset/addr_plus_off addr_decode_encode //=. Qed.

  Lemma addr_id_of_plus (l: L1) off:
    addr_id (addr_plus_off l off) = addr_id l.
  Proof. rewrite /addr_base/addr_id/addr_plus_off addr_decode_encode //=. Qed.

  Lemma addr_base_of_plus (l: L1) off:
    addr_base (addr_plus_off l off) = addr_base l.
  Proof. rewrite /addr_base addr_id_of_plus //=. Qed.

  Lemma addr_component_eq l1 l2:
    addr_id l1 = addr_id l2 → addr_offset l1 = addr_offset l2 → l1 = l2.
  Proof.
    intros Heq1 Heq2.
    rewrite -(addr_encode_decode' l1).
    rewrite -(addr_encode_decode' l2).
    congruence.
  Qed.

  Lemma addr_plus_plus (l: L1) off1 off2:
    addr_plus_off (addr_plus_off l off1) off2 = addr_plus_off l (off1 + off2).
  Proof.
    apply addr_component_eq.
    - rewrite !addr_id_of_plus //=.
    - rewrite !addr_offset_of_plus //=. lia.
  Qed.

  Instance addr_encode_inj : Inj eq eq (addr_encode).
  Proof.
    rewrite /Inj => x y Heq. apply (f_equal addr_decode) in Heq.
    by rewrite ?addr_decode_encode in Heq.
  Qed.

  Global Instance addr_plus_off_inj l : Inj eq eq (addr_plus_off l).
  Proof.
    rewrite /Inj => x y. rewrite /addr_plus_off => Heq.
    apply (inj addr_encode) in Heq. inversion Heq; subst.
    lia.
  Qed.

  Lemma addr_offset_of_base (x: L1):
    addr_offset (addr_base x) = 0%Z.
  Proof.
    rewrite /addr_offset/addr_base addr_decode_encode //=.
  Qed.

  Lemma addr_plus_Sn l n : addr_plus_off l (S n) = addr_plus_off (addr_plus_off l 1) n.
  Proof. rewrite addr_plus_plus; f_equal; lia. Qed.

  Lemma addr_plus_eq_inv l i : addr_plus_off l i = l -> i = 0.
  Proof. rewrite -{2}(addr_plus_off_0 l). apply addr_plus_off_inj. Qed.

  Lemma addr_plus_ne l i : (0 < i)%Z -> addr_plus_off l i <> l.
  Proof. intros ? Heq%addr_plus_eq_inv; lia. Qed.

  Fixpoint heap_array {V} (l : L1) (vs : list V) : gmap L1 V :=
    match vs with
    | [] => ∅
    | v :: vs' => {[l := v]} ∪ heap_array (addr_plus_off l 1) vs'
    end.

  Lemma heap_array_singleton V l (v:V) : heap_array l [v] = {[l := v]}.
  Proof. by rewrite /heap_array right_id. Qed.

  Open Scope Z.

  Lemma heap_array_lookup V l (vs: list V) w k :
    heap_array l vs !! k = Some w ↔
                                ∃ j, 0 ≤ j ∧ k = addr_plus_off l j ∧ vs !! (Z.to_nat j) = Some w.
  Proof.
    revert k l; induction vs as [|v' vs IH]=> l' l /=.
    { rewrite lookup_empty. naive_solver lia. }
    rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
    - intros [[-> Heq] | (Hl & j & ? & -> & ?)].
      { inversion Heq; subst. exists 0. rewrite addr_plus_off_0. naive_solver lia. }
      exists (1 + j)%Z. rewrite addr_plus_plus !Z.add_1_l Z2Nat.inj_succ; auto with lia.
    - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
      { rewrite addr_plus_off_0; eauto. }
      right. split.
      { rewrite -{1}(addr_plus_off_0 l). intros ?%(inj (addr_plus_off _)); lia. }
      assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
      { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
      rewrite Hj /= in Hil.
      exists (j - 1)%Z. rewrite addr_plus_plus Z.add_sub_assoc Z.add_simpl_l.
      auto with lia.
  Qed.

  Lemma heap_array_map_disjoint {V} (h : gmap L1 V) (l : L1) (vs : list V) :
    (∀ i, (0 ≤ i) → (i < length vs) → h !! (addr_plus_off l i) = None) →
    (heap_array l vs) ##ₘ h.
  Proof.
    intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
    intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
    move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
  Qed.

  Lemma heap_array_fmap V1 V2 l (f: V1 → V2) (vs: list V1) :
    fmap f (heap_array l vs) = heap_array l (fmap f vs).
  Proof.
    revert l. induction vs; simpl; intros.
    - rewrite fmap_empty //=.
    - rewrite -insert_union_singleton_l fmap_insert insert_union_singleton_l IHvs //=.
  Qed.

End block_addr_defs.
