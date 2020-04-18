(* copied from an earlier version from mit-plv/coqutil:

https://github.com/mit-plv/coqutil/blob/f3209a5b2c22eb36c3c1a8688b2a18b0d40fd476/src/coqutil/Word/LittleEndian.v
 *)
From Coq Require Import ZArith.ZArith.
From coqutil Require Import Z.Lia.
From coqutil Require Import Word.Interface Datatypes.HList Datatypes.PrimitivePair.
From coqutil Require Import Word.Properties.
From coqutil Require Import Z.bitblast.
Local Set Universe Polymorphism.

Local Open Scope Z_scope.

Section LittleEndian.
  Context {byte: word 8}.

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (word.unsigned (pair._1 bs))
                             (Z.shiftl (combine n (pair._2 bs)) 8)
    end.

  Fixpoint split (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (word.of_Z w) (split n (Z.shiftr w 8))
    end.

  Lemma combine_split {ok : word.ok byte} (n : nat) (z : Z) :
    combine n (split n z) = z mod 2 ^ (Z.of_nat n * 8).
  Proof.
    revert z; induction n.
    - cbn. intros. rewrite Z.mod_1_r. trivial.
    - cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      erewrite IHn; clear IHn.
      rewrite word.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold word.wrap.
      rewrite <-! Z.land_ones by blia.
      Z.bitblast.
  Qed.

  Lemma split_combine {ok : word.ok byte} (n: nat) bs :
    split n (combine n bs) = bs.
  Proof.
    revert bs; induction n.
    - destruct bs. reflexivity.
    - destruct bs; cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      specialize (IHn _2).
      f_equal.
      { eapply Properties.word.unsigned_inj.
        rewrite word.unsigned_of_Z, <-Properties.word.wrap_unsigned; cbv [word.wrap].
        Z.bitblast; cbn; subst.
        rewrite (Z.testbit_neg_r _ (i-8)) by blia.
        Z.bitblast_core. }
      { rewrite <-IHn.
        rewrite combine_split.
        f_equal.
        rewrite <-word.wrap_unsigned.
        Z.bitblast; subst; cbn.
        rewrite <-IHn.
        rewrite combine_split.
        Z.bitblast_core. }
  Qed.

End LittleEndian.

Arguments combine: simpl never.
Arguments split: simpl never.
