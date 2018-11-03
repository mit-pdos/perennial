Require Import Omega.
Require Import RelationClasses.
Require Import List.
Require Import Helpers.

Set Implicit Arguments.


(** * Disk model.

    This file defines our model of a disk. We represent a disk as a list
    of 1KB blocks and provide functions to read and update disks, as
    well as theorems about these operations. In order to describe disks,
    we first provide a model of byte sequences.
 *)

(** * Model of bytes.

    In our lab assignments, we will model disks as consisting of
    blocks, which are in turn composed of bytes.  Here, we define
    a notion of a byte array: the type of an array of [n] bytes
    will be [bytes n].

    There's one unusual aspect of how we model bytes: instead of
    defining the bytes type in Coq, we simply add it as an [Axiom]. This
    means we are not providing a Coq (Gallina) implementation of bytes,
    and instead we are telling Coq to assume that there exists something
    called [bytes], and there exist other functions that manipulate
    bytes that we define here as well (like [bytes_dec] to decide if two
    byte arrays are equal).

    When we generate executable code by extracting our Coq (Gallina)
    code into Haskell, we will be required to provide a Haskell
    implementation of any such [Axiom].  This correspondence is
    made below, using [Extract Constant], and we (as developers)
    are responsible for making sure any axioms we state (like
    [bsplit_bappend]) are true of our Haskell implementations.
  *)

Axiom bytes : nat -> Type.

Axiom bytes_dec : forall n, EqualDec (bytes n).
Existing Instance bytes_dec.

(**
    Two "initial" byte values: an all-zero array, [bytes0], and
    an all-ones array, [bytes1].  We also promise that all-zero
    and all-ones arrays are different, as long as there's at least
    one element.
  *)

Axiom bytes0 : forall n, bytes n.
Axiom bytes1 : forall n, bytes n.
Axiom bytes_differ : forall n, n > 0 -> bytes0 n <> bytes1 n.

Definition bnull : bytes 0 := bytes0 0.

Axiom bappend : forall n1 n2, bytes n1 -> bytes n2 -> bytes (n1+n2).
Axiom bsplit : forall n1 n2, bytes (n1+n2) -> bytes n1 * bytes n2.
Arguments bsplit {n1 n2} bs.

Axiom bsplit_bappend : forall n1 n2 (b1 : bytes n1) (b2 : bytes n2), bsplit (bappend b1 b2) = (b1, b2).

Fixpoint bsplit_list {n} {m} : bytes (n * m) -> list (bytes m) :=
  match n with
  | O => fun _ => nil
  | S n' => fun (bs : bytes ((S n') * m)) =>
    let (this, rest) := bsplit bs in
    this :: bsplit_list rest
  end.

Extraction Language Haskell.

Extract Constant bytes => "Data.ByteString.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".

Extract Constant bappend => "(\_ _ bs1 bs2 -> Data.ByteString.append bs1 bs2)".
Extract Constant bsplit => "(\n1 _ bs -> Data.ByteString.splitAt (Prelude.fromIntegral n1) bs)".


(** * Model of blocks.

    We represent blocks as a byte array of a fixed size.

    We define the block size as a separate constant, [blockbytes], to avoid the
    literal constant [1024] reducing performance of proofs.
  *)

Definition blockbytes := 1024.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.

Theorem block0_block1_differ : block0 <> block1.
Proof.
  apply bytes_differ.
  unfold blockbytes.
  omega.
Qed.

Hint Resolve block0_block1_differ.

(** Mark [blockbytes] as opaque so that Coq doesn't expand it too eagerly.
  *)

Opaque blockbytes.


(** * Disk as a list of blocks.

    Now we can define our model of a disk: a list of blocks.
    A disk with zero blocks is an empty list, [nil].
  *)

Definition disk := list block.

Definition empty_disk : disk := nil.

(** We define three main operations on disks:

    - [diskGet d a] gets the contents of an address [a] in disk [d].
      It returns an [option block], which is either a block value [b]
      (represented by [Some b]), or [None] if [a] is past the end of
      the disk.

    - [diskSize] returns the size of the disk, which is just the length
      of the list representing the disk.

    - [diskUpd] writes to a disk.  Since Gallina is a functional language,
      we cannot update a disk "in-place", so instead [diskUpd] returns a
      new disk reflecting the write.  Specifically, [diskUpd d a b] returns
      a new disk with address [a] updated to block value [b], if [a] is
      in-bounds, or the original disk unchanged if [a] is out-of-bounds.
  *)

(** We address into disks with [addr], which is simply a [nat]. *)
Definition addr := nat.

(** Coq v8.6 has a minor bug in the [omega] tactic, which is helpful
    in solving simple arithmetic goals.  In particular, when we have
    arithmetic expressions that involve the [addr] type, [omega] gets
    confused because it doesn't see that [addr] is simply a wrapper
    for [nat].  This works around the bug, which should eventually be
    fixed by https://github.com/coq/coq/pull/876
  *)

Local Ltac omega_orig := omega.
Ltac omega := unfold addr in *; omega_orig.

Definition diskGet (d : disk) (a : addr) : option block :=
  nth_error d a.

Definition diskSize (d : disk) : nat := length d.

Fixpoint diskUpd d (a: addr) b : disk :=
  match d with
  | nil => nil
  | db :: drest =>
    match a with
    | O => b :: drest
    | S a' => db :: diskUpd drest a' b
    end
  end.

(** We also define another helper operation, [diskShrink], which takes
    a disk and drops the last block.  This will be helpful in the
    bad-block-remapping lab assignment.
  *)

Definition diskShrink (d : disk) : disk :=
  firstn (length d - 1) d.

(** Finally, we prove a variety of theorems about the behavior of these
    disk operations.
  *)

(** ** Theorems about diskGet *)

Theorem disk_inbounds_exists : forall a d,
    a < diskSize d ->
    exists b, diskGet d a = Some b.
Proof.
  unfold diskSize.
  intros.
  case_eq (diskGet d a); intros; eauto.
  apply nth_error_None in H0.
  omega.
Qed.

Theorem disk_inbounds_not_none : forall a d,
    a < diskSize d ->
    diskGet d a = None ->
    False.
Proof.
  unfold diskSize.
  intros.
  apply nth_error_None in H0.
  omega.
Qed.

Theorem disk_none_oob : forall a d,
    diskGet d a = None ->
    ~a < diskSize d.
Proof.
  intros.
  destruct (lt_dec a (diskSize d)); eauto.
  exfalso; eapply disk_inbounds_not_none; eauto.
Qed.

Theorem disk_oob_eq : forall d a,
    ~a < diskSize d ->
    diskGet d a = None.
Proof.
  unfold diskSize.
  induction d; simpl; intros.
  - induction a; eauto.
  - destruct a0; simpl.
    + omega.
    + eapply IHd. omega.
Qed.

Theorem disk_ext_eq : forall d d',
    (forall a, diskGet d a = diskGet d' a) ->
    d = d'.
Proof.
  induction d; simpl; intros.
  - destruct d'; simpl; intros; eauto.
    specialize (H 0); simpl in *.
    congruence.
  - destruct d'; simpl; intros.
    + specialize (H 0); simpl in *.
      congruence.
    + specialize (H 0) as H'; simpl in H'.
      f_equal; try congruence.
      eapply IHd; intros.
      specialize (H (S a0)); simpl in H.
      eauto.
Qed.

Theorem disk_ext_inbounds_eq : forall d d',
    diskSize d = diskSize d' ->
    (forall a, a < diskSize d -> diskGet d a = diskGet d' a) ->
    d = d'.
Proof.
  intros.
  apply disk_ext_eq; intros.
  destruct (lt_dec a (diskSize d)); eauto.
  rewrite ?disk_oob_eq by congruence; auto.
Qed.

(** ** Theorems about diskUpd *)

Theorem diskUpd_eq_some : forall d a b0 b,
    diskGet d a = Some b0 ->
    diskGet (diskUpd d a b) a = Some b.
Proof.
  induction d; simpl; eauto.
  - destruct a; simpl; intros; congruence.
  - destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_eq : forall d a b,
    a < diskSize d ->
    diskGet (diskUpd d a b) a = Some b.
Proof.
  intros.
  apply disk_inbounds_exists in H; deex.
  eauto using diskUpd_eq_some.
Qed.

Theorem diskUpd_size : forall d a b,
    diskSize (diskUpd d a b) = diskSize d.
Proof.
  induction d; simpl; eauto.
  destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_oob_eq : forall d a b,
    ~a < diskSize d ->
    diskGet (diskUpd d a b) a = None.
Proof.
  intros.
  apply disk_oob_eq.
  rewrite diskUpd_size; auto.
Qed.

Theorem diskUpd_neq : forall d a b a',
    a <> a' ->
    diskGet (diskUpd d a b) a' = diskGet d a'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl.
  - destruct a'; simpl; try omega; auto.
  - destruct a'; simpl; auto.
Qed.

Theorem diskUpd_none : forall d a b,
    diskGet d a = None ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *; try congruence.
  rewrite IHd; eauto.
Qed.

Theorem diskUpd_same : forall d a b,
    diskGet d a = Some b ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_twice : forall d a b b',
    diskUpd (diskUpd d a b) a b' = diskUpd d a b'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_oob_noop : forall d a b,
    ~a < diskSize d ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - omega.
  - rewrite IHd; auto; omega.
Qed.

(** ** Theorems about diskShrink *)

Theorem diskShrink_size : forall d,
    diskSize d <> 0 ->
    diskSize (diskShrink d) = diskSize d - 1.
Proof.
  unfold diskSize, diskShrink; intros.
  rewrite firstn_length.
  rewrite min_l; omega.
Qed.

Theorem diskShrink_preserves : forall d a,
    a <> diskSize (diskShrink d) ->
    diskGet (diskShrink d) a = diskGet d a.
Proof.
  unfold diskShrink.
  induction d; simpl; intros; auto.
  destruct d; simpl in *.
  - destruct a0; try omega; simpl.
    destruct a0; auto.
  - destruct a0; simpl; auto.
    replace (length d - 0) with (length d) in * by omega.
    rewrite <- IHd; auto.
Qed.

Theorem diskShrink_diskUpd_last : forall d a b,
    a >= diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskShrink d.
Proof.
  unfold diskShrink; intros.
  destruct (eq_nat_dec a (diskSize d - 1)); subst.
  - clear H.
    rewrite diskUpd_size; unfold diskSize.
    induction d; simpl; auto.
    destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by omega.
    f_equal; auto.
  - rewrite diskUpd_oob_noop by omega; auto.
Qed.

Theorem diskShrink_diskUpd_notlast : forall d a b,
    a < diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskUpd (diskShrink d) a b.
Proof.
  unfold diskShrink.
  induction d; simpl; auto; intros.
  destruct a0; simpl; auto.
  - destruct d; simpl; auto.
  - destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by omega.
    rewrite <- IHd by omega.
    destruct a0; simpl; try rewrite diskUpd_size; unfold diskSize;
      replace (length d - 0) with (length d) by omega; auto.
Qed.

Hint Rewrite diskUpd_size : disk_size.
Hint Rewrite diskShrink_size using solve [ auto || omega ] : disk_size.

(** We combine all of the above theorems into a hint database called "upd".
    This means that, when you type [autorewrite with upd] in some Coq proof,
    Coq will try to rewrite using all of the hints in that database.

    The [using] part of the hint tells Coq that all of the side conditions
    associated with the rewrite must be solved using the tactic specified
    in the [using] clause.  This prevents Coq from applying a rewrite rule
    if some side condition (like an address being out-of-bounds) cannot be
    immediately proven.
  *)

Local Ltac solve_disk_size :=
  solve [ autorewrite with disk_size; (auto || omega) ].

Hint Rewrite diskUpd_eq using solve_disk_size : upd.
Hint Rewrite disk_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using solve_disk_size : upd.
Hint Rewrite diskUpd_twice : upd.

Hint Rewrite diskShrink_size using solve_disk_size : upd.
Hint Rewrite diskShrink_preserves using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_last using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_notlast using solve_disk_size : upd.
