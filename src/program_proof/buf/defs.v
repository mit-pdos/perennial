Require Import Coq.Program.Equality.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


From Perennial.program_proof Require Import proof_prelude.

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.
Definition inode_to_vals {ext: ext_op} (i:inode_buf) : list val :=
  fmap b2val (vec_to_list i).

Hint Unfold inode_bytes : word.

Definition list_to_inode_buf (l: list u8) : inode_buf :=
  match decide (length l = inode_bytes) with
  | left H => eq_rect _ _ (list_to_vec l) _ H
  | _ => inhabitant
  end.

Lemma vec_to_list_to_vec_eq_rect A (l: list A) n (H: length l = n) :
  vec_to_list (eq_rect _ _ (list_to_vec l) _ H) = l.
Proof.
  rewrite <- H; simpl.
  rewrite vec_to_list_to_vec.
  auto.
Qed.

Theorem list_to_inode_buf_to_list l :
  length l = inode_bytes ->
  vec_to_list (list_to_inode_buf l) = l.
Proof.
  intros H.
  rewrite /list_to_inode_buf.
  rewrite decide_left.
  rewrite vec_to_list_to_vec_eq_rect; auto.
Qed.

Theorem inode_buf_list_inj l (i: inode_buf) :
  l = vec_to_list i →
  i = list_to_inode_buf l.
Proof.
  intros ->.
  apply vec_to_list_inj2.
  rewrite list_to_inode_buf_to_list //.
  rewrite vec_to_list_length //.
Qed.

Theorem inode_buf_to_list_to_inode_buf i :
  list_to_inode_buf (vec_to_list i) = i.
Proof.
  symmetry.
  apply inode_buf_list_inj.
  auto.
Qed.

Theorem list_to_inode_buf_to_vals l :
  length l = inode_bytes ->
  inode_to_vals (list_to_inode_buf l) = b2val <$> l.
Proof.
  intros H.
  rewrite /inode_to_vals list_to_inode_buf_to_list //.
Qed.

Inductive bufDataKind :=
| KindBit
| KindInode
| KindBlock
.

Global Instance bufDataKind_eq_dec : EqDecision bufDataKind.
Proof.
  solve_decision.
Defined.

Inductive bufDataT : bufDataKind -> Type :=
| bufBit (b : bool) : bufDataT KindBit
| bufInode (i : inode_buf) : bufDataT KindInode
| bufBlock (b : Block) : bufDataT KindBlock
.

Global Instance bufDataT_eq_dec K : EqDecision (bufDataT K).
Proof.
  intros d1 d2. rewrite /Decision.
  destruct d1.
  - refine (match d2 as d in (bufDataT K) return
              (match K as K' return bufDataT K' → Type
               with KindBit => λ d', {bufBit b = d'} + {bufBit b ≠ d'} | _ => λ d, True end) d
            with bufBit b2 => _ | bufInode i2 => _ | bufBlock b2 => _ end); try done.
    destruct (decide (b = b2)) as [<-|Hne]; first by left.
    right. by inversion 1.
  - refine (match d2 as d in (bufDataT K) return
              (match K as K' return bufDataT K' → Type
               with KindInode => λ d', {bufInode i = d'} + {bufInode i ≠ d'} | _ => λ d, True end) d
            with bufBit b2 => _ | bufInode i2 => _ | bufBlock b2 => _ end); try done.
    destruct (decide (i = i2)) as [<-|Hne]; first by left.
    right. by inversion 1.
  - refine (match d2 as d in (bufDataT K) return
              (match K as K' return bufDataT K' → Type
               with KindBlock => λ d', {bufBlock b = d'} + {bufBlock b ≠ d'} | _ => λ d, True end) d
            with bufBit b2 => _ | bufInode i2 => _ | bufBlock b2 => _ end); try done.
    destruct (decide (b = b2)) as [<-|Hne]; first by left.
    right. by inversion 1.
Qed.

Arguments bufDataT K.

Definition bufSz K : nat :=
  match K with
  | KindBit => 1
  | KindInode => inode_bytes*8
  | KindBlock => block_bytes*8
  end.

Record buf := {
  bufKind : bufDataKind;
  bufData : bufDataT bufKind;
  bufDirty : bool;
}.

Definition get_bit (b0 : u8) (off : u64) : bool :=
  if decide (U8 1 = word.and (word.sru b0 (u8_from_u64 off)) (U8 1))
  then true
  else false.

Definition valid_off K (off : u64) : Prop :=
  int.Z off `mod` bufSz K = 0.
