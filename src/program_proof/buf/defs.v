Require Import Coq.Program.Equality.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


From Perennial.program_proof Require Import proof_prelude.

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.
Definition inode_to_vals {ext: ext_op} (i:inode_buf) : list val :=
  fmap b2val (vec_to_list i).

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
  int.val off `mod` bufSz K = 0.
