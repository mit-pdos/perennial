From RecoveryRefinement Require Import Database.Base.

Import ProcNotations.
Local Open Scope proc.

Import UIntNotations.
Local Open Scope u64.

Import EqualDecNotation.

Section HashTableBenchmarks.

  Implicit Types (r:HashTable ByteString) (k:uint64) (bs:ByteString).

  Definition ht_setup : proc (HashTable ByteString) :=
    Data.newHashTable _.

  Definition ht_write1 k bs r : proc unit :=
    Data.hashTableAlter r k (fun _ => Some bs).

  Definition ht_write3 k bs r : proc unit :=
    _ <- Data.hashTableAlter r k (fun _ => Some bs);
    _ <- Data.hashTableAlter r (k+1) (fun _ => Some bs);
    _ <- Data.hashTableAlter r (k+2) (fun _ => Some bs);
    Ret tt.

  Definition ht_read k r : proc (option ByteString) :=
    Data.hashTableLookup r k.

  Definition ht_seq_reads k (iters:uint64) r : proc unit :=
    Loop (fun i => if i == iters
                then LoopRet tt
                else _ <- Data.hashTableLookup r k;
                  Continue (i+1)) 0.

  Definition ht_par_reads k (iters:uint64) r : proc unit :=
    _ <- Spawn (ht_seq_reads k iters r);
      _ <- ht_seq_reads k iters r;
      Ret tt.

End HashTableBenchmarks.
