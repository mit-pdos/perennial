From RecoveryRefinement Require Import Database.Base.

Import ProcNotations.
Local Open Scope proc.

Import UIntNotations.
Local Open Scope u64.

Import EqualDecNotation.

Section HashTableBenchmarks.

  Definition ex1_setup : proc (HashTable ByteString) :=
    Data.newHashTable _.

  Definition ex1_write1 (k:uint64) (bs:ByteString)
    (t:HashTable ByteString) : proc unit :=
    Data.hashTableAlter t k (fun _ => Some bs).

  Definition ex1_write3 (k:uint64) (bs:ByteString)
             (t:HashTable ByteString) : proc unit :=
    _ <- Data.hashTableAlter t k (fun _ => Some bs);
    _ <- Data.hashTableAlter t (k+1)%u64 (fun _ => Some bs);
    _ <- Data.hashTableAlter t (k+2)%u64 (fun _ => Some bs);
    Ret tt.

  Definition ex1_read (k:uint64)
             (t:HashTable ByteString) : proc (option ByteString) :=
    Data.hashTableLookup t k.

  Definition ex2_seq_reads (k:uint64) (iters:uint64)
             (t:HashTable ByteString) : proc unit :=
    Loop (fun i => if i == iters
                then LoopRet tt
                else _ <- Data.hashTableLookup t k;
                  Continue (i+1)%u64) 0.

  Definition ex2_par_reads (k:uint64) (iters:uint64)
             (t:HashTable ByteString) : proc unit :=
    _ <- Spawn (ex2_seq_reads k iters t);
      _ <- ex2_seq_reads k iters t;
      Ret tt.

End HashTableBenchmarks.
