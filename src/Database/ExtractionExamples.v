From RecoveryRefinement Require Import Database.Base.

Import ProcNotations.
Local Open Scope proc.

Import UIntNotations.
Local Open Scope u64.

Import EqualDecNotation.

Module HashTableBenchmarks.

  Definition ex1_setup : proc (HashTable ByteString) :=
    Data.newHashTable _.

  Definition ex1_write1 (t:HashTable ByteString)
             (k:uint64) (bs:ByteString) : proc unit :=
    Data.hashTableAlter t k (fun _ => Some bs).

  Definition ex1_write3 (t:HashTable ByteString)
             (k:uint64) (bs:ByteString) : proc unit :=
    _ <- Data.hashTableAlter t k (fun _ => Some bs);
    _ <- Data.hashTableAlter t (k+1)%u64 (fun _ => Some bs);
    _ <- Data.hashTableAlter t (k+2)%u64 (fun _ => Some bs);
    Ret tt.

  Definition ex1_read (t:HashTable ByteString)
             (k:uint64) : proc (option ByteString) :=
    Data.hashTableLookup t k.

  Definition ex2_seq_reads (t:HashTable ByteString)
             (k:uint64) (iters:uint64) : proc unit :=
    Loop (fun i => if i == iters
                then LoopRet tt
                else _ <- Data.hashTableLookup t k;
                  Continue (i+1)%u64) 0.

  Definition ex2_par_reads (t:HashTable ByteString)
             (k:uint64) (iters:uint64) : proc unit :=
    _ <- Spawn (ex2_seq_reads t k iters);
      _ <- ex2_seq_reads t k iters;
      Ret tt.

End HashTableBenchmarks.
