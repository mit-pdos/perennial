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

Section ArrayBenchmarks.
  Implicit Types (r:Array uint64) (i:uint64).
  Definition a_setup : proc (Array uint64) :=
    Data.newArray _.

  Definition a_append1 r : proc unit :=
    Data.arrayAppend r 1.

  Definition a_append3 r : proc unit :=
    _ <- Data.arrayAppend r 1;
    _ <- Data.arrayAppend r 1;
    _ <- Data.arrayAppend r 1;
    Ret tt.

  Definition a_append_many (els:uint64) r : proc unit :=
    Loop (fun i => if i == els then LoopRet tt
                else _ <- Data.arrayAppend r i;
                  Continue (i+1)) 0.

  Definition a_read r : proc uint64 :=
    Data.arrayGet r 0.

  Definition a_readall r : proc unit :=
    sz <- Data.arrayLength r;
      Loop (fun i => if i == sz then LoopRet tt
                  else _ <- Data.arrayGet r i;
                    Continue (i+1)) 0.

  Definition a_readall_par r : proc unit :=
    _ <- Spawn (a_readall r);
      a_readall r.
End ArrayBenchmarks.
