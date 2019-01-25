From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.Log.

Module WAL.
  Module Cache.
    Definition t := HashTable (option ByteString).
  End Cache.

  Module DbLog.
    Record t :=
      { log: Log.t;
        cache: Cache.t; }.
  End DbLog.

  Import ProcNotations.
  Local Open Scope proc.

  Definition create (p: string) : proc DbLog.t :=
    log <- Log.create p;
      cache <- Data.newHashTable _;
      Ret {| DbLog.log := log;
             DbLog.cache := cache; |}.

End WAL.
