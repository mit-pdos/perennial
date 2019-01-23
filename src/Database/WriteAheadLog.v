From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Log.

Module WAL.
  Module Cache.
    Definition t := HashTable uint64 (option ByteString).
  End Cache.

  Module DbLog.
    Record t :=
      { log: Log.t;
        cache: Cache.t; }.
  End DbLog.

  Import ProcNotations.
  Local Open Scope proc.

  Notation proc := (proc (Data.Op ⊕ FS.Op)).

  Definition create (p: string) : proc DbLog.t :=
    log <- Log.create p;
      cache <- Call (inject (Data.NewHashTable _ _));
      Ret {| DbLog.log := log;
             DbLog.cache := cache; |}.

End WAL.
