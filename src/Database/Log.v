From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Module Log.
  Import ProcNotations.
  Local Open Scope proc.

  Definition addTxn (txn: ByteString) : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- Data.get (Var.LogFile);
      let bs := encode (array16 txn) in
      lift (FS.append fd bs).

  Definition clear : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- Data.get (Var.LogFile);
      lift (FS.truncate fd).

  Definition init : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- lift (FS.create "log");
      Data.set_var (Var.LogFile) fd.

  (* TODO: injection type inference does the wrong thing here, need to debug
  it *)
  Definition recoverTxns : proc (Data.Op ⊕ FS.Op) (Array ty.ByteString) :=
    fd <- Data.get (Op':=Data.Op ⊕ FS.Op) (Var.LogFile);
      txns <- Call (inject (Op:=Data.Op ⊕ FS.Op) (Data.NewArray ty.ByteString));
      sz <- lift (FS.size fd);
      log <- lift (FS.readAt fd int_val0 sz);
      _ <- Loop
        (fun log => match decode Array16 log with
                 | Some (txn, n) =>
                   _ <- Data.arrayAppend (Op':=Data.Op ⊕ FS.Op) txns (getBytes txn);
                     Continue (BS.drop n log)
                 | None => LoopRet tt
                 end) log;
      Ret txns.
End Log.
