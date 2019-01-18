From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Definition DoWhile Op T (body: T -> proc Op (option T)) (init: T) : proc Op T :=
  Bind (Until (T:=option T * T) (fun '(v, last) => match v with
               | Some _ => false
               | None => true
               end)
        (fun v => match v with
               | Some (Some x, last) => Bind (body x) (fun v => Ret (v, x))
               | Some (None, last) => Ret (None, last)
               | None => Ret (None, init)
               end)
        (Some (Some init, init)))
       (fun '(_, last) => Ret last).

Definition DoWhileVoid Op T (body: T -> proc Op (option T)) (init: T) : proc Op unit :=
  Bind (Until (T:=option T) (fun v => match v with
               | Some _ => false
               | None => true
               end)
        (fun v => match v with
               | Some (Some x) => body x
               | Some None => Ret None
               | None => Ret None
               end)
        (Some (Some init)))
       (fun _ => Ret tt).

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
      _ <- DoWhileVoid
        (fun log => match decode Array16 log with
                 | Some (txn, n) =>
                   _ <- Data.arrayAppend (Op':=Data.Op ⊕ FS.Op) txns (getBytes txn);
                     Ret (Some (BS.drop n log))
                 | None => Ret None
                 end) log;
      Ret txns.
End Log.
