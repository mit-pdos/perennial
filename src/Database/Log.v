From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Import ProcNotations.
Open Scope proc.

Module Log.
  Inductive Op : Type -> Type :=
  | AddTxn : ByteString -> Op unit
  | Clear : Op unit
  (* hack to return from recovery: these transactions are processed and
  persisted by the upper layer; we don't provide a way to clear them here
  because all they do is take memory *)
  | GetRecoveredTxns : Op (Array ByteString)
  .
End Log.

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

Module LogImpl.
  Definition addTxn (txn: ByteString) : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- Data.get (Log File);
      let bs := encode (array16 txn) in
      lift (FS.append fd bs).

  Definition clear : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- Data.get (Log File);
      lift (FS.truncate fd).

  Definition getRecoveredTxns : proc (Data.Op ⊕ FS.Op) _ :=
    Data.get (Log RecoveredTxns).

  Definition init : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- lift (FS.create "log");
      Data.set (Log File) fd.

  Definition recover : proc (Data.Op ⊕ FS.Op) _ :=
    fd <- Data.get (Log File);
      txns <- Data.get (Log RecoveredTxns);
      sz <- lift (FS.size fd);
      log <- lift (FS.readAt fd int_val0 sz);
      DoWhileVoid (fun log => match decode Array16 log with
                           | Some (txn, n) =>
                             _ <- Data.arrayAppend txns txn;
                               Ret (Some (BS.drop n log))
                           | None => Ret None
                           end) log.

End LogImpl.
