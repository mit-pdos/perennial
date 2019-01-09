From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.

From Coq Require Import String.

Definition Path := string.

Module FS.
  Implicit Types (p:Path) (fh:Fd) (bs:ByteString).

  Inductive Op : Type -> Type :=
  | Open : Path -> Op Fd
  | Close : Fd -> Op unit
  | List : Op (list Path)
  | Size : Fd -> Op int64
  (* readAt fh offset length *)
  | ReadAt : Fd -> int64 -> int64 -> Op ByteString
  | Create : Path -> Op Fd
  | Append : Fd -> ByteString -> Op unit
  | Delete : Path -> Op unit
  | Truncate : Fd -> Op unit
  | AtomicCreate : Path -> ByteString -> Op unit
  .

  Definition open (p:Path) : proc Op Fd := Call (Open p).
  Definition close fh := Call (Close fh).
  Definition list := Call (List).
  Definition size fh := Call (Size fh).
  Definition readAt fh off len := Call (ReadAt fh off len).
  Definition create p := Call (Create p).
  Definition append fh bs := Call (Append fh bs).
  Definition delete p := Call (Delete p).
  Definition truncate fh := Call (Truncate fh).
  Definition atomicCreate p bs := Call (AtomicCreate p bs).
End FS.
