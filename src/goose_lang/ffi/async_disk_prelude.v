From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.async_disk.
Existing Instances async_disk.disk_op async_disk.disk_model async_disk.disk_ty.
Existing Instances async_disk.disk_semantics async_disk.disk_interp.
Existing Instance goose_diskGS.
(* Now that the TC parameter is fixed, we can make this a coercion. *)
Coercion Var' (s: string) := Var s.


Module disk.
  Notation Disk := async_disk.Disk.
  Notation Write := async_disk.Write.
  Notation Read := async_disk.Read.
  Notation ReadTo := async_disk.ReadTo.
  Notation Barrier := async_disk.Barrier.
End disk.
