From Perennial.goose_lang Require Import lang notation.
From Perennial.goose_lang Require Export ffi.disk_ffi.impl.
#[global]
Existing Instances disk.disk_op disk.disk_model.
Coercion Var' (s: string) := Var s.

Section disk.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk.disk_op disk.disk_model disk.disk_ty.

  (* FIXME(tchajed): new goose is emitting __Read for d.Read when I'd expect
  Disk__Read since it's a method of the Disk type *)

  (* these model the methods of disk.Disk, which are modeled by ignoring the
  disk argument - the FFI model assumes all disks are the same, but the code
  does not to enable testing *)
  Definition __Read: val :=
    λ: <> "a", disk.Read "a".
  Definition __Write: val :=
    λ: <> "a" "v", disk.Write "a".

End disk.
