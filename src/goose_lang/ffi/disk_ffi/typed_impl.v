From Perennial.goose_lang Require Export ffi.disk_ffi.impl.
From Perennial.goose_lang Require Export lang notation typing.
From Perennial.goose_lang.lib Require Export slice.

Inductive Disk_ty := | DiskInterfaceTy.

#[global]
Instance disk_val_ty: val_types :=
  {| ext_tys := Disk_ty; |}.

Inductive disk_ext_tys : @val disk_op -> (ty * ty) -> Prop :=
| DiskOpType op :
  disk_ext_tys (λ: "v", ExternalOp op (Var "v"))%V
    (match op with
     | ReadOp => (uint64T, arrayT byteT)
     | WriteOp => (prodT uint64T (arrayT byteT), unitT)
     | SizeOp => (unitT, uint64T)
     end).

Definition disk_ty : ext_types disk_op :=
  {| val_tys := disk_val_ty;
    get_ext_tys := disk_ext_tys |}.

Module disk.
  Definition Disk: ty := extT DiskInterfaceTy.

  (** * Disk user-facing operations. *)
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the disk model *)
  Existing Instances disk_op disk_model disk_ty.

  Definition disk_val (d : ()) : val := ExtV d.

  Definition blockT `{ext_tys:ext_types}: @ty val_tys := slice.T byteT.

  Definition BlockSize := BlockSize.

  Definition Get: val :=
    λ: <>, disk_val ().

  Definition Read: val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    raw_slice byteT (Var "p") #4096.

  Definition ReadTo: val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp (Var "a") in
    MemCpy_rec byteT (slice.ptr (Var "buf")) (Var "p") #4096.

  Definition Write: val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  Definition Barrier: val :=
    λ: <>, #().

  Definition Size: val :=
    λ: "v",
       ExternalOp SizeOp (Var "v").
End disk.
