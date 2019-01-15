From RecoveryRefinement Require Export Helpers.MachinePrimitives.
From RecoveryRefinement Require Export Database.DataStructures.

Definition Key := uint64.
Definition Value := ByteString.

Module Entry.
  Record t :=
    mk { key : Key;
         value : Value; }.
End Entry.

Module SliceHandle.
  Record t :=
    mk { offset : uint64;
         length : uint32; }.
End SliceHandle.
