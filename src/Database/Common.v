From RecoveryRefinement Require Export Helpers.MachinePrimitives.
From RecoveryRefinement Require Export Database.DataStructures.

Definition Key := int64.
Definition Value := ByteString.

Module Entry.
  Record t :=
    mk { key : Key;
         value : Value; }.
End Entry.

Module SliceHandle.
  Record t :=
    mk { offset : int64;
         length : int32; }.
End SliceHandle.
