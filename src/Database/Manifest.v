From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.BinaryEncoding.
From RecoveryRefinement Require Import Database.Table.

Module Manifest.
  Module Mft.
    Record t :=
      mk { l0tables: Array Table.Tbl.t;
           l1tables: Array Table.Tbl.t;
           nextIdent: IORef uint64;
         }.
  End Mft.
End Manifest.
