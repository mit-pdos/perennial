From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Table.

Module Manifest.
  Module Mft.
    Record t :=
      mk { l0tables: Array Table.Tbl.t;
           l1tables: Array Table.Tbl.t;
           nextIdent: IORef uint32;
         }.
  End Mft.
End Manifest.
