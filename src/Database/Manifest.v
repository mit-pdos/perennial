From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Database.Common.
From RecoveryRefinement Require Import Database.BinaryEncoding.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.Table.

Module Manifest.
  Module Mft.
    (* TODO: would be good to have arrays of tables, but tables are not
    represented by a type code (they're records) *)
    Record t :=
      mk { l0tables: list Table.Tbl.t;
           l1tables: list Table.Tbl.t;
           nextIdent: IORef ty.uint32;
         }.
  End Mft.
End Manifest.
