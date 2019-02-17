(* This file is a temporary provision to build a subset of the code in CI. *)
(* TODO: go back to building everything *)

(* simple databases *)
From RecoveryRefinement Require Import Database.Store.
From RecoveryRefinement Require Import Database.Simple.SimpleDb.
From RecoveryRefinement Require Import Database.Simple.SimpleDbProof.

(* mail server experiment *)
From RecoveryRefinement Require Import Mail.Impl Mail.API.

(* concurrency framework *)
From RecoveryRefinement Require Import CSL.RefinementAdequacy.
From RecoveryRefinement Require Import CSL.Lifting.
From RecoveryRefinement Require Import Examples.ExMach.WeakestPre.
From RecoveryRefinement Require Import Examples.ExMach.RefinementAdequacy.
From RecoveryRefinement Require Import Examples.StatDb.Refinement.

(* goose output *)
From RecoveryRefinement Require Import Database.Simple.GoSimpleDb.
From RecoveryRefinement Require Import Examples.GooseUnitTests.
(* new goose support library *)
From RecoveryRefinement.Goose Require Import base.
