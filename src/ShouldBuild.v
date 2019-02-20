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
From RecoveryRefinement Require Import Examples.AtomicPair.RefinementShadow.

(* goose output *)
From RecoveryRefinement Require Import Goose.Examples.UnitTests.
From RecoveryRefinement Require Import Goose.Examples.SimpleDb.
From RecoveryRefinement Require Import Goose.Examples.MailServer.
