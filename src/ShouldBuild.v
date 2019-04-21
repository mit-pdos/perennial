(* examples on top of concurrency framework *)
From RecoveryRefinement Require Import Examples.StatDb.Refinement.
From RecoveryRefinement Require Import Examples.AtomicPair.RefinementShadow.
From RecoveryRefinement Require Import Examples.AtomicPair.RefinementLog.
From RecoveryRefinement Require Import Examples.Logging.LogRefinement.
From RecoveryRefinement Require Import Examples.ReplicatedDisk.TwoDiskAPI.
From RecoveryRefinement Require Import Examples.ReplicatedDisk.ReplicatedDiskImpl.
From RecoveryRefinement Require Import Examples.ReplicatedDisk.RefinementAdequacy.

(* mailboat proof *)
From RecoveryRefinement Require Import Examples.MailServer.MailRefinement.

(* goose output *)
From RecoveryRefinement Require Import Goose.Examples.UnitTests.
From RecoveryRefinement Require Import Goose.Examples.SimpleDb.
From RecoveryRefinement Require Import Goose.Examples.MailServer.
