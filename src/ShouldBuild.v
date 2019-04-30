(* examples on top of concurrency framework *)
From Armada Require Import Examples.StatDb.Refinement.
From Armada Require Import Examples.AtomicPair.RefinementShadow.
From Armada Require Import Examples.AtomicPair.RefinementLog.
From Armada Require Import Examples.Logging.LogRefinement.
From Armada Require Import Examples.ReplicatedDisk.ReplicatedDiskRefinement.

(* mailboat proof *)
From Armada Require Import Examples.MailServer.MailRefinement.

(* goose output *)
From Armada Require Import Goose.Examples.UnitTests.
From Armada Require Import Goose.Examples.SimpleDb.
From Armada Require Import Goose.Examples.MailServer.
