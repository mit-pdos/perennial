Cd "logging-client/extract/".

From Coq Require Extraction.

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.

Extraction Language Haskell.

From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Import Examples.Logging.ComposedRefinement.

Definition compile := LoggingTwoDiskRefinement.rf.(compile).

Extraction "Logging" compile.

Cd "../../".
