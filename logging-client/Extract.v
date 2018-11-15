Cd "logging-client/extract/".

From Coq Require Extraction.

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.

Extraction Language Haskell.

From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Import Examples.Logging.ComposedRefinement.

Separate Extraction LoggingTwoDiskRefinement.compile.

Cd "../../".
