Cd "logging-client/extract/".

From Coq Require Extraction.

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.

Extraction Language Haskell.

From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Import Examples.Logging.Impl.
From RecoveryRefinement Require Import Examples.Logging.ComposedRefinement.

Extract Constant Impl.LogHdr_fmt => "logHdrFmt".
Extract Constant Impl.Descriptor_fmt => "descriptorFmt".

Separate Extraction LoggingTwoDiskRefinement.compile.

Cd "../../".
