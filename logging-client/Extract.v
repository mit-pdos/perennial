Cd "logging-client/extract/".

From Coq Require Extraction.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.

From RecoveryRefinement Require Import Examples.Logging.Impl.
From RecoveryRefinement Require Import Examples.Logging.ComposedRefinement.

Extraction Language Haskell.

Extract Constant Impl.LogHdr_fmt => "logHdrFmt".
Extract Constant Impl.Descriptor_fmt => "descriptorFmt".

Import LoggingTwoDiskRefinement.
Separate Extraction compile init recover.

Cd "../../".
