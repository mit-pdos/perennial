Cd "database/src/Coq/".

From Coq Require Extraction.

From RecoveryRefinement Require Import Helpers.ExtrMachinePrimitives.
From RecoveryRefinement Require Import Database.ExtrBaseLayer.
From RecoveryRefinement Require Import Database.ExtractionExamples.
From RecoveryRefinement Require Import Database.Simple.SimpleDb.

Extraction Language Haskell.

Separate Extraction ExtractionExamples SimpleDb.

Cd "../../..".
