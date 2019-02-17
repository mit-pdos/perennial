From Classes Require Import EqualDec.

From RecoveryRefinement Require Export Spec.Proc.

From RecoveryRefinement.Goose Require Export Machine.
From RecoveryRefinement.Goose Require Export GoZeroValues.
From RecoveryRefinement.Goose Require Export GoLayer.

Export EqualDecNotation.
Export ProcNotations. Open Scope proc.

Open Scope string.

Notation proc := (Proc.proc Op).
