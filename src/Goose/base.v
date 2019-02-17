From Classes Require Import EqualDec.

From RecoveryRefinement Require Export Spec.Proc.

From RecoveryRefinement.Goose Require Export Machine.
From RecoveryRefinement.Goose Require Export GoZeroValues.
From RecoveryRefinement.Goose Require Export GoLayer.

Import EqualDecNotation.
Import ProcNotations. Open Scope proc.

Notation proc := (Proc.proc Op).
