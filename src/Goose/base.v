From Classes Require Import EqualDec.

From Perennial Require Export Spec.Proc.
From Perennial Require Export Spec.LockDefs.

From Perennial.Goose Require Export GoZeroValues.
From Perennial.Goose Require Export GoLayer.

Export EqualDecNotation.
Export ProcNotations. Open Scope proc.

Open Scope string.

Notation proc := (Proc.proc Op).
