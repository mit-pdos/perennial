From Classes Require Import EqualDec.

From Armada Require Export Spec.Proc.
From Armada Require Export Spec.LockDefs.

From Armada.Goose Require Export GoZeroValues.
From Armada.Goose Require Export GoLayer.

Export EqualDecNotation.
Export ProcNotations. Open Scope proc.

Open Scope string.

Notation proc := (Proc.proc Op).
