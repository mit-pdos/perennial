From iris.algebra Require Export auth gmap frac agree excl vector.

From Perennial.algebra Require Export big_op.

From Perennial.Helpers Require Export Tactics List ListLen BigOp Transitions iris ipm.

From Perennial.base_logic Require Export ghost_var.
From Perennial.program_logic Require Export atomic ncinv.
From Perennial.goose_lang Require Export proofmode wpc_proofmode array.
From Perennial.goose_lang Require Export into_val.
From Perennial.goose_lang.lib Require Export
     persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map.

Export uPred.

Global Set Default Proof Using "Type".
Global Set Printing Projections.

Global Opaque load_ty store_ty.

Global Remove Hints fractional.frame_fractional : typeclass_instances.

Import sel_patterns.

Fixpoint fix_frame_selpat (Hs: list sel_pat) : list sel_pat :=
  match Hs with
  | nil => []
  | SelIntuitionistic :: Hs => fix_frame_selpat Hs ++ [SelIntuitionistic]
  | SelPure :: Hs => fix_frame_selpat Hs ++ [SelPure]
  | s :: Hs => s :: fix_frame_selpat Hs
  end.

Ltac iFrame_hyps_fast :=
  repeat match goal with
         | |- envs_entails ?Δ (?P ∗ _)%I =>
           lazymatch Δ with
           | context[Esnoc _ ?i P] => iFrameHyp i
           end
         end.

Ltac iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; iFrame_go Hs
  | SelIntuitionistic :: ?Hs => iFrameAnyIntuitionistic; iFrame_go Hs
  | SelSpatial :: ?Hs => iFrame_hyps_fast; iFrameAnySpatial; iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; iFrame_go Hs
  end.

Tactic Notation "iFrame" constr(Hs) :=
  let Hs := sel_pat.parse Hs in
  let Hs := (eval cbv in (fix_frame_selpat Hs)) in
  iFrame_go Hs.
