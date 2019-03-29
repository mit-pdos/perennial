From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecordUpdate Require Import RecordSet.

Generalizable All Variables.

Definition _zoom `{Setter A C proj} T (r: relation C C T) : relation A A T :=
  zoom proj (fun c => set proj (fun _ => c)) r.

Arguments _zoom {A C} proj {H} {T} r.
