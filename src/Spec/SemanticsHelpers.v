From Classes Require Import EqualDec.
From stdpp Require Import base.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Spec.Proc.

Set Implicit Arguments.

Arguments existT {A P} _ _.
Import EqNotations.

Import RelationNotations.

(* modeling non-atomic operations as pairs of begin/end ops *)
Inductive NonAtomicArgs T :=
| FinishArgs (args:T)
| Begin.
Arguments Begin {T}.
(* NOTE: this does not allow dependent return values *)
Definition retT T (args:NonAtomicArgs T) T' : Type := if args then T' else unit.

(* nonAtomicOp takes an operation partially applied to some key identifying
  the object (assuming the operation does separate over some resources, such as
  addresses or references) *)
Definition nonAtomicOp {Op ArgT T}
           (op: forall (args:NonAtomicArgs ArgT), Op (retT args T))
  : ArgT -> proc Op T :=
  fun args => Bind (Call (op Begin)) (fun _ => Call (op (FinishArgs args))).


(* this is represented as an inductive rather than a combination of ObjΣ and a
  boolean state to make misuse harder (there's no reasonable way to use the
  state without knowing the status) *)
Inductive NonAtomicState ObjΣ : Type :=
| Clean (s:ObjΣ)
| Dirty (s:ObjΣ).

Definition readClean {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean s => pure s
  | Dirty _ => error
  end.

Definition readDirty {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean _ => error
  | Dirty s  => pure s
  end.

Definition nonAtomicStep
           {ArgT} (args: NonAtomicArgs ArgT) {T} (* the operation *)
           {ObjΣ} (obj_s: NonAtomicState ObjΣ)
           {State}
           (mkDirty: ObjΣ -> relation State State unit)
           (opStep: ObjΣ -> ArgT -> relation State State T)
  : relation State State (retT args T) :=
  match args with
  | Begin => s <- readClean obj_s;
              mkDirty s
  | FinishArgs x => s <- readDirty obj_s;
                     opStep s x
  end.

Record DynMap A (Ref: A -> Type) (Model: A -> Type) :=
  { dynMap : sigT Ref -> option (sigT Model);
    dynMap_wf : forall T v, match dynMap (existT T v) with
                       | Some (existT T' _) => T' = T
                       | None => True
                       end; }.

Module OptionNotations.
  Delimit Scope option_monad with opt.
  Notation "'Some!' x <- a ; f" :=
    (match a with
     | Some x => f
     | _ => None
     end)
      (right associativity, at level 70, x pattern) : option_monad.

  Notation "'left!' H <- a ; f" :=
    (match a with
     | left H => f
     | right _ => None
     end)
      (right associativity, at level 60, f at level 200) : option_monad.

  Notation "'ret!' a" := (Some a) (at level 60) : option_monad.
End OptionNotations.

Import EqualDecNotation.
Import OptionNotations.
Local Open Scope option_monad.

Definition getDyn A (Ref Model: A -> Type)
           (m: DynMap Ref Model) a (r: Ref a) : option (Model a).
Proof.
  pose proof (m.(dynMap_wf) _ r).
  destruct (m.(dynMap) (existT a r)); [ apply Some | exact None ].
  destruct s.
  exact (rew H in m0).
Defined.

Arguments getDyn {A Ref Model} m {a} r.

Definition updDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
           a (v: Ref a) (x: Model a) (m: DynMap Ref Model) : DynMap Ref Model.
Proof.
  refine {| dynMap := fun r => if r == existT a v then ret! existT a x else m.(dynMap) r |}.
  intros.
  destruct (existT _ v0 == existT _ v).
  - inversion e; auto.
  - apply (m.(dynMap_wf) _ v0).
Defined.

Arguments updDyn {A Ref Model dec a} v x m.

Instance empty_dynmap A Ref Model : Empty (@DynMap A Ref Model).
refine {| dynMap := fun _ => None; |}.
intros; auto.
Defined.
