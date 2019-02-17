From RecordUpdate Require Import RecordUpdate.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.
From RecoveryRefinement.Goose Require Import Heap.

From Classes Require Import EqualDec.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Import EqualDecNotation.

Module FS.
  Implicit Types (p:string) (fh:File) (bs:slice.t byte).

  (* the types of the arguments are determined by their name, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Open p : Op File
  | Close fh : Op unit
  | List : Op (list string)
  | Size fh : Op uint64
  | ReadAt fh (off:uint64) (len:uint64) : Op (slice.t byte)
  | Create p : Op File
  | Append fh bs' : Op unit
  | Delete p : Op unit
  | Rename p1 p2 : Op unit
  | Truncate p : Op unit
  | AtomicCreate p bs : Op unit
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op)) (at level 0, op at level 200).
    Definition open p : proc _ := Call! Open p.
    Definition close fh : proc _ := Call! Close fh.
    Definition list : proc _ := Call! List.
    Definition size fh : proc _ := Call! Size fh.
    Definition readAt fh off len : proc _ := Call! ReadAt fh off len.
    Definition create p : proc _ := Call! Create p.
    Definition append fh bs : proc _ := Call! Append fh bs.
    Definition delete p : proc _ := Call! Delete p.
    Definition rename p1 p2 : proc _ := Call! Rename p1 p2.
    Definition truncate p : proc _ := Call! Truncate p.
    Definition atomicCreate p bs : proc _ := Call! AtomicCreate p bs.

  End OpWrappers.

  Inductive OpenMode := Read | Write.

  Record State :=
    mkState { heap: Data.State;
              files: gmap.gmap string (List.list byte);
              fds: gmap.gmap File (string * OpenMode); }.

  Instance _eta : Settable State :=
    mkSettable (constructor mkState <*> heap <*> files <*> fds)%set.

  Definition readFd (fh: File) (m: OpenMode) : relation State State string :=
    readSome (fun s => match s.(fds) !! fh with
                    | Some (p, m') => if m == m' then Some p else None
                    | _ => None
                    end).

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | _ => error
    end.

  Definition crash_step : relation State State unit :=
    _ <- puts (set fds (fun _ => ∅));
      puts (set heap (fun _ => ∅)).

End FS.
