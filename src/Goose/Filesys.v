From RecordUpdate Require Import RecordSet.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Spec.LockDefs.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.
From RecoveryRefinement.Goose Require Import Heap.

From Classes Require Import EqualDec.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Import EqualDecNotation.

Module FS.
  Module path.
    Record t :=
      mk { dir: string;
           fname: string; }.
  End path.

  Section GoModel.
  Context `{model_wf:GoModelWf}.
  Implicit Types (dir p:string) (fh:File) (bs:slice.t byte).

  (* the types of the arguments are determined by their name, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Open dir p : Op File
  | Close fh : Op unit
  | List dir (na: NonAtomicArgs unit) : Op (retT na (slice.t string))
  | Size fh : Op uint64
  | ReadAt fh (off:uint64) (len:uint64) : Op (slice.t byte)
  | Create dir p : Op (File*bool)
  | Append fh bs' : Op unit
  | Delete dir p : Op unit
  | Rename dir1 p1 dir2 p2 : Op unit
  | Truncate dir p : Op unit
  | AtomicCreate dir p bs : Op unit
  | Link dir1 p1 dir2 p2 : Op bool
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op) : proc _) (at level 0, op at level 200).
    Definition open dir p : proc _ := Call! Open dir p.
    Definition close fh : proc _ := Call! Close fh.
    Definition list dir : proc (slice.t string) :=
      Bind (Call (inject (List dir Begin)))
           (fun _ => Call (inject (List dir (FinishArgs tt)))).
    Definition size fh : proc _ := Call! Size fh.
    Definition readAt fh off len : proc _ := Call! ReadAt fh off len.
    Definition create dir p : proc _ := Call! Create dir p.
    Definition append fh bs : proc _ := Call! Append fh bs.
    Definition delete dir p : proc _ := Call! Delete dir p.
    Definition rename dir1 p1 dir2 p2 : proc _ := Call! Rename dir1 p1 dir2 p2.
    Definition truncate dir p : proc _ := Call! Truncate dir p.
    Definition atomicCreate dir p bs : proc _ := Call! AtomicCreate dir p bs.
    Definition link dir1 p1 dir2 p2 := Call! Link dir1 p1 dir2 p2.

  End OpWrappers.

  Inductive OpenMode := Read | Write.

  Global Instance path_eqdec: EqDecision path.t.
  Proof. apply _. Qed.

  Global Instance path_countable : countable.Countable path.t.
  Proof.
    apply (countable.inj_countable'
            (fun '(path.mk dir fname) => (dir, fname))
            (fun '(dir, fname) => path.mk dir fname)).
    destruct x; simpl; auto.
  Qed.

  Definition Inode := nat.

  Record State :=
    mkState { heap: Data.State;
              dirlocks: gmap.gmap string (LockStatus * unit);
              dirents: gmap.gmap string (gmap.gmap string Inode);
              inodes: gmap.gmap Inode (List.list byte);
              fds: gmap.gmap File (Inode * OpenMode); }.

  Global Instance _eta : Settable State :=
    settable! mkState <heap; dirlocks; dirents; inodes; fds>.

  Import RelationNotations.

  Definition lookup K `{countable.Countable K} V (proj:State -> gmap.gmap K V) (k:K) : relation State State V :=
    readSome (fun s => s.(proj) !! k).

  Definition resolvePath dir name : relation State State Inode :=
    let! ents <- lookup dirents dir;
         readSome (fun _ => ents !! name).

  Definition fresh_key K `{countable.Countable K} V (proj: State -> gmap.gmap K V) : relation State State K :=
    such_that (fun s v => s.(proj) !! v = None).

  Definition createSlice V (data: List.list V) : relation State State (slice.t V) :=
    r <- such_that (fun s (r: ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
      _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap V) r (Unlocked, data))));
      pure {| slice.ptr := r;
              slice.offset := 0;
              slice.length := length data; |}.

  Definition readFd (fh: File) m : relation State State (List.list byte) :=
    let! (inode, m') <- lookup fds fh;
         if m == m' then lookup inodes inode
         else error.

  Definition unwrap S A (e: option A) : relation S S A :=
    match e with
    | Some v => pure v
    | None => error
    end.

  Definition is_none S A (e: option A) : relation S S unit :=
    match e with
    | Some _ => error
    | None => pure tt
    end.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Open dir name =>
      inode <- resolvePath dir name;
        fh <- fresh_key fds;
        _ <- puts (set fds <[fh := (inode, Read)]>);
        pure fh

    | Close fh =>
      puts (set fds (map_delete fh))

    | List dir na =>
      let! (s, _) <- lookup dirlocks dir;
           match na return relation _ _ (retT na (slice.t string)) with
           | Begin =>
             s' <- unwrap (lock_acquire Reader s);
               puts (set dirlocks <[dir := (s', tt)]>)
           | FinishArgs _ =>
             let! ents <- lookup dirents dir;
                  s' <- unwrap (lock_release Reader s);
                  _ <- puts (set dirlocks <[dir := (s', tt)]>);
                  let l := map fst (map_to_list ents) in
                  createSlice l
                end

    | Size fh =>
      bs <- readFd fh Read;
        pure (length bs)

    | ReadAt fh off len =>
      bs <- readFd fh Read;
        let read_bs := list.take len (list.drop off bs) in
        createSlice bs

    | Create dir name =>
      ents <- lookup dirents dir;
           match ents !! name with
           | Some _ => fh <- identity;
                        pure (fh, false)
           | None =>
             inode <- fresh_key inodes;
               fh <- fresh_key fds;
               _ <- puts (set dirents <[ dir := <[ name := inode ]> ents ]>);
               _ <- puts (set inodes <[inode := nil]>);
               _ <- puts (set fds <[fh := (inode, Write)]>);
               pure (fh, true)
           end

    | Append fh p' =>
      let! (inode, _) <- lookup fds fh;
      bs <- readFd fh Write;
      let! (s, alloc) <- readSome (fun st => Data.getAlloc p'.(slice.ptr) st.(heap));
           bs' <- unwrap (Data.getSliceModel p' alloc);
           _ <- unwrap (lock_available Reader s);
           puts (set inodes <[ inode := bs ++ bs' ]>)

    | Delete dir name =>
      let! (s, _) <- lookup dirlocks dir;
           _ <- unwrap (lock_available Writer s);
           ents <- lookup dirents dir;
           _ <- unwrap (ents !! name);
       puts (set dirents <[ dir := map_delete name ents ]>)

    (* TODO: eventually implement these (currently unused) *)
    | Truncate dir name => error
    | AtomicCreate dir name p => error

    | Rename dir1 name1 dir2 name2 =>
      ents1 <- lookup dirents dir1;
        inode1 <- unwrap (ents1 !! name1);
        ents2 <- lookup dirents dir2;
        _ <- is_none (ents2 !! name2);
        _ <- puts (set dirents <[ dir1 := map_delete name1 ents1 ]>);
        _ <- puts (set dirents <[ dir2 := <[ name2 := inode1 ]> ents2 ]>);
        pure tt

    | Link dir1 name1 dir2 name2 =>
      ents1 <- lookup dirents dir1;
        inode1 <- unwrap (ents1 !! name1);
        ents2 <- lookup dirents dir2;
        match ents2 !! name2 with
        | Some _ => pure false
        | None =>
          _ <- puts (set dirents <[ dir2 := <[ name2 := inode1 ]> ents2 ]>);
            pure true
        end
    end.

    Definition crash_step : relation State State unit :=
    _ <- puts (set fds (fun _ => ∅));
        _ <- puts (set heap (fun _ => ∅));
        _ <- puts (set dirlocks (fmap (fun _ => (Unlocked, tt))));
        pure tt.

  Theorem crash_step_non_err s res :
      crash_step s res ->
      res <> Err.
  Proof.
    destruct res; eauto.
    unfold crash_step, puts, pure; simpl; intros.
    repeat match goal with
           | [ H: _ \/ _ |- _ ] => destruct H
           | _ => progress propositional
           | _ => discriminate
           end.
  Qed.

  Global Instance empty_fs : Empty State :=
    {| heap := ∅;
       dirlocks := ∅;
       dirents := ∅;
       fds := ∅;
       inodes := ∅; |}.

  End GoModel.
End FS.
