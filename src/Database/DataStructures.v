From stdpp Require gmap.
From stdpp Require Import fin_maps.

From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations.

From Classes Require Import EqualDec.
From Coq Require Import NArith.
Import EqNotations.

Set Implicit Arguments.

Axiom IORef : Type -> Type.
Axiom Array : Type -> Type.
(* Hashtables always use uint64 as the key type since the Haskell interpreter
needs to statically know the type in order to resolve Hashable and Eq instances

We could instead use a type code and dispatch on that. *)
Axiom HashTable : forall (V:Type), Type.
Axiom LockRef : Type.

Axiom sigIORef_eq_dec : EqualDec (sigT IORef).
Axiom sigArray_eq_dec : EqualDec (sigT Array).
Axiom sigHashTable_eq_dec : EqualDec (sigT HashTable).
Axiom lockRef_eq_dec : EqualDec LockRef.

Existing Instances sigIORef_eq_dec sigArray_eq_dec sigHashTable_eq_dec lockRef_eq_dec.

Module Var.
  Inductive t :=
  .

  Definition ty (x:t) : Type :=
    match x with
    end.
End Var.

Instance var_eqdec : EqualDec Var.t := _.

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

Inductive LockMode := Reader | Writer.

Module Data.
  Inductive Op : Type -> Type :=
  (* generic variable operations *)
  | GetVar : forall (v:Var.t), Op (Var.ty v)
  | SetVar : forall (v:Var.t), Var.ty v -> Op unit

  (* arbitrary references *)
  | NewIORef : forall T, T -> Op (IORef T)
  | ReadIORef : forall T, IORef T -> Op T
  | WriteIORef : forall T, IORef T -> forall (args:NonAtomicArgs T), Op (retT args unit)

  (* arrays *)
  | NewArray : forall T, Op (Array T)
  | ArrayLength : forall T, Array T -> Op uint64
  | ArrayGet : forall T, Array T -> uint64 -> Op T
  | ArrayAppend : forall T, Array T -> T -> Op unit

  (* hashtables *)
  | NewHashTable :
      forall V, Op (HashTable V)
  | HashTableAlter :
      forall V, HashTable V -> uint64 -> (option V -> option V) -> Op unit
  | HashTableLookup :
      forall V, HashTable V -> uint64 -> Op (option V)
  (* TODO: this operation is definitely not thread-safe; should use the non-atomic op combinators on the entire hashtable API *)
  | HashTableReadAll :
      forall V, HashTable V -> Op (Array (uint64*V))

  (* locks *)
  | NewLock : Op LockRef (* will be unlocked *)
  | LockAcquire : LockMode -> LockRef -> Op unit
  | LockRelease : LockMode -> LockRef -> Op unit

  | PrintByteString : String.string -> ByteString -> Op unit
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op)) (at level 0, op at level 200).

    Definition get (var: Var.t) : proc (Var.ty var) :=
      Call! GetVar var.

    Definition set_var (var: Var.t) (v: Var.ty var) : proc unit :=
      Call! SetVar var v.

    Definition newIORef {T} (v:T) : proc (IORef T) :=
      Call! NewIORef v.

    Definition readIORef T (ref:IORef T) : proc T :=
      Call! ReadIORef ref.

    Definition writeIORef T (ref:IORef T) (v:T) : proc unit :=
      nonAtomicOp (fun args => inject (WriteIORef ref args)) v.

    (* non-atomic modify (this immediately follows from Read and Write each not
  being atomic) *)
    Definition modifyIORef T (ref:IORef T) (f: T -> T) : proc unit :=
      Bind (Call! ReadIORef ref)
           (fun x => writeIORef ref (f x)).

    Definition newArray T : proc _ :=
      Call! NewArray T.

    Definition arrayAppend T (a: Array T) (v:T) : proc unit :=
      Call! ArrayAppend a v.

    Definition arrayLength T (a: Array T) : proc uint64 :=
      Call! ArrayLength a.

    Definition arrayGet T (a: Array T) (ix:uint64) : proc T :=
      Call! ArrayGet a ix.

    Definition newHashTable V : proc _ :=
      Call! NewHashTable V.

    Definition hashTableAlter V h k f : proc _ :=
      Call! @HashTableAlter V h k f.

    Definition hashTableLookup V h k : proc _ :=
      Call! @HashTableLookup V h k.

    Definition hashTableReadAll V h : proc _ :=
      Call! @HashTableReadAll V h.

    Definition newLock : proc _ :=
      Call! NewLock.

    Definition lockAcquire m r : proc _ :=
      Call! LockAcquire m r.

    Definition lockRelease m r : proc _ :=
      Call! LockRelease m r.

    Definition printByteString key bs : proc _ :=
      Call! PrintByteString key bs.

  End OpWrappers.

  (* this is represented as an inductive rather than a combination of ObjΣ and a
  boolean state to make misuse harder (there's no reasonable way to use the
  state without knowing the status) *)
  Inductive NonAtomicState ObjΣ : Type :=
  | Clean (s:ObjΣ)
  | Dirty (s:ObjΣ).

  Record DynMap A (Ref: A -> Type) (Model: A -> Type) :=
    { dynMap : sigT Ref -> option (sigT Model);
      dynMap_wf : forall T v, match dynMap (existT T v) with
                         | Some (existT T' _) => T' = T
                         | None => True
                         end; }.

  Definition hashtableM V := gmap.gmap uint64 V.

  Inductive LockStatus := Locked | ReadLocked (num:nat) | Unlocked.

  Record State : Type :=
    mkState { vars: forall (var:Var.t), Var.ty var;
              iorefs: DynMap IORef (fun T => NonAtomicState T);
              arrays: DynMap Array list;
              hashtables: DynMap HashTable hashtableM;
              locks: LockRef -> option LockStatus; }.

  Instance _eta : Settable _ :=
    mkSettable (constructor mkState
                            <*> vars
                            <*> iorefs
                            <*> arrays
                            <*> hashtables
                            <*> locks)%set.

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

  Definition upd_vars (var: Var.t) (v: Var.ty var) (vars: forall var, Var.ty var) :
    forall var, Var.ty var :=
    fun var' => match var == var' with
             | left H => rew [Var.ty] H in v
             | right _ => vars var'
             end.

  Definition upd_locks (r:LockRef) (v:LockStatus) (ls: LockRef -> option LockStatus) : LockRef -> option LockStatus :=
    fun r' => if r == r' then Some v else ls r'.

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

  Definition alter_map V (m: hashtableM V)
             (k:uint64) (f: option V -> option V) : hashtableM V :=
    partial_alter f k m.

  Close Scope option_monad.

  Import RelationNotations.

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

  (* returns [Some s'] when the lock should be acquired to status s', and None
  if the lock would block *)
  Definition lock_acquire (m:LockMode) (s:LockStatus) : option LockStatus :=
    match m, s with
    | Reader, ReadLocked n => Some (ReadLocked (S n))
    (* note that the number is one less than the number of readers, so that
       ReadLocked 0 means something *)
    | Reader, Unlocked => Some (ReadLocked 0)
    | Writer, Unlocked => Some Locked
    | _, _ => None
    end.

  (* returns [Some s'] when the lock should be released to status s', and None if this usage is an error *)
  Definition lock_release (m:LockMode) (s:LockStatus) : option LockStatus :=
    match m, s with
    | Reader, ReadLocked 0 => Some Unlocked
    | Reader, ReadLocked (S n) => Some (ReadLocked n)
    | Writer, Locked => Some Unlocked
    | _, _ => None
    end.

  (* sanity check lock definitions: if you can acquire a lock, you can always
  release it the same way and get back to where you started *)
  Lemma lock_acquire_release m s :
    forall s', lock_acquire m s = Some s' ->
          lock_release m s' = Some s.
  Proof.
    destruct m, s; simpl; inversion 1; auto.
  Qed.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | GetVar v => reads (fun s => vars s v)
    | SetVar v x => puts (set vars (upd_vars v x))
    | NewIORef x =>
      r <- such_that (fun s r => getDyn s.(iorefs) r = None);
        _ <- puts (set iorefs (updDyn r (Clean x)));
        pure r
    | WriteIORef v x =>
      obj_s <- readSome (fun s => getDyn s.(iorefs) v);
        nonAtomicStep
          x obj_s
          (* TODO: it would be really nice to abstract away this notion of
          getters/setters for state so that we don't have to use relations
          everywhere and can just use state transformers, very similar to lens.
          For example, right now these semantics are technically allowed to use
          the entire state to update this object, but it should be apparent from
          the lenses used that the semantics depends only on the lens {iorefs,
          set iorefs} |> {getDyn v, updDyn v} *)
          (fun refS => puts (set iorefs (updDyn v (Dirty refS))))
          (fun refS x => puts (set iorefs (updDyn v (Clean refS))))
    | ReadIORef v =>
      obj_s <- readSome (fun s => getDyn s.(iorefs) v);
        readClean obj_s
    | NewArray T =>
      r <- such_that (fun s r => getDyn s.(arrays) r = None);
        _ <- puts (set arrays (updDyn r (@nil T)));
        pure r
    | ArrayAppend v x =>
      l0 <- readSome (fun s => getDyn s.(arrays) v);
        puts (set arrays (updDyn v (l0 ++ x::nil)%list))
    | ArrayLength v =>
      l <- readSome (fun s => getDyn s.(arrays) v);
        pure (fromNum (length l))
    | ArrayGet v i =>
      l0 <- readSome (fun s => getDyn s.(arrays) v);
        readSome (fun _ => List.nth_error l0 (toNum i))
    | NewHashTable V =>
      r <- such_that (fun s r => getDyn s.(hashtables) r = None);
        _ <- puts (set hashtables (updDyn r empty));
        pure r
    | HashTableLookup v k =>
      m <- readSome (fun s => getDyn s.(hashtables) v);
        pure (m !! k)
    | HashTableAlter v k f =>
      m <- readSome (fun s => getDyn s.(hashtables) v);
        _ <- puts (set hashtables (updDyn v (alter_map m k f)));
        pure tt
    | HashTableReadAll h =>
      m <- readSome (fun s => getDyn s.(hashtables) h);
        a <- such_that (fun s a => getDyn s.(arrays) a = None);
        let els : list (uint64*_) := map_to_list m in
        _ <- puts (set arrays (updDyn a els));
        pure a
    | NewLock =>
      r <- such_that (fun s r => s.(locks) r = None);
        _ <- puts (set locks (upd_locks r Unlocked));
        pure r
    | LockAcquire m r =>
      v <- readSome (fun s => s.(locks) r);
        match lock_acquire m v with
        | Some s' => puts (set locks (upd_locks r s'))
        | None =>
          (* disabled transition; will only become available when the lock
             is freed by its owner *)
          none
        end
    | LockRelease m r =>
      v <- readSome (fun s => s.(locks) r);
        match lock_release m v with
        | Some s' => puts (set locks (upd_locks r s'))
        | None => error (* attempt to free the lock incorrectly *)
        end
    | PrintByteString _ _ => identity
    end.

  Definition vars0 (v:Var.t) : Var.ty v :=
    match v with
    end.

  Global Instance empty_dynmap A Ref Model : Empty (@DynMap A Ref Model).
  refine {| dynMap := fun _ => None; |}.
  intros; auto.
  Defined.

  Instance empty_state : Empty State.
  refine {| vars := vars0 ;
            iorefs := ∅ ;
            arrays := ∅ ;
            hashtables := ∅ ;
            locks := fun _ => None ;
         |}.
  Defined.

  Definition crash_step : relation State State unit :=
    puts (fun _ => ∅).

End Data.
