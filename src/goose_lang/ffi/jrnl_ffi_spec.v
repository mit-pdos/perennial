(* This defines the jrnl FFI layer's semantics (i.e., how the state of the
   journal is represented, and how operations/crashes affect it. Thus, this spec
   is trusted. *)

From iris.algebra Require Import auth frac agree excl csum.
From Perennial.algebra Require Import auth_map.
From RecordUpdate Require Import RecordSet.
Require Import Coq.Logic.Classical_Prop.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.base_logic.lib Require Import ghost_var.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.
From Perennial.goose_lang.lib.struct Require Import struct.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.program_proof Require Import addr_proof buf.buf_proof.

Section recoverable.
  Context {Σ:Type}.
  Context `{INH: Inhabited Σ}.
  Inductive RecoverableState :=
    | Closed (s:Σ)
    | Opened (s:Σ)
  .

  Definition recoverable_model : ffi_model :=
    mkFfiModel (RecoverableState) () (populate (Closed (inhabitant INH))) _.

  Local Existing Instance recoverable_model.

  Context {ext:ffi_syntax}.

  Definition openΣ : transition (state*global_state) Σ :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Opened s => ret s
                           | _ => undefined
                           end).

  Definition modifyΣ (f:Σ -> Σ) : transition (state*global_state) unit :=
    bind openΣ (λ s, modify (prod_map (set world (λ _, Opened (f s))) id)).

  Definition open : transition (state*global_state) Σ :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Closed s => bind (modify (prod_map (set world (fun _ => Opened s)) id))
                                             (fun _ => ret s)
                           | _ => undefined
                           end).

  Definition close : transition (RecoverableState) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s | Closed s => modify (fun _ => Closed s)
                           end).

  Global Instance Recoverable_inhabited : Inhabited RecoverableState := populate (Closed (inhabitant INH)).
End recoverable.

Arguments RecoverableState Σ : clear implicits.
Arguments recoverable_model Σ : clear implicits.

Definition ty_ := forall (val_ty:val_types), @ty val_ty.
(* TODO: slice should not require an entire ext_ty *)
Definition sliceT_ (t: ty_) : ty_ := λ val_ty, prodT (arrayT (t _)) uint64T.
Definition blockT_: ty_ := sliceT_ (λ val_ty, byteT).

Inductive JrnlOp :=
  | ReadBufOp (* jrnl, addr *)
  | ReadBitOp (* jrnl, addr *)
  | OverWriteOp (* jrnl, addr, data tuple *)
  | OverWriteBitOp (* jrnl, addr, bool *)
  | OpenOp (* (no arguments) *)
  | MkAllocOp (* max *)
  | MarkUsedOp (* alloc, idx *)
  | FreeNumOp (* alloc, idx *)
  | AllocOp (* alloc *)
.

Instance eq_JrnlOp : EqDecision JrnlOp.
Proof. solve_decision. Defined.

Instance JrnlOp_fin : Countable JrnlOp.
Proof. solve_countable JrnlOp_rec 8%nat. Qed.

Definition jrnl_op : ffi_syntax.
Proof. refine (mkExtOp JrnlOp _ _ Empty_set _ _). Defined.

Inductive Jrnl_ty :=
 | JrnlT
 | AllocT.

Instance jrnl_val_ty: val_types :=
  {| ext_tys := Jrnl_ty; |}.

Section jrnl.
  Existing Instances jrnl_op jrnl_val_ty.

  Inductive obj :=
    | objBit (b: bool)
    | objBytes (data: list u8).

  Definition val_of_obj' o :=
    match o with
    | objBit b => #b
    | objBytes o => val_of_list ((λ u, LitV (LitByte u)) <$> o)
    end.

  Definition blkno := u64.
  Definition kind := bufDataKind.

  Definition objSz o : nat :=
    match o with
    | objBit b => 1
    | objBytes o => 8 * (length o)
    end.

  (* The only operations that can be called outside an atomically block are OpenOp and MkAlloc *)
  Inductive jrnl_ext_tys : @val jrnl_op -> (ty * ty) -> Prop :=
  | JrnlOpenOpType :
      jrnl_ext_tys (λ: "v", ExternalOp OpenOp (Var "v"))%V (unitT, extT JrnlT)
  | JrnlMkAllocOpType :
      jrnl_ext_tys (λ: "v", ExternalOp MkAllocOp (Var "v"))%V (baseT uint64BT, extT AllocT).

  Instance jrnl_ty: ext_types jrnl_op :=
    {| val_tys := jrnl_val_ty;
       get_ext_tys := jrnl_ext_tys |}.

  Definition addrT : ty := impl.struct.t (impl.struct.decl [
    "Blkno" :: uint64T;
    "Off" :: uint64T
  ])%struct.

  Record jrnl_map : Type :=
    { jrnlData : gmap addr obj;
      jrnlKinds : gmap blkno kind;
      jrnlAllocs : gmap loc u64 }.

  Definition updateData m a o :=
    {| jrnlData := <[a := o]> (jrnlData m);
       jrnlKinds := jrnlKinds m;
       jrnlAllocs := jrnlAllocs m |}.

  Definition updateAllocs m l max :=
    {| jrnlData := jrnlData m;
       jrnlKinds := jrnlKinds m;
       jrnlAllocs := <[l := max]> (jrnlAllocs m) |}.

  Definition clearAllocs m :=
    {| jrnlData := jrnlData m;
       jrnlKinds := jrnlKinds m;
       jrnlAllocs := ∅ |}.

  Definition offsets_aligned (m : jrnl_map) :=
    (∀ a, a ∈ dom (gset _) (jrnlData m) →
     ∃ k, jrnlKinds m !! (addrBlock a) = Some k ∧ valid_off k (addrOff a)).

  Definition size_consistent_and_aligned a (o: obj) (jk: gmap blkno kind) :=
    ∃ k,
      jk !! (addrBlock a) = Some k ∧
      objSz o = bufSz k ∧
      valid_off k (addrOff a).

  Definition sizes_correct (m : jrnl_map) :=
    (∀ a o, jrnlData m !! a = Some o → ∃ k, jrnlKinds m !! (addrBlock a) = Some k ∧ objSz o = bufSz k).

  Definition wf_jrnl (m : jrnl_map) := offsets_aligned m ∧ sizes_correct m.

  Definition jrnl_state := RecoverableState (jrnl_map).

  Definition get_jrnl (s: jrnl_state) :=
    match s with
      | Closed j | Opened j => j
    end.

  Instance jrnl_model : ffi_model := recoverable_model jrnl_map (populate {| jrnlData := ∅;
                                                                             jrnlKinds := ∅;
                                                                             jrnlAllocs := ∅ |}).

  Existing Instances r_mbind r_fmap.

  Fixpoint tmapM {Σ A B} (f: A -> transition Σ B) (l: list A) : transition Σ (list B) :=
    match l with
    | [] => ret []
    | x::xs => b ← f x;
             bs ← tmapM f xs;
             ret (b :: bs)
    end.

  Definition allocIdent: transition (state*global_state) loc :=
    l ← allocateN;
    modify (prod_map (set heap <[l := Free #()]>) id);;
    ret l.

  Existing Instance fallback_genPred.

  Definition isFreshAlloc (σja: gmap loc u64) (l: loc) :=
    σja !! l = None.

  Theorem fresh_locs_isFreshAlloc σja :
    isFreshAlloc σja (fresh_locs (dom (gset loc) σja)).
  Proof.
    * apply (not_elem_of_dom (D := gset loc)).
        by apply fresh_locs_fresh.
  Qed.

  Definition gen_isFreshAlloc σja : {l: loc | isFreshAlloc σja l}.
  Proof.
    refine (exist _ (fresh_locs (dom (gset loc) σja)) _).
      by apply fresh_locs_isFreshAlloc.
  Defined.

  Global Instance mkalloc_gen σja : GenPred loc (state*global_state) (λ _, isFreshAlloc σja) :=
    fun _ σ => Some (gen_isFreshAlloc σja).

  Definition checkPf (Σ : Type) (P : Prop) {D: Decision P} : transition Σ P :=
    match decide P with
    | left Hpf => ret Hpf
    | _ => undefined
    end.

  Definition gen_lt (max: u64) (Hpf: 0 < int.Z max) : {n: u64 | int.Z n < int.Z max }.
  Proof. exists (U64 0). auto. Defined.

  Global Instance allocnum_gen (max : u64) Hpf : GenPred u64 (state*global_state) (λ _ n, int.Z n < int.Z max) :=
    fun _ σ => Some (gen_lt max Hpf).

  Global Instance decide_gt0 (m : u64) : Decision (0 < int.Z m).
  Proof. apply _. Qed.

  Definition jrnl_step (op:JrnlOp) (v:val) : transition (state*global_state) val :=
    match op, v with
    | OpenOp, _ =>
      j ← open;
      ret $ LitV $ LitBool $ true
    | ReadBufOp, PairV (#(LitInt blkno), (#(LitInt off), #()))%V #(LitInt sz) =>
      j ← openΣ;
      d ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      (* bit reads must be done with ReadBitOp *)
      check (k ≠ KindBit ∧ bufSz k = int.nat sz);;
      ret $ val_of_obj' d
    | ReadBitOp, (#(LitInt blkno), (#(LitInt off), #()))%V =>
      j ← openΣ;
      d ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      (* bit reads must be done with ReadBitOp *)
      check (k = KindBit);;
      ret $ val_of_obj' d
    | OverWriteOp, PairV (#(LitInt blkno), (#(LitInt off), #()))%V ov =>
      j ← openΣ;
      (* This only allows writing to addresses that already have defined contents *)
      _ ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      o ← suchThat (λ _ o, val_of_obj' o = ov);
      check (objSz o = bufSz k ∧ k ≠ KindBit);;
      modifyΣ (λ j, updateData j (Build_addr blkno off) o);;
      ret $ #()
    | OverWriteBitOp, PairV (#(LitInt blkno), (#(LitInt off), #()))%V ov =>
      j ← openΣ;
      (* This only allows writing to addresses that already have defined contents *)
      _ ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      o ← suchThat (λ _ o, val_of_obj' o = ov);
      check (objSz o = bufSz k ∧ k = KindBit);;
      modifyΣ (λ j, updateData j (Build_addr blkno off) o);;
      ret $ #()
    | MkAllocOp, #(LitInt max) =>
      j ← openΣ;
      l ← suchThat (λ _, isFreshAlloc (jrnlAllocs j));
      check (0 < int.Z max ∧ int.Z max `mod` 8 = 0) ;;
      modifyΣ (λ j, updateAllocs j l max);;
      ret $ (LitV $ LitLoc $ l)
    | MarkUsedOp, PairV #(LitLoc l) #(LitInt n) =>
      j ← openΣ;
      max ← unwrap (jrnlAllocs j !! l);
      check (int.Z n < int.Z max) ;;
      ret $ #()
    | FreeNumOp, PairV #(LitLoc l) #(LitInt n) =>
      j ← openΣ;
      max ← unwrap (jrnlAllocs j !! l);
      check (int.Z n ≠ 0 ∧ int.Z n < int.Z max) ;;
      ret $ #()
    | AllocOp, #(LitLoc l) =>
      j ← openΣ;
      max ← unwrap (jrnlAllocs j !! l);
      Hpf ← @checkPf _ (0 < int.Z max) (decide_gt0 max);
      n ← @suchThat _ _ (λ _ n, int.Z n < int.Z max) (allocnum_gen _ Hpf);
      ret $ #(LitInt n)
    | _, _ => undefined
    end.


  Definition crash_step : transition (ffi_state) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s | Closed s => modify (fun _ => Closed (clearAllocs s))
                           end).

  Instance jrnl_semantics : ffi_semantics jrnl_op jrnl_model :=
    {| ffi_step := jrnl_step;
       ffi_crash_step := fun s s' =>
                      relation.denote crash_step s s' tt; |}.
End jrnl.


