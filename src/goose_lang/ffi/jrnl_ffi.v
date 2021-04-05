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

  Context {ext:ext_op}.

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
Proof.
  solve_decision.
Defined.

Instance JrnlOp_fin : Countable JrnlOp.
Proof.
  solve_countable JrnlOp_rec 8%nat.
Qed.

Definition jrnl_op : ext_op.
Proof.
  refine (mkExtOp JrnlOp _ _).
Defined.

(* Should addrs be opaque? I think not *)
Inductive Jrnl_ty :=
 | JrnlT
 | AllocT.

Instance jrnl_val_ty: val_types :=
  {| ext_tys := Jrnl_ty; |}.

Section jrnl.
  Existing Instances jrnl_op jrnl_val_ty.

  Inductive obj :=
    objBit (b: bool)
    | objBytes (data: list u8).

  Definition val_of_obj' o :=
    match o with
    | objBit b => #b
    | objBytes o => val_of_list ((λ u, LitV (LitByte u)) <$> o)
    end.

  Lemma val_of_list_inj o1 o2:
    val_of_list o1 = val_of_list o2 →
    o1 = o2.
  Proof.
    revert o2.
    induction o1 => o2.
    - rewrite //=. destruct o2; try congruence.
      inversion 1.
    - rewrite //=. destruct o2; try inversion 1.
      subst. naive_solver.
  Qed.

  Lemma val_of_obj'_inj o1 o2:
    val_of_obj' (objBytes o1) = val_of_obj' (objBytes o2) →
    o1 = o2.
  Proof.
    rewrite /=.
    intros Hval%val_of_list_inj.
    apply fmap_inj in Hval; eauto.
    intros ??. inversion 1; eauto.
  Qed.

  Definition blkno := u64.
  Definition kind := bufDataKind.

  Definition objSz o : nat :=
    match o with
    | objBit b => 1
    | objBytes o => 8 * (length o)
    end.

  Lemma val_of_obj'_inj2 o1 o k:
    val_of_obj' (objBytes o1) = val_of_obj' o →
    objSz (objBytes o1) = bufSz k →
    k ≠ KindBit →
    o = objBytes o1.
  Proof.
    destruct o.
    - rewrite /val_of_obj'; destruct o1 => //=.
    - intros ?%val_of_obj'_inj; eauto. congruence.
  Qed.

  Lemma val_of_obj'_inj3 o1 o:
    val_of_obj' (objBit o1) = val_of_obj' o →
    o = objBit o1.
  Proof.
    destruct o.
    - rewrite /val_of_obj'; destruct o1 => //=; congruence.
    - rewrite //=.
      rewrite /val_of_list; destruct data => //=.
  Qed.

  (* The only operations that can be called outside an atomically block are OpenOp and MkAlloc *)
  Inductive jrnl_ext_tys : @val jrnl_op -> (ty * ty) -> Prop :=
  | JrnlOpenOpType t :
      jrnl_ext_tys (λ: "v", ExternalOp OpenOp (Var "v"))%V (refT t, extT JrnlT)
  | JrnlMkAllocOpType :
      jrnl_ext_tys (λ: "v", ExternalOp AllocOp (Var "v"))%V (baseT uint64BT, extT AllocT).

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

  (* TODO: do we need to enforce that every valid offset in a block has some data? *)
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
    l ← allocateN 1;
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
  Proof.
    exists (U64 0).
    auto.
  Defined.

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
      check (0 < int.Z max ) ;;
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
      ret $ #()
    | _, _ => undefined
    end.


  Definition crash_step : transition (ffi_state) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s | Closed s => modify (fun _ => Closed (clearAllocs s))
                           end).

  Instance jrnl_semantics : ext_semantics jrnl_op jrnl_model :=
    {| ext_step := jrnl_step;
       ext_crash := fun s s' =>
                      relation.denote crash_step s s' tt; |}.
End jrnl.


Definition openR := csumR (prodR fracR (agreeR (leibnizO unitO))) (agreeR (leibnizO unitO)).
Definition jrnl_opened : openR := Cinr (to_agree tt).

Class jrnlG Σ :=
  { jrnlG_open_inG :> inG Σ openR;
    jrnlG_open_name : gname;
    jrnlG_data_inG :> mapG Σ addr obj;
    jrnlG_data_name: gname;
    jrnlG_kinds_inG :> inG Σ (agreeR (leibnizO (gmap blkno kind)));
    jrnlG_kinds_name: gname;
    jrnlG_dom_inG :> inG Σ (agreeR (leibnizO (gset addr)));
    jrnlG_dom_name: gname;
    jrnlG_crash_toks_inG :> mapG Σ addr unit;
    jrnlG_crash_toks_name: gname;
    jrnlG_full_crash_tok_inG :> ghost_varG Σ unit;
    jrnlG_full_crash_tok_name: gname;
    jrnlG_allocs_inG :> mapG Σ loc u64;
    jrnlG_allocs_name : gname;
  }.

Class jrnl_preG Σ :=
  { jrnlG_preG_open_inG :> inG Σ openR;
    jrnlG_preG_data_inG:> mapG Σ addr obj;
    jrnlG_preG_kinds_inG:> inG Σ (agreeR (leibnizO (gmap blkno kind)));
    jrnlG_preG_dom_inG:> inG Σ (agreeR (leibnizO (gset addr)));
    jrnlG_preG_crash_toks_inG:> mapG Σ addr unit;
    jrnlG_preG_full_crash_tok_inG :> ghost_varG Σ unit;
    jrnlG_preG_allocs_inG :> mapG Σ loc u64;
  }.

Definition jrnlΣ : gFunctors :=
  #[GFunctor openR; mapΣ addr obj;
    GFunctor (agreeR (leibnizO (gmap blkno kind)));
    GFunctor (agreeR (leibnizO (gset addr)));
    mapΣ addr unit;
    ghost_varΣ unit;
    mapΣ loc u64
   ].

Instance subG_jrnlG Σ: subG jrnlΣ Σ → jrnl_preG Σ.
Proof. solve_inG. Qed.

Record jrnl_names :=
  { jrnl_names_open: gname;
    jrnl_names_data: gname;
    jrnl_names_kinds: gname;
    jrnl_names_dom: gname;
    jrnl_names_crash: gname;
    jrnl_names_full_crash: gname;
    jrnl_names_allocs: gname;
  }.

Definition jrnl_get_names {Σ} (jG: jrnlG Σ) :=
  {| jrnl_names_open := jrnlG_open_name;
     jrnl_names_data := jrnlG_data_name;
     jrnl_names_kinds := jrnlG_kinds_name;
     jrnl_names_dom := jrnlG_dom_name;
     jrnl_names_crash := jrnlG_crash_toks_name;
     jrnl_names_full_crash := jrnlG_full_crash_tok_name;
     jrnl_names_allocs := jrnlG_allocs_name;
|}.

Definition jrnl_update {Σ} (jG: jrnlG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
     jrnlG_dom_inG := jrnlG_dom_inG;
     jrnlG_dom_name := (jrnl_names_dom names);
     jrnlG_crash_toks_inG := jrnlG_crash_toks_inG;
     jrnlG_crash_toks_name := (jrnl_names_crash names);
     jrnlG_full_crash_tok_inG := jrnlG_full_crash_tok_inG;
     jrnlG_full_crash_tok_name := (jrnl_names_full_crash names);
     jrnlG_allocs_inG := jrnlG_allocs_inG;
     jrnlG_allocs_name := (jrnl_names_allocs names);
  |}.

Definition jrnl_update_pre {Σ} (jG: jrnl_preG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_preG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_preG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_preG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
     jrnlG_dom_inG := jrnlG_preG_dom_inG;
     jrnlG_dom_name := (jrnl_names_dom names);
     jrnlG_crash_toks_inG := jrnlG_preG_crash_toks_inG;
     jrnlG_crash_toks_name := (jrnl_names_crash names);
     jrnlG_full_crash_tok_inG := jrnlG_preG_full_crash_tok_inG;
     jrnlG_full_crash_tok_name := (jrnl_names_full_crash names);
     jrnlG_allocs_inG := jrnlG_preG_allocs_inG;
     jrnlG_allocs_name := (jrnl_names_allocs names);
  |}.

Definition jrnl_open {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (jrnl_opened).
Definition jrnl_closed_frag {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_closed_auth {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_kinds {Σ} {lG: jrnlG Σ} σj : iProp Σ :=
 (own (jrnlG_kinds_name) (to_agree (σj : leibnizO (gmap blkno kind)))).
Definition jrnl_kinds_lb {Σ} {lG: jrnlG Σ} (σj : gmap blkno kind) : iProp Σ :=
 (∃ σj', ⌜ σj ⊆ σj' ⌝ ∧ own (jrnlG_kinds_name) (to_agree (σj' : leibnizO (gmap blkno kind)))).
Definition jrnl_mapsto {Σ} {lG: jrnlG Σ} a q v : iProp Σ :=
  ptsto_mut (jrnlG_data_name) a q v ∗
  (∃ σj,  ⌜ size_consistent_and_aligned a v σj ⌝ ∗ jrnl_kinds σj).
Definition jrnl_crash_tok {Σ} {lG: jrnlG Σ} a : iProp Σ :=
  ptsto_mut (jrnlG_crash_toks_name) a 1 tt.
Definition jrnl_dom {Σ} {lG: jrnlG Σ} (σ: gset addr) : iProp Σ :=
  own (jrnlG_dom_name) (to_agree (σ: leibnizO (gset addr))).
Definition jrnl_full_crash_tok {Σ} {lG: jrnlG Σ} : iProp Σ :=
  ghost_var (jrnlG_full_crash_tok_name) 1 tt.
Definition jrnl_alloc {Σ} {lG: jrnlG Σ} (l: loc) (v : u64) : iProp Σ :=
  ptsto_ro (jrnlG_allocs_name) l v.
Definition jrnl_alloc_map {Σ} {lG: jrnlG Σ} (σ: gmap loc u64) : iProp Σ :=
  [∗ map] l ↦ v ∈ σ, jrnl_alloc l v.

Section jrnl_interp.
  Existing Instances jrnl_op jrnl_model jrnl_val_ty.

  Definition jrnl_state_ctx {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ⌜ wf_jrnl m ⌝ ∗
      map_ctx jrnlG_data_name 1 (jrnlData m) ∗
      jrnl_kinds (jrnlKinds m) ∗
      jrnl_dom (dom (gset _) (jrnlData m)) ∗
      map_ctx jrnlG_allocs_name 1 (jrnlAllocs m).

  Definition jrnl_ctx {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_ctx s
    | Closed s => jrnl_closed_auth ∗ jrnl_state_ctx s
    end.

  Definition jrnl_crash_ctx {Σ} {jG: jrnlG Σ} : iProp Σ :=
    ∃ m, ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
          map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
          jrnl_full_crash_tok.

  Definition jrnl_state_start {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_mapsto a 1 v) ∗
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
    map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
    jrnl_kinds (jrnlKinds m) ∗
    jrnl_dom (dom (gset _) (jrnlData m)) ∗
    jrnl_full_crash_tok.


  Definition jrnl_state_restart {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
    map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
    jrnl_kinds (jrnlKinds m) ∗
    jrnl_dom (dom (gset _) (jrnlData m)) ∗
    jrnl_full_crash_tok.

  Definition jrnl_start {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_start s
    | Closed s => jrnl_closed_frag ∗ jrnl_state_start s
    end.

  Definition jrnl_restart {Σ} (jG: jrnlG Σ) (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_restart s
    | Closed s => jrnl_closed_frag ∗ jrnl_state_restart s
    end.

  Program Instance jrnl_interp : ffi_interp jrnl_model :=
    {| ffiG := jrnlG;
       ffi_names := jrnl_names;
       ffi_get_names := @jrnl_get_names;
       ffi_update := @jrnl_update;
       ffi_get_update := _;
       ffi_ctx := @jrnl_ctx;
       ffi_global_ctx _ _ _ := True%I;
       ffi_start Σ G w _ := @jrnl_start Σ G w;
       ffi_restart := @jrnl_restart;
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @jrnlG_data_inG _ hF1 = @jrnlG_data_inG _ hF2 ∧
                                             @jrnlG_kinds_inG _ hF1 = @jrnlG_kinds_inG _ hF2 ∧
                                             @jrnlG_dom_inG _ hF1 = @jrnlG_dom_inG _ hF2 ∧
                                           jrnl_names_data (jrnl_get_names hF1) =
                                           jrnl_names_data (jrnl_get_names hF2) ∧
                                           jrnl_names_kinds (jrnl_get_names hF1) =
                                           jrnl_names_kinds (jrnl_get_names hF2) ∧
                                           jrnl_names_dom (jrnl_get_names hF1) =
                                           jrnl_names_dom (jrnl_get_names hF2) ⌝%I;
    |}.
  Next Obligation. intros ? [] [] => //=. Qed.
  Next Obligation. intros ? [] => //=. Qed.
  Next Obligation. intros ? [] => //=. Qed.

End jrnl_interp.


Section jrnl_lemmas.
  Context `{lG: jrnlG Σ}.

  Global Instance jrnl_ctx_Timeless lg: Timeless (jrnl_ctx lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_start_Timeless lg: Timeless (jrnl_start lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_restart_Timeless lg: Timeless (jrnl_restart _ lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_open_Persistent : Persistent (jrnl_open).
  Proof. rewrite /jrnl_open/jrnl_opened. apply own_core_persistent. rewrite /CoreId//=. Qed.

  Global Instance jrnl_kinds_lb_Persistent kmap : Persistent (jrnl_kinds_lb kmap).
  Proof. refine _. Qed.

  Definition jrnl_full_crash_tok_excl :
    jrnl_full_crash_tok -∗ jrnl_full_crash_tok -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "[$] [$]") as %[Hval _].
    rewrite //= in Hval.
  Qed.

  Lemma jrnl_closed_auth_opened :
    jrnl_closed_auth -∗ jrnl_open -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma jrnl_closed_token_open :
    jrnl_closed_auth -∗ jrnl_closed_frag ==∗ jrnl_open.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (jrnl_opened) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma jrnl_ctx_unify_closed lg:
    jrnl_closed_frag -∗ jrnl_ctx lg -∗ ⌜ ∃ vs, lg = Closed vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hclosed_frag Hctx".
    iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
    iDestruct (jrnl_closed_auth_opened with "[$] [$]") as %[].
  Qed.

  Lemma jrnl_ctx_unify_opened lg:
    jrnl_open -∗ jrnl_ctx lg -∗ ⌜ ∃ vs, lg = Opened vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hopen Hctx".
    iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

   Lemma jrnl_dom_agree σ1 σ2:
     jrnl_dom σ1 -∗ jrnl_dom σ2 -∗ ⌜ σ1 = σ2 ⌝.
   Proof.
     iIntros "H1 H2".
     iDestruct (own_valid_2 with "H1 H2") as %Hval.
     apply to_agree_op_valid in Hval. iPureIntro. set_solver.
   Qed.

  Lemma jrnl_ctx_allocs_agree σja σ:
    jrnl_alloc_map σja -∗ jrnl_state_ctx σ -∗ ⌜ σja ⊆ jrnlAllocs σ ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H2" as "(_&_&_&_&Hctx)".
    destruct σ as [? ? σja'] => /=.
    rewrite /jrnl_alloc_map.
    rewrite map_subseteq_spec.
    iIntros (l v Hlookup).
    iDestruct (big_sepM_lookup with "H1") as "H"; eauto.
    iDestruct (map_ro_valid with "[$] [$]") as %?; eauto.
  Qed.

  Lemma jrnl_state_ctx_extract_pers m :
    jrnl_state_ctx m -∗
    ⌜ wf_jrnl m ⌝ ∗
      jrnl_kinds (jrnlKinds m) ∗
      jrnl_dom (dom (gset _) (jrnlData m)).
  Proof. iDestruct 1 as "($&?&$&$&?)". Qed.

End jrnl_lemmas.

From Perennial.goose_lang Require Import adequacy.

Program Instance jrnl_interp_adequacy:
  @ffi_interp_adequacy jrnl_model jrnl_interp jrnl_op jrnl_semantics :=
  {| ffi_preG := jrnl_preG;
     ffiΣ := jrnlΣ;
     subG_ffiPreG := subG_jrnlG;
     ffi_initP := λ σ _, ∃ m, σ = Closed m ∧ wf_jrnl m;
     ffi_update_pre := @jrnl_update_pre;
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ g (m&->&Hwf)). simpl.
  iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (map_init_many (jrnlData m)) as (γdata) "(Hdata_ctx&Hdata)".
  iMod (map_init_many ((λ _, tt) <$> jrnlData m)) as (γcrash) "(Hcrash_ctx&Hcrash)".
  iMod (own_alloc (to_agree (jrnlKinds m : leibnizO (gmap blkno kind)))) as (γkinds) "#Hkinds".
  { constructor. }
  iMod (own_alloc (to_agree (dom (gset _) (jrnlData m) : leibnizO (gset addr)))) as (γdom) "#Hdom".
  { constructor. }
  iMod (ghost_var_alloc ()) as (γfull) "Hfull".
  iMod (map_init_many (jrnlAllocs m)) as (γallocs) "(Hallocs_ctx&_)".
  iExists {| jrnl_names_open := γ1; jrnl_names_data := γdata; jrnl_names_kinds := γkinds;
             jrnl_names_dom := γdom;
             jrnl_names_crash := γcrash;
             jrnl_names_full_crash := γfull;
             jrnl_names_allocs := γallocs;
          |}.
  iFrame. iModIntro. iFrame "% #".
  rewrite assoc.
  iSplitL "H".
  { by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp. }
  rewrite /jrnl_state_start.
  rewrite big_sepM_fmap.
  iFrame.
  iDestruct (big_sepM.big_sepM_mono_with_inv with "Hkinds Hdata") as "(_&$)".
  iIntros (a x Hlookup) "(#Hkinds&Hpt)". iFrame "Hkinds".
  rewrite /jrnl_mapsto.
  rewrite /wf_jrnl/offsets_aligned/sizes_correct in Hwf.
  destruct Hwf as (Hoff&Hsize).
  edestruct Hsize as (k&Hlookup_kind&Hlen); eauto. iFrame.
  iExists _. iFrame "% #".
  iPureIntro. exists k.
  split_and!; eauto.
  edestruct (Hoff a); eauto.
  { apply elem_of_dom. eauto. }
  naive_solver.
Qed.
Next Obligation.
  iIntros (Σ σ σ' g Hcrash Hold) "Hinterp _".
  inversion Hcrash; subst.
  monad_inv. inversion H. subst. inversion H1. subst.
  destruct x; monad_inv.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iMod (map_init_many ((λ _, tt) <$> jrnlData s)) as (γcrash) "(Hcrash_ctx&Hcrash)".
    iMod (ghost_var_alloc ()) as (γfull) "Hfull".
    iMod (map_init_many ∅) as (γallocs) "(Hallocs_ctx&_)".
    iExists {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) ;
               jrnl_names_crash := γcrash;
               jrnl_names_full_crash := γfull;
               jrnl_names_allocs := γallocs;
            |}.
    iDestruct "Hinterp" as "(?&Hstate)".
    iDestruct (jrnl_state_ctx_extract_pers with "Hstate") as "(%&#?&#?)".
    iDestruct "Hstate" as "(?&?&?&?&?)".
    rewrite //=/jrnl_restart//=.
    iFrame. rewrite left_id comm -assoc. iSplitL ""; first eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    rewrite big_sepM_fmap.
    rewrite /jrnl_state_restart.
    rewrite /jrnl_crash_tok.
    rewrite /jrnl_full_crash_tok.
    rewrite //= /=. iFrame "# ∗".
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iMod (map_init_many ((λ _, tt) <$> jrnlData s)) as (γcrash) "(Hcrash_ctx&Hcrash)".
    iMod (ghost_var_alloc ()) as (γfull) "Hfull".
    iMod (map_init_many ∅) as (γallocs) "(Hallocs_ctx&_)".
    iExists {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) ;
               jrnl_names_crash := γcrash;
               jrnl_names_allocs := γallocs;
            |}.
    iDestruct "Hinterp" as "(?&Hstate)".
    iDestruct (jrnl_state_ctx_extract_pers with "Hstate") as "(%&#?&#?)".
    rewrite //=/jrnl_restart//=.
    iDestruct "Hstate" as "(?&?&?&?&?)".
    iFrame. rewrite left_id comm -assoc. iSplitL ""; first eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    rewrite big_sepM_fmap.
    rewrite /jrnl_state_restart.
    rewrite /jrnl_crash_tok.
    rewrite /jrnl_full_crash_tok.
    rewrite //=. iFrame "# ∗".
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance jrnl_spec_ext : spec_ext_op := {| spec_ext_op_field := jrnl_op |}.
Instance jrnl_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := jrnl_model |}.
Instance jrnl_spec_ext_semantics : spec_ext_semantics (jrnl_spec_ext) (jrnl_spec_ffi_model) :=
  {| spec_ext_semantics_field := jrnl_semantics |}.
Instance jrnl_spec_ffi_interp : spec_ffi_interp jrnl_spec_ffi_model :=
  {| spec_ffi_interp_field := jrnl_interp |}.
Instance jrnl_spec_ty : ext_types (spec_ext_op_field) := jrnl_ty.
Instance jrnl_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := jrnl_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := jrnl_interp_adequacy |}.

Context `{invG Σ}.
Context `{crashG Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.

Implicit Types K: spec_lang.(language.expr) → spec_lang.(language.expr).
Instance jrnlG0 : jrnlG Σ := refinement_spec_ffiG.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | [ H1: context[ match world ?σ with | _ => _ end ], Heq: world ?σ = _ |- _ ] =>
          rewrite Heq in H1
        end.

Notation spec_ext := jrnl_spec_ext.
Notation sstate := (@state (@spec_ext_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation shead_step := (@head_step (@spec_ext_op_field spec_ext)).
Notation sworld := (@world (@spec_ext_op_field spec_ext) (@spec_ffi_model_field jrnl_spec_ffi_model)).

Definition jrnl_sub_dom (σj1 σj2 : jrnl_map) : Prop :=
  (dom (gset _) (jrnlData σj1) = dom _ (jrnlData σj2) ∧ jrnlKinds σj1 ⊆ jrnlKinds σj2 ∧
   jrnlAllocs σj1 = jrnlAllocs σj2 ∧
  wf_jrnl σj1 ∧ wf_jrnl σj2).

Definition jrnl_sub_state (σj : jrnl_map) (s: sstate) : Prop :=
  (∃ sj, s.(world) = Opened sj ∧ jrnlData σj ⊆ jrnlData sj ∧ jrnlKinds σj = jrnlKinds sj ∧ jrnlAllocs σj ⊆ jrnlAllocs sj).

Definition jrnl_upd (σj: jrnl_map) (s: sstate) : sstate :=
  set sworld (λ s, Opened {| jrnlData := jrnlData σj ∪ (jrnlData $ get_jrnl s);
                             jrnlKinds := jrnlKinds $ get_jrnl s;
                             jrnlAllocs := jrnlAllocs $ (get_jrnl s) |}) s.

Definition always_steps (e: sexpr) (σj: jrnl_map) (e': sexpr) (σj': jrnl_map) : Prop :=
  (jrnlKinds σj = jrnlKinds σj') ∧
  (jrnl_sub_dom σj σj') ∧
  (∀ s g, jrnl_sub_state σj s →
           rtc (λ '(e, (s,g)) '(e', (s',g')), prim_step' e s g [] e' s' g' []) (e, (s,g)) (e', (jrnl_upd σj' s, g))).

Lemma jrnl_upd_sub σj s :
  jrnl_sub_state σj s →
  jrnl_upd σj s = s.
Proof.
  intros (sj&Heq1&Hsub1&Hsub2).
  rewrite /jrnl_upd.
  destruct s. rewrite /set//=. f_equal.
  rewrite /= in Heq1. rewrite Heq1. f_equal. destruct sj as [sjd [sjk sja]].
  f_equal => /=. apply map_subseteq_union; auto.
Qed.

Lemma jrnl_sub_state_upd σj1 σj2 s :
  jrnl_sub_state σj1 s →
  jrnlKinds σj1 = jrnlKinds σj2 →
  jrnlAllocs σj1 = jrnlAllocs σj2 →
  jrnl_sub_state σj2 (jrnl_upd σj2 s).
Proof.
  intros (sj&Heq&Hsub_data&Hsub_kinds&Hsub_allocs) Heq_kinds Heq_allocs.
  eexists; split; eauto => /=.
  split_and!.
  - apply map_union_subseteq_l.
  - rewrite Heq /= -Heq_kinds //.
  - rewrite Heq /= -Heq_allocs //.
Qed.

Lemma jrnl_upd_upd_sub_dom σj1 σj2 s :
  jrnl_sub_dom σj1 σj2 →
  jrnl_upd σj2 (jrnl_upd σj1 s) = jrnl_upd σj2 s.
Proof.
  intros (?&?).
  rewrite /jrnl_upd/set //=. do 3 f_equal.
  apply map_eq => i.
  destruct (jrnlData σj2 !! i) eqn:Hlookup.
  { erewrite lookup_union_Some_l; eauto.
    erewrite lookup_union_Some_l; eauto. }
  rewrite ?lookup_union_r //.
  apply not_elem_of_dom. apply not_elem_of_dom in Hlookup. rewrite H1. auto.
Qed.

Lemma jrnl_upd_idemp σj s :
  jrnl_upd σj (jrnl_upd σj s) = jrnl_upd σj s.
Proof.
  rewrite /jrnl_upd/set//=. do 3 f_equal.
  rewrite map_union_assoc map_union_idemp //.
Qed.

Lemma always_steps_refl e σj :
  wf_jrnl σj →
  always_steps e σj e σj.
Proof.
  intros. split_and! => //= s g Hsub.
  rewrite jrnl_upd_sub //.
Qed.

Lemma jrnl_sub_dom_trans σj1 σj2 σj3 :
  jrnl_sub_dom σj1 σj2 →
  jrnl_sub_dom σj2 σj3 →
  jrnl_sub_dom σj1 σj3.
Proof.
  intros (?&?&?&?&?) (?&?&?&?&?); split_and!; eauto.
  - congruence.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Lemma always_steps_trans e1 σj1 e2 σj2 e3 σj3 :
  always_steps e1 σj1 e2 σj2 →
  always_steps e2 σj2 e3 σj3 →
  always_steps e1 σj1 e3 σj3.
Proof.
  intros (Hkinds1&Hsub1&Hsteps1) (Hkinds2&Hsub2&Hsteps2).
  split_and!; first congruence.
  { eapply jrnl_sub_dom_trans; eassumption. }
  intros s g Hsub.
  eapply rtc_transitive.
  { eapply Hsteps1; eauto. }
  { assert (jrnl_upd σj3 s = jrnl_upd σj3 (jrnl_upd σj2 s)) as ->.
    { rewrite jrnl_upd_upd_sub_dom; eauto. }
    eapply Hsteps2; eauto.
    eapply jrnl_sub_state_upd; eauto.
    { destruct Hsub1 as (?&?&?&?).
      destruct Hsub2 as (?&?&?&?). congruence. }
  }
Qed.

Lemma insert_jrnl_upd a o σj s :
  a ∉ dom (gset _) (jrnlData σj) →
  jrnl_upd (updateData σj a o) s =
  jrnl_upd σj (jrnl_upd ({| jrnlData := {[ a := o]};
                           jrnlKinds := jrnlKinds σj;
                           jrnlAllocs := jrnlAllocs σj|}) s).
Proof.
  intros.
  rewrite /jrnl_upd/set/=. do 3 f_equal.
  rewrite insert_union_singleton_l.
  rewrite (map_union_comm ({[a := o]})) ?assoc //.
  apply map_disjoint_dom_2.
  rewrite dom_singleton. set_solver.
Qed.

Lemma always_steps_bind `{Hctx: LanguageCtx' (ext := @spec_ext_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K} e1 e2 σj1 σj2 :
  always_steps e1 σj1 e2 σj2 →
  always_steps (K e1) σj1 (K e2) σj2.
Proof.
  rewrite /always_steps.
  intros (?&?&Hstep). split_and!; eauto.
  intros s g Hsub. specialize (Hstep _ g Hsub).
  clear -Hstep Hctx.
  remember (e1, (s,g)) as ρ1 eqn:Hρ1.
  remember (e2, (jrnl_upd σj2 s,g)) as ρ2 eqn:Hρ2.
  revert Hρ1 Hρ2. destruct g.
  generalize (jrnl_upd σj2 s) as s'.
  revert e1 e2 s.
  induction Hstep.
  - intros. rewrite Hρ1 in Hρ2. inversion Hρ2. subst.
    apply rtc_refl.
  - intros. subst. destruct y as (e0'&s0'&[]).
    eapply rtc_l; last first.
    { eapply IHHstep; eauto. }
    simpl. eapply fill_step'. eauto.
Qed.

Lemma insert_jrnl_sub_state a o σj s:
  jrnl_sub_state (updateData σj a o ) s →
  s = (jrnl_upd ({| jrnlData := {[ a := o]};
                           jrnlKinds := jrnlKinds σj;
                           jrnlAllocs := jrnlAllocs σj|}) s).
Proof.
  rewrite /jrnl_sub_state /=.
  intros (sj&Heq1&Hsub1&Hsub2).
  rewrite /jrnl_upd/set. destruct s => //=. simpl in Heq1. f_equal.
  rewrite Heq1. f_equal.
  destruct sj; f_equal. apply map_eq.
  intros i => /=.
  destruct (decide (a = i)).
  - subst.
    transitivity (({[i := o]} : gmap addr obj) !! i).
    { rewrite lookup_singleton.
      eapply lookup_weaken; eauto. rewrite lookup_insert //=. }
    rewrite lookup_singleton. symmetry.
    apply lookup_union_Some_l.
    apply lookup_singleton.
  - rewrite lookup_union_r //.
    rewrite lookup_singleton_ne //=.
Qed.

Lemma wf_jrnl_extend σj a o:
  size_consistent_and_aligned a o (jrnlKinds σj) →
  wf_jrnl σj →
  wf_jrnl (updateData σj a o).
Proof.
  intros Haligned Hwf. rewrite /wf_jrnl.
  split.
  - rewrite /offsets_aligned => a' Hin.
    rewrite dom_insert_L in Hin. set_unfold in Hin. destruct Hin; subst.
    * simpl. destruct Haligned. naive_solver.
    * eapply Hwf; eauto.
  - rewrite /sizes_correct => a' Hin Hlookup.
    destruct (decide (a' = a)).
    { subst. rewrite lookup_insert in Hlookup. destruct Haligned. naive_solver. }
    rewrite lookup_insert_ne in Hlookup; auto.
    eapply Hwf; eauto.
Qed.

Lemma always_steps_extend e1 σj1 e2 σj2 a o :
  (a ∉ dom (gset _) (jrnlData σj2)) →
  size_consistent_and_aligned a o (jrnlKinds σj1) →
  always_steps e1 σj1 e2 σj2 →
  always_steps e1 (updateData σj1 a o)
               e2 (updateData σj2 a o).
Proof.
  intros Hdom Hconsistent (?&Hsub&Hstep).
  split_and!.
  - simpl. congruence.
  - destruct Hsub as (?&?&?&?&?). split_and! => //=.
    * rewrite ?dom_insert_L H2. set_solver.
    * apply wf_jrnl_extend; auto.
    * apply wf_jrnl_extend; auto. congruence.
  - intros s g Hsub_state.
    rewrite insert_jrnl_upd //.
    rewrite {1}(insert_jrnl_sub_state _ _ _ _ Hsub_state).
    apply Hstep.
    rewrite /jrnl_sub_state.
    destruct Hsub_state as (sj&Hworld&Hsub_data&?&Hsub_allocs).
    rewrite /jrnl_upd/set//=. rewrite Hworld /=.
    eexists; split_and!; eauto => /=.
    intros i => /=.
    specialize (Hsub_data i).
    destruct Hsub as (Hsub_data'&?).
    assert (a ∉ dom (gset _) (jrnlData σj1)) as Hdom' by (rewrite Hsub_data'; set_solver).
    destruct (decide (a = i)).
    * subst. apply not_elem_of_dom in Hdom'.
      rewrite Hdom' => //=. destruct (({[ i := o]} ∪ jrnlData sj) !! i) eqn:Heq; auto.
    * rewrite lookup_union_r ?lookup_singleton_ne //.
      rewrite lookup_insert_ne // in Hsub_data.
Qed.

Definition addr2val' (a : addr) : sval := (#(addrBlock a), (#(addrOff a), #()))%V.

Lemma always_steps_lifting_puredet K `{Hctx: LanguageCtx' (ext := @spec_ext_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K}:
  ∀ e0 σ0 e1 σ1 e2,
  (∀ σ g, prim_step' e1 σ g [] e2 σ g []) →
  always_steps e0 σ0 (K e1) σ1 →
  always_steps e0 σ0 (K e2) σ1.
Proof.
  intros e0 σ0 e1 σ1 e2 Hdet Hsteps.
  split_and!; eauto.
  { eapply Hsteps. }
  { eapply Hsteps. }
  intros s g Hsub.
  destruct Hsteps as (?&?&Hrtc).
  specialize (Hrtc _ g Hsub).
  eapply rtc_r; eauto.
  simpl. eapply fill_step'. eapply Hdet.
Qed.

Lemma always_steps_ReadBufOp a v (sz: u64) k σj:
  wf_jrnl σj →
  jrnlData σj !! a = Some v →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (k ≠ KindBit ∧ bufSz k = int.nat sz) →
  always_steps (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                           ReadBufOp
                           (PairV (addr2val' a) #sz))
               σj
               (val_of_obj' v)
               σj.
Proof.
  intros Hwf Hlookup1 Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite -H2. rewrite Hlookup2; eauto.
    econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite decide_True //=. }
Qed.

Lemma always_steps_ReadBitOp a v σj:
  wf_jrnl σj →
  jrnlData σj !! a = Some v →
  jrnlKinds σj !! (addrBlock a) = Some KindBit →
  always_steps (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                           ReadBitOp
                           (addr2val' a))
               σj
               (val_of_obj' v)
               σj.
Proof.
  intros Hwf Hlookup1 Hlookup2.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite -H2. rewrite Hlookup2; eauto.
    econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite //=. }
Qed.

Lemma val_of_obj'_bytes vs: val_of_obj' (objBytes vs) = val_of_list ((λ u : u8, #u) <$> vs).
Proof. rewrite //=. Qed.

Lemma val_of_obj'_bit (vs : bool) : val_of_obj' (objBit vs) = #vs.
Proof. rewrite //=. Qed.

Lemma wf_jrnl_updateData σj a vs vs_old k :
  wf_jrnl σj →
  jrnlData σj !! a = Some vs_old →
  jrnlKinds σj !! addrBlock a = Some k →
  objSz vs = bufSz k →
  wf_jrnl (updateData σj a vs).
Proof.
  intros Hwf Hlookup1 Hlookup2 Hsize.
  split.
  - rewrite /offsets_aligned => a' Hin.
    eapply Hwf. move: Hin. rewrite dom_insert_L.
    cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
    apply elem_of_dom. eauto.
  - rewrite /sizes_correct//= => a' o Hlookup'.
    destruct (decide (a' = a)).
    * subst. eexists; split; eauto. rewrite lookup_insert in Hlookup'. congruence.
    * eapply Hwf. rewrite lookup_insert_ne in Hlookup'; eauto.
Qed.

Lemma always_steps_OverWriteOp a vs k σj:
  wf_jrnl σj →
  is_Some (jrnlData σj !! a)  →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (objSz (objBytes vs) = bufSz k ∧ k ≠ KindBit) →
  always_steps (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                           OverWriteOp
                           (PairV (addr2val' a) (val_of_obj' (objBytes vs))))
               σj
               #()
               (updateData σj a (objBytes vs)).
Proof.
  intros Hwf (vs_old&Hlookup1) Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver.
    - rewrite //=. rewrite dom_insert_L.
      cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
      apply elem_of_dom. eauto.
    - eapply wf_jrnl_updateData; eauto. naive_solver.
  }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite H2 in Hlookup2.
    rewrite Hlookup2. econstructor; eauto. }
  { eapply val_of_obj'_bytes. }
  { rewrite /check/ifThenElse.
    rewrite decide_True; auto.
    { repeat econstructor. }
  }
  { rewrite //= Heq. repeat econstructor. }
  { rewrite //=. do 2 f_equal.
    rewrite /jrnl_upd //=. rewrite /set. destruct s => //=.
    do 2 f_equal. rewrite /updateData. rewrite /= in Heq.
    subst => //=. repeat f_equal.
    rewrite -insert_union_l.
    rewrite map_subseteq_union //.
  }
Qed.

Lemma always_steps_OverWriteBitOp a b k σj:
  wf_jrnl σj →
  is_Some (jrnlData σj !! a)  →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (objSz (objBit b) = bufSz k ∧ k = KindBit) →
  always_steps (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                           OverWriteBitOp
                           (PairV (addr2val' a) (val_of_obj' (objBit b))))
               σj
               #()
               (updateData σj a (objBit b)).
Proof.
  intros Hwf (vs_old&Hlookup1) Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver.
    - rewrite //=. rewrite dom_insert_L.
      cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
      apply elem_of_dom. eauto.
    - eapply wf_jrnl_updateData; eauto. naive_solver.
  }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite H2 in Hlookup2.
    rewrite Hlookup2. econstructor; eauto. }
  {
    eapply val_of_obj'_bit. }
  { rewrite /check/ifThenElse.
    rewrite decide_True; auto.
    { repeat econstructor. }
  }
  { rewrite //= Heq. repeat econstructor. }
  { rewrite //=. do 2 f_equal.
    rewrite /jrnl_upd //=. rewrite /set. destruct s => //=.
    do 2 f_equal. rewrite /updateData. rewrite /= in Heq.
    subst => //=. repeat f_equal.
    rewrite -insert_union_l.
    rewrite map_subseteq_union //.
  }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ g (v : sval):
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ jrnl_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp v) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ g -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ??????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)) eqn:Heq; try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
  }
  { solve_ndisj. }
Qed.

Lemma jrnl_opened_open_false E j K {HCTX: LanguageCtx K} (v : sval):
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_open -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp v) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma jrnl_open_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'} (v: sval) :
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp v) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp v) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step_trans. simpl. econstructor.
      * eexists _ _; repeat econstructor.
        ** simpl. rewrite Heq. repeat econstructor.
      * repeat econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { simpl. congruence. }
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma ghost_step_jrnl_open E j K {HCTX: LanguageCtx K} (v: sval):
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_closed_frag -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp v)
  -∗ |NC={E}=> j ⤇ K #true%V ∗ jrnl_open.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_unify_closed with "[$] [$]") as %(σj&Heq).
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl. econstructor.
    * repeat econstructor => //=.
      rewrite Heq.
      repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (jrnl_closed_token_open with "[$] [$]") as "#Hopen".
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen". }
  iModIntro. iFrame "Hopen". iFrame.
Qed.

Lemma jrnl_ctx_sub_state_valid' σj s :
  (∀ sj, (s.(world) : @ffi_state jrnl_model) ≠ Closed sj) →
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ jrnl_sub_state σj s ⌝.
Proof.
  iIntros (?) "Hpts #Hkinds #Hallocs Hctx".
  rewrite /jrnl_sub_state.
  destruct (s.(world)) as [|sj] eqn:Heq_world; first by congruence.
  iExists _. iSplit; first eauto.
  iSplit; [| iSplit].
  - iIntros (a). destruct (jrnlData σj !! a) as [o|] eqn:Heq'.
    { rewrite /=. iDestruct (big_sepM_lookup with "Hpts") as "H"; eauto.
      rewrite /jrnl_ctx. rewrite /jrnl_state_ctx. iDestruct "Hctx" as "(_&_&Hctx1&Hctx2)".
      iDestruct "H" as "(?&?)".
      iDestruct (map_valid with "Hctx1 [$]") as %->; eauto.
    }
    { rewrite /=. destruct (jrnlData sj !! _); eauto. }
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom)".
    iDestruct (own_valid_2 with "Hkinds Hctx2") as %Hval.
    apply to_agree_op_valid in Hval. iPureIntro. set_solver.
  - iDestruct "Hctx" as "(_&Hctx)". iApply (jrnl_ctx_allocs_agree with "[$] [$]"); eauto.
Qed.

Lemma jrnl_ctx_dom_eq σj (s: sstate) :
  jrnl_dom (σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ dom (gset addr) (jrnlData (get_jrnl s.(world))) = σj ⌝.
Proof.
  iIntros "#Hdom Hctx".
  rewrite /jrnl_sub_state.
  rewrite /jrnl_ctx.
  destruct (s.(world)) as [sj|sj] eqn:Heq_world.
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom'&?)".
    iDestruct (jrnl_dom_agree with "[$] [$]") as %Heq; eauto.
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom'&?)".
    iDestruct (jrnl_dom_agree with "[$] [$]") as %Heq; eauto.
Qed.

Lemma jrnl_ctx_sub_state_valid σj s :
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_open -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ jrnl_sub_state σj s ⌝.
Proof.
  iIntros "Hpts #Hkinds #Hopen #Halloc Hctx".
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %[sj Heq].
  iApply (jrnl_ctx_sub_state_valid' with "[$] [$] [$] [$]").
  congruence.
Qed.

Lemma offsets_aligned_delete i σjd σjk σja :
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  offsets_aligned {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros Hoa k Hin. eapply Hoa.
  set_solver.
Qed.

Lemma sizes_correct_delete i σjd σjk σja :
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  sizes_correct {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros Hoa k Hin Hlookup. eapply Hoa.
  rewrite /=.
  eapply lookup_delete_Some; eauto.
Qed.

Lemma wf_jrnl_delete i σjd σjk σja :
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  wf_jrnl {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros (?&?).
  split; eauto using offsets_aligned_delete, sizes_correct_delete.
Qed.

Lemma offsets_aligned_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros Hsub Hoa i Hin. edestruct Hoa as (k&?&?); eauto.
  exists k; split_and!; eauto. rewrite /=.
  eapply lookup_weaken; eauto.
Qed.

Lemma sizes_correct_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros Hsub Hoa i ? Hin. edestruct Hoa as (k&?&?); eauto.
  exists k; split_and!; eauto. rewrite /=.
  eapply lookup_weaken; eauto.
Qed.

Lemma wf_jrnl_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros ? (?&?).
  split; eauto using offsets_aligned_mono_kinds, sizes_correct_mono_kinds.
Qed.

Lemma wf_jrnl_lookup_size_consistent_and_aligned σjd σjk σja i o :
  σjd !! i = Some o →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  size_consistent_and_aligned i o σjk.
Proof.
  intros Hlookup (Hoa&Hsizes).
  edestruct Hsizes as (k&?&?); eauto.
  exists k; split_and!; eauto.
  edestruct (Hoa i) as (k'&?&?).
  { apply elem_of_dom; eauto. }
  congruence.
Qed.

Lemma jrnl_ctx_upd σj σjd' σjk σja s :
  wf_jrnl {| jrnlData := σjd'; jrnlKinds := σjk; jrnlAllocs := σja |} →
  dom (gset _) (jrnlData σj) = dom (gset _) σjd' →
  jrnl_open -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds σjk -∗
  jrnl_alloc_map σja -∗
  jrnl_ctx s.(world) ==∗
  ([∗ map] a ↦ o ∈ (σjd'), jrnl_mapsto a 1 o) ∗
  jrnl_ctx (jrnl_upd {| jrnlData := σjd'; jrnlKinds := σjk; jrnlAllocs := σja |} s).(world).
Proof.
  iIntros (Hwf Hdom) "#Hopen Hpts #Hkinds #Hallocs Hctx".
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %[sj Heq].
  iDestruct (jrnl_ctx_sub_state_valid {| jrnlData := jrnlData σj; jrnlKinds := σjk; jrnlAllocs := σja |}
     with "Hpts Hkinds [$] [$] [$]") as %Hval.
  rewrite /jrnl_ctx. rewrite Heq.
  iDestruct "Hctx" as "(_&Hstate)".
  iDestruct "Hstate" as (Hwf0) "(Hctx&Hkinds'&Hdom'&Halloc_ctx)". simpl.
  assert (Hdom_sub: dom (gset _) (jrnlData σj) ⊆ dom (gset _) (jrnlData sj)).
  { rewrite /jrnl_sub_state/sworld in Hval.
    destruct Hval as (?&Heq'&?&?). rewrite /world in Heq. rewrite Heq in Heq'.
    inversion Heq'; subst.
    apply subseteq_dom. eauto. }
  clear Hval.
  rewrite /jrnl_state_ctx/=.
  iAssert (jrnl_dom (dom (gset addr) (σjd' ∪ jrnlData (get_jrnl s.(world))))) with "[Hdom']" as "$".
  { rewrite Heq /= dom_union_L.
    assert (dom (gset addr) σjd' ∪ dom (gset addr) (jrnlData sj) =
            dom (gset addr) (jrnlData sj)) as ->.
    { rewrite -Hdom. set_solver. }
    eauto. }
  clear Hdom_sub.
  iInduction (jrnlData σj) as [| i x m] "IH" using map_ind forall (σjd' Hwf Hdom).
  - rewrite dom_empty_L in Hdom.
    symmetry in Hdom. apply dom_empty_inv_L in Hdom.
    rewrite ?Hdom big_sepM_empty. iFrame.
    rewrite /=. rewrite left_id_L //=. rewrite Heq => //=. iFrame. eauto.
  - assert (Hin: i ∈ dom (gset _) σjd').
    { rewrite -Hdom. rewrite dom_insert_L. set_solver. }
    apply elem_of_dom in Hin.
    destruct Hin as (o&Hin).
    rewrite (big_sepM_delete _ σjd'); eauto.
    rewrite big_sepM_insert; eauto.
    iDestruct "Hpts" as "(Hmaps&Hpts)".
    iMod ("IH" with "[] [] Hpts [$] [$] [$]") as "($&Hctx)".
    { iPureIntro. apply wf_jrnl_delete; auto. }
    { iPureIntro. rewrite dom_insert_L in Hdom. rewrite dom_delete_L.
      apply not_elem_of_dom in H1. set_solver. }
    iDestruct "Hctx" as "($&Hstate)".
    iDestruct "Hstate" as (Hwf') "(Hctx&Hkinds'&Halloc_ctx)".
    iDestruct "Hmaps" as "(Hmaps&Hkind)".
    iDestruct "Hkind" as (? Hconsistent) "Hkind".
    iMod (map_update _ _ o with  "[$] [$]") as "(Hctx&?)".
    iDestruct (own_valid_2 with "Hkind Hkinds'") as %Hval.
    apply to_agree_op_valid, leibniz_equiv in Hval. rewrite /= in Hval.
    iDestruct (own_valid_2 with "Hkinds' Hkinds") as %Hval2.
    apply to_agree_op_valid, leibniz_equiv in Hval2. rewrite /= in Hval2.
    subst.
    iFrame. simpl.
    rewrite insert_union_l.
    rewrite insert_delete insert_id //.
    iFrame.
    assert (size_consistent_and_aligned i o (jrnlKinds (get_jrnl s.(world)))).
    {
      eapply wf_jrnl_lookup_size_consistent_and_aligned; eauto.
    }
    iModIntro; iSplit; auto.
    { iPureIntro. eapply wf_jrnl_extend in Hwf'; last eauto.
      rewrite /updateData//= in Hwf'.
      rewrite /= insert_union_l insert_delete insert_id in Hwf'; eauto.
    }
Qed.

Lemma ghost_step_jrnl_atomically_abort E j K {HCTX: LanguageCtx K} (l: sval) e :
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |NC={E}=>
  j ⤇ K NONEV.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopen Hj".
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iMod (ghost_step_stuck' with "[$] [$] [$]") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod (ghost_step_lifting _ _ _ _ _ _ [] _ _ _ [] with "[$] [$] [$]") as "($&Hstate'&_)".
  { apply head_prim_step. eapply head_step_atomically_fail.
    eapply atomically_not_stuck_body_safe; eauto. }
  { solve_ndisj. }
  iMod ("Hclo" with "[-]") as "_".
  { iNext. iExists _, _. iFrame. }
  iModIntro. eauto.
Qed.

Lemma ghost_step_jrnl_atomically E j K {HCTX: LanguageCtx K} (l: sval) e σj (v: sval) σj' :
  always_steps e σj (SOMEV v) σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |NC={E}=>
  j ⤇ K (SOMEV v) ∗ ([∗ map] a ↦ o ∈ (jrnlData σj'), jrnl_mapsto a 1 o).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_allocs Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iMod (ghost_step_stuck' with "[$] [$] [$]") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod (ghost_step_lifting _ _ _ (Atomically l e) s g [] (jrnl_upd σj' s) g (SOMEV v) []
          with "Hj Hctx H") as "(Hj&H&_)".
  { destruct g. apply head_prim_step.
    apply head_step_atomically; eauto.
    eapply atomically_not_stuck_body_safe; eauto.
  }
  { solve_ndisj. }
  iMod (jrnl_ctx_upd _ (jrnlData σj') _ (jrnlAllocs σj) with "[$] [$] [$] [$] [$]") as "(Hσj'_data&Hffi)".
  { destruct Hwf as (?&?&?&?&?). rewrite Heq_kinds; eauto. }
  { destruct Hwf as (?&?&?&?&?). eauto. }
  iMod ("Hclo" with "[Hσ Hrest H Hffi]") as "_".
  { iNext. iExists _, _. iFrame "H". iFrame. }
  iModIntro. iFrame.
Qed.

Lemma ghost_step_jrnl_atomically_crash E j K {HCTX: LanguageCtx K} (l: sval) e σj (v: sval) σj' :
  always_steps e σj (SOMEV v) σj' →
  nclose sN ⊆ E →
  spec_crash_ctx (jrnl_crash_ctx) -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  ([∗ map] a ↦ _ ∈ (jrnlData σj), jrnl_crash_tok a) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |C={E}_0=>
    ([∗ map] a ↦ o ∈ (jrnlData σj'), jrnl_mapsto a 1 o) ∗
    ([∗ map] a ↦ _ ∈ (jrnlData σj), jrnl_crash_tok a).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_crash_toks Hσj_kinds Hσj_allocs Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iMod (cfupd_weaken_all with "Hstate") as "#Hstate'"; eauto.
  { solve_ndisj. }
  iInv "Hstate'" as "[>Hbad|Hrest]" "Hclo".
  { iIntros "HC".
    destruct Hwf as (Hdom&?).
    iDestruct "Hbad" as (?) "(Htok&Hcrash_ctx&Hfull_tok)".
    induction (jrnlData σj) as [| x v' ? ? _] using map_ind.
    { rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_inv_L in Hdom. rewrite Hdom.
      rewrite ?big_sepM_empty. iMod ("Hclo" with "[-]").
      { iLeft. iNext; iExists _; eauto. iFrame. }
      eauto. }
    iEval (rewrite big_sepM_insert //) in "Hσj_crash_toks".
    iDestruct "Hσj_crash_toks" as "(Hcrash1&_)".
    iDestruct (map_valid with "Hcrash_ctx Hcrash1") as %Hlookup.
    apply lookup_fmap_Some in Hlookup as (?&_&Hlookup).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Htok") as "(H1&_)"; eauto.
    iDestruct (ptsto_conflict with "Hcrash1 H1") as %[].
  }
  iDestruct "Hrest" as (s g) "(>H&Hinterp)".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&?&?&?&?&>Hctok)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iIntros "#HC".
  iMod (ghost_step_crash_stuck' with "[] Hctx Hctok Hj [$] [$]") as (Hnstuck) "(Hj&H&Hctok)"; first by solve_ndisj.
  { iModIntro. iIntros "(h1&>h2)". iDestruct (pending_pending with "[$] [$]") as %[]. }
  iMod (ghost_step_crash_lifting _ _ _ _ _ (Atomically l e) s g [] (jrnl_upd σj' s) g (SOMEV v) []
          with "[] Hctok Hj Hctx H HC") as "(Hctok&Hj&H&_)".
  { apply head_prim_step.
    apply head_step_atomically; eauto.
    eapply atomically_not_stuck_body_safe; eauto.
  }
  { solve_ndisj. }
  { iModIntro. iIntros "(h1&>h2)". iDestruct (pending_pending with "[$] [$]") as %[]. }
  iMod (jrnl_ctx_upd _ (jrnlData σj') _ (jrnlAllocs σj) with "[$] [$] [$] [$] [$]") as "(Hσj'_data&Hffi)".
  { destruct Hwf as (?&?&?&?&?). rewrite Heq_kinds; eauto. }
  { destruct Hwf as (?&?&?&?&?). eauto. }
  iMod ("Hclo" with "[-Hσj_crash_toks Hσj'_data]") as "_".
  { iNext. iRight. iExists _, _. iFrame "H". iFrame. }
  iModIntro. iFrame.
Qed.

Lemma ghost_step_jrnl_atomically_ub' E j K {HCTX: LanguageCtx K} (l: sval) e1 σj e2 σj' σdom :
  always_steps e1 σj e2 σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_dom σdom -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e1)
  -∗ |NC={E}=>
   ⌜ (∃ s g, jrnl_sub_state σj' s ∧
        dom (gset _) (jrnlData (get_jrnl s.(world))) = σdom ∧
        ¬ stuck' e2 s g) ⌝ ∗
  j ⤇ K (Atomically l e1) ∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_allocs Hdom Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iDestruct (jrnl_ctx_dom_eq _ s with "[$] [$]") as %Hdom.
  iMod (ghost_step_stuck' with "Hj Hctx H") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod ("Hclo" with "[-Hj Hσj_data]").
  { iNext. iExists _, _. iFrame. }
  iModIntro. iFrame.  iPureIntro.
  exists (jrnl_upd σj' s), g.
  split_and!.
  - eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto.
  - rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
    destruct Hsub as (?&?&Hsub&_).
    eapply subseteq_dom in Hsub.
    rewrite /=.
    rewrite /addr in Hsub Hdom.  rewrite -Hdom.
    match goal with
    | [ H: sworld _ = _ |- _ ] => rewrite H
    end.
    set_solver.
  - intros Hnstuck'. apply Hnstuck.
  split; first done.
  apply prim_head_irreducible; last first.
  { intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    naive_solver.
  }
  rewrite /irreducible. intros ????? Hnostep.
  inversion Hnostep; subst.
  {
    inversion H2; eauto.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
  }
Qed.

Lemma ghost_step_jrnl_atomically_ub E j K {HCTX: LanguageCtx K} (l: sval) e1 σj e2 σj' σdom :
  (∀ s g, jrnl_sub_state σj' s →
        dom (gset _) (jrnlData (get_jrnl s.(world))) = σdom →
        stuck' e2 s g) →
  always_steps e1 σj e2 σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_dom σdom -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e1)
  -∗ |NC={E}=> False.
Proof.
  iIntros (Hub Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_alloc Hdom Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iDestruct (jrnl_ctx_dom_eq _ s with "[$] [$]") as %Hdom.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[]; last by solve_ndisj.
  rewrite /stuck.
  split; first done.
  apply prim_head_irreducible; last first.
  { intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    naive_solver.
  }
  rewrite /irreducible. intros ????? Hnostep.
  inversion Hnostep; subst.
  {
    inversion H2; eauto.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
    eapply Hub.
    { eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto. }
    { rewrite /jrnl_sub_dom in Hwf.
      rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
      destruct Hsub as (?&?&Hsub&_).
      eapply subseteq_dom in Hsub.
      match goal with
      | [ H: sworld _ = _ |- _ ] => rewrite H
      end.
      set_solver.
    }
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
    eapply Hub.
    { eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto. }
    { rewrite /jrnl_sub_dom in Hwf.
      rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
      destruct Hsub as (?&?&Hsub&_).
      eapply subseteq_dom in Hsub.
      match goal with
      | [ H: sworld _ = _ |- _ ] => rewrite H
      end.
      set_solver.
    }
  }
Qed.

Lemma objSize_non_bit_inv o b:
  objSz o = bufSz b ∧ b ≠ KindBit →
  ∃ vs, o = objBytes vs.
Proof.
  destruct o.
  - intros (Hsize&?). destruct b; try congruence; rewrite /objSz/bufSz in Hsize; lia.
  - eauto.
Qed.

Lemma objSize_bit_inv o b:
  objSz o = bufSz b ∧ b = KindBit →
  ∃ vs, o = objBit vs.
Proof.
  destruct o.
  - intros (Hsize&?). eauto.
  - intros (Hsize&?). subst. rewrite //= in Hsize. lia.
Qed.

Lemma not_stuck'_OverWriteBit_inv K `{!LanguageCtx' K} a (ov : sval) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                        OverWriteBitOp (addr2val' a, ov)%V)) s g →
  ∃ σj o, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some KindBit ∧
  val_of_obj' (objBit o) = ov.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (objSz o0 = bufSz b ∧ b = KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  edestruct (objSize_bit_inv) as (vs&Heq_vs); eauto.
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_OverWrite_inv K `{!LanguageCtx' K} a (ov : sval) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                        OverWriteOp (addr2val' a, ov)%V)) s g →
  ∃ σj k o, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some k ∧
  val_of_obj' (objBytes o) = ov ∧
  objSz (objBytes o) = bufSz k ∧ k ≠ KindBit.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (objSz o0 = bufSz b ∧ b ≠ KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  edestruct (objSize_non_bit_inv) as (vs&Heq_vs); eauto.
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_ReadBuf_inv K `{!LanguageCtx' K} a (sz : u64) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                        ReadBufOp (addr2val' a, #sz)%V)) s g →
  ∃ σj k, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some k ∧
  bufSz k = int.nat sz ∧ k ≠ KindBit.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (b ≠ KindBit ∧ bufSz b = int.nat sz)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_ReadBit_inv K `{!LanguageCtx' K} a s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                        ReadBitOp (addr2val' a)%V)) s g →
  ∃ σj, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some (KindBit).
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (b = KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

End spec.
