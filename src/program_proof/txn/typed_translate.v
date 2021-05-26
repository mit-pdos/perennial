From Perennial.goose_lang Require Import lang notation typing metatheory.
From Perennial.goose_lang.lib Require Import map.impl list.impl.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.go_journal Require Import obj txn alloc.
From Perennial.program_proof Require Import txn.op_wrappers.
From Perennial.program_proof Require jrnl.sep_jrnl_proof buf.defs.

Section translate.

  (* Records defining spec language extensions *)
  Notation spec_op := jrnl_op.
  Notation spec_ffi := jrnl_model.
  Notation spec_semantics := jrnl_semantics.
  Notation spec_ty := jrnl_ty.
  Existing Instances jrnl_op jrnl_model jrnl_semantics jrnl_ty.

  (* Records for the target language *)
  Notation impl_op := disk_op.
  Context (impl_ffi: ffi_model).
  Context (impl_semantics: ffi_semantics impl_op impl_ffi).
  Context (impl_ty: ext_types impl_op).

  Notation sexpr := (@expr spec_op).
  Notation sval := (@val spec_op).
  Notation iexpr := (@expr impl_op).
  Notation ival := (@val impl_op).
  Notation sty := (@ty (@val_tys _ spec_ty)).
  Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

  Fixpoint atomic_convertible (s: sty) : Prop :=
    match s with
    | baseT _ => True
    | prodT t1 t2 => atomic_convertible t1 ∧ atomic_convertible t2
    | sumT t1 t2 => atomic_convertible t1 ∧ atomic_convertible t2
    | listT t => atomic_convertible t
    | extT AllocT => True
    | _ => False
    end.

  Fixpoint atomic_deconvertible (s: sty) : Prop :=
    match s with
    | baseT _ => True
    | prodT t1 t2 => atomic_deconvertible t1 ∧ atomic_deconvertible t2
    | sumT t1 t2 => atomic_deconvertible t1 ∧ atomic_deconvertible t2
    | listT t => atomic_deconvertible t
    | extT AllocT => True
    | _ => False
    end.

  Local Reserved Notation "Γ @ t ⊢ e1 -- e2 : A" (at level 74, t, e1, e2, A at next level).
  Local Reserved Notation "Γ @ t ⊢v v1 -- v2 : A" (at level 74, t, v1, v2, A at next level).

  Inductive atomically_base_lit_hasTy : base_lit -> ty -> Prop :=
  | uint64_hasTy x : atomically_base_lit_hasTy (LitInt x) uint64T
  | uint32_hasTy x : atomically_base_lit_hasTy (LitInt32 x) uint32T
  | byte_hasTy x : atomically_base_lit_hasTy (LitByte x) byteT
  | bool_hasTy x : atomically_base_lit_hasTy (LitBool x) boolT
  | unit_hasTy : atomically_base_lit_hasTy (LitUnit) unitT
  | string_hasTy s : atomically_base_lit_hasTy (LitString s) stringT.

  Local Existing Instance disk_ty.

  Inductive atomic_body_expr_transTy (Γ: SCtx) (tph : iexpr) : sexpr -> iexpr -> sty -> Prop :=
  | var_transTy x t :
      Γ !! x = Some t ->
      Γ @ tph ⊢ Var x -- Var x : t
  | app_transTy f1 f2 x1 x2 t1 t2 :
      Γ @ tph ⊢ x1 -- x2 : t1 ->
      Γ @ tph ⊢ f1 -- f2 : arrowT t1 t2 ->
      Γ @ tph ⊢ App f1 x1 -- App f2 x2 : t2
  | val_expr_transTy v1 v2 t :
      atomic_body_val_transTy Γ tph v1 v2 t ->
      Γ @ tph ⊢ Val v1 -- Val v2 : t
  | rec_expr_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) @ tph ⊢ e -- e' : t2 ->
      Γ @ tph ⊢ Rec f x e -- Rec f x e' : arrowT t1 t2
  (** control flow *)
  | if_transTy cond cond' e1 e1' e2 e2' t :
      Γ @ tph ⊢ cond -- cond' : boolT ->
      Γ @ tph ⊢ e1 -- e1' : t ->
      Γ @ tph ⊢ e2 -- e2' : t ->
      Γ @ tph ⊢ If cond e1 e2 -- If cond' e1' e2' : t

  (** primitives operations *)
  | panic_expr_transTy msg t :
      Γ @ tph ⊢ Panic msg -- (Skip ;; Panic msg) : t
  | arbitrary_int_expr_transTy :
      Γ @ tph ⊢ ArbitraryInt -- ArbitraryInt : uint64T
  | cast_u64_op_transTy e1 e2 t :
      Γ @ tph ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ @ tph ⊢ UnOp ToUInt64Op e1 -- UnOp ToUInt64Op e2 : uint64T
  | cast_u32_op_transTy e1 e2 t :
      Γ @ tph ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ @ tph ⊢ UnOp ToUInt32Op e1 -- UnOp ToUInt32Op e2 : uint32T
  | cast_u8_op_transTy e1 e2 t :
      Γ @ tph ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ @ tph ⊢ UnOp ToUInt8Op e1 -- UnOp ToUInt8Op e2 : byteT
  | cast_string_op_transTy e1 e2 t :
      Γ @ tph ⊢ e1 -- e2 : t ->
      is_byteTy t = true ->
      Γ @ tph ⊢ UnOp ToStringOp e1 -- UnOp ToStringOp e2 : stringT
  | un_op_transTy op e1 e2 t1 t :
      un_op_ty op = Some (t1, t) ->
      Γ @ tph ⊢ e1 -- e2 : t1 ->
      Γ @ tph ⊢ UnOp op e1 -- UnOp op e2 : t
  | eq_op_transTy e1 e1' e2 e2' t :
      Γ @ tph ⊢ e1 -- e1' : t ->
      Γ @ tph ⊢ e2 -- e2' : t ->
      is_comparableTy t = true ->
      Γ @ tph ⊢ BinOp EqOp e1 e2 -- BinOp EqOp e1' e2' : boolT
  | bin_op_64_transTy op e1 e1' e2 e2' t1 t2 t :
      bin_op_ty op uint64T = Some (t1, t2, t) ->
      Γ @ tph ⊢ e1 -- e1' : t1 ->
      Γ @ tph ⊢ e2 -- e2' : t2 ->
      Γ @ tph ⊢ BinOp op e1 e2 -- BinOp op e1' e2' : t
  | bin_op_32_transTy op e1 e1' e2 e2' t1 t2 t :
      bin_op_ty op uint32T = Some (t1, t2, t) ->
      Γ @ tph ⊢ e1 -- e1' : t1 ->
      Γ @ tph ⊢ e2 -- e2' : t2 ->
      Γ @ tph ⊢ BinOp op e1 e2 -- BinOp op e1' e2' : t
  | str_plus_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : stringT ->
      Γ @ tph ⊢ e2 -- e2' : stringT ->
      Γ @ tph ⊢ BinOp PlusOp e1 e2 -- BinOp PlusOp e1' e2' : stringT

  (** data *)
  | pair_transTy e1 e1' e2 e2' t1 t2 :
      Γ @ tph ⊢ e1 -- e1' : t1 ->
      Γ @ tph ⊢ e2 -- e2' : t2 ->
      Γ @ tph ⊢ Pair e1 e2 -- Pair e1' e2' : prodT t1 t2
  | fst_transTy e e' t1 t2 :
      Γ @ tph ⊢ e -- e' : prodT t1 t2 ->
      Γ @ tph ⊢ Fst e -- Fst e' : t1
  | snd_transTy e e' t1 t2 :
      Γ @ tph ⊢ e -- e' : prodT t1 t2 ->
      Γ @ tph ⊢ Snd e -- Snd e' : t2
  | cons_transTy ehd ehd' etl etl' t :
      Γ @ tph ⊢  ehd -- ehd' : t ->
      Γ @ tph ⊢  etl -- etl' : listT t ->
      Γ @ tph ⊢  ListCons ehd etl -- ListCons ehd' etl' : listT t
  | listmatch_hasTy el el' nilfun nilfun' consfun consfun' tl tret :
      Γ @ tph ⊢ el -- el' : listT tl ->
      Γ @ tph ⊢ nilfun -- nilfun' : arrowT unitT tret ->
      Γ @ tph ⊢ consfun -- consfun' : arrowT (prodT tl (listT tl)) tret ->
      Γ @ tph ⊢ ListMatch el nilfun consfun -- ListMatch el' nilfun' consfun' : tret
  | inl_transTy e e' t1 t2 :
      Γ @ tph ⊢ e -- e' : t1 ->
      Γ @ tph ⊢ InjL e -- InjL e' : sumT t1 t2
  | inr_transTy e e' t1 t2 :
      Γ @ tph ⊢ e -- e' : t2 ->
      Γ @ tph ⊢ InjR e -- InjR e' : sumT t1 t2
  | case_transTy cond cond' e1 e1' e2 e2' t1 t2 t :
      Γ @ tph ⊢ cond -- cond' : sumT t1 t2 ->
      Γ @ tph ⊢ e1 -- e1' : arrowT t1 t ->
      Γ @ tph ⊢ e2 -- e2' : arrowT t2 t ->
      Γ @ tph ⊢ Case cond e1 e2 -- Case cond' e1' e2' : t

  (* Journal operations *)
  | readbuf_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : addrT ->
      Γ @ tph ⊢ e2-- e2' : uint64T ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) ReadBufOp (e1, e2) -- (Txn__ReadBuf' tph (e1', e2')%E) : listT byteT
  | readbit_transTy e1 e1' :
      Γ @ tph ⊢ e1 -- e1' : addrT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) ReadBitOp e1 -- (Txn__ReadBufBit' tph e1') : boolT
  | overwrite_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : addrT ->
      Γ @ tph ⊢ e2 -- e2' : listT byteT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) OverWriteOp (e1, e2) -- (Txn__OverWrite' tph (e1', e2')%E) : unitT
  | overwritebit_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : addrT ->
      Γ @ tph ⊢ e2 -- e2' : boolT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) OverWriteBitOp (e1, e2) -- (Txn__OverWriteBit' tph (e1', e2')%E) : unitT
 (* Alloc operations *)
  | markused_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : extT AllocT ->
      Γ @ tph ⊢ e2 -- e2' : baseT uint64BT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) MarkUsedOp (e1, e2) --
               (Alloc__MarkUsed' (e1', e2')%E) : unitT
  | freenum_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : extT AllocT ->
      Γ @ tph ⊢ e2 -- e2' : baseT uint64BT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) FreeNumOp (e1, e2) --
               (Alloc__FreeNum' (e1', e2')%E) : unitT
  | alloc_transTy e1 e1' :
      Γ @ tph ⊢ e1 -- e1' : extT AllocT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) AllocOp e1 --
               ((λ: "x", Skip;; Alloc__AllocNum (Var "x"))%V e1') : baseT uint64BT
  | num_free_transTy e1 e1' :
      Γ @ tph ⊢ e1 -- e1' : extT AllocT ->
      Γ @ tph ⊢ ExternalOp (ext := spec_op) NumFreeOp e1 --
               ((λ: "x", Skip;; Alloc__NumFree (Var "x"))%V e1') : baseT uint64BT

  where "Γ @ tph ⊢ e1 -- e2 : A" := (atomic_body_expr_transTy Γ tph e1 e2 A)

  with atomic_body_val_transTy (Γ: SCtx) (tph : iexpr) : sval -> ival -> sty -> Prop :=
  | val_base_lit_transTy v t :
      atomically_base_lit_hasTy v t ->
      Γ @ tph ⊢v (LitV v) -- (LitV v) : t
  | val_pair_transTy v1 v1' v2 v2' t1 t2 :
      Γ @ tph ⊢v v1 -- v1' : t1 ->
      Γ @ tph ⊢v v2 -- v2' : t2 ->
      Γ @ tph ⊢v PairV v1 v2 -- PairV v1' v2' : prodT t1 t2
  | val_nil_transTy t :
      Γ @ tph ⊢v ListNilV -- ListNilV : listT t
  | val_cons_hasTy vhd vhd' vtl vtl' t :
      Γ @ tph ⊢v vhd -- vhd' : t ->
      Γ @ tph ⊢v vtl -- vtl' : listT t ->
      Γ @ tph ⊢v ListConsV vhd vtl -- ListConsV vhd' vtl' : listT t
  | val_injL_transTy v1 v1' t1 t2 :
      Γ @ tph ⊢v v1 -- v1' : t1 ->
      Γ @ tph ⊢v InjLV v1 -- InjLV v1' : sumT t1 t2
  | val_injR_transTy v2 v2' t1 t2 :
      Γ @ tph ⊢v v2 -- v2' : t2 ->
      Γ @ tph ⊢v InjRV v2 -- InjRV v2' : sumT t1 t2
  (* We can't allow RecV's we can't properly substitute the tph in later on *)
  (*
  | rec_val_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ ∅) @ tph ⊢ e -- e' : t2 ->
      Γ @ tph ⊢v RecV f x e -- RecV f x e' : arrowT t1 t2 *)
  where "Γ @ tph ⊢v v1 -- v2 : A" := (atomic_body_val_transTy Γ tph v1 v2 A).

  Inductive jrnl_trans : sval → ival → Prop :=
  | jrnl_open_trans (x: string) :
      jrnl_trans (λ: x, ExternalOp OpenOp (Var x)) (λ: x, Init (disk_val ()))
  | jrnl_mkalloc_trans (x: string) :
      jrnl_trans (λ: x, ExternalOp MkAllocOp (Var x)) MkMaxAlloc.

  Inductive jrnl_atomic_transTy : SCtx → sexpr → iexpr → sty → sexpr → iexpr → sty → Prop :=
  | jrnl_atomic_transTy_core Γ Γ' etxn etxn' ebdy ebdy' t (tph: string) :
      (∀ x ty, Γ' !! x = Some ty → Γ !! x = Some ty ∧ atomic_convertible ty) →
      tph ∉ dom (gset _) Γ →
      tph ∉ expr_vars ebdy →
      Γ' @ (Var tph) ⊢ ebdy -- ebdy' : t →
      atomic_deconvertible t →
      jrnl_atomic_transTy Γ etxn etxn' (extT JrnlT)
                            ebdy
                            (* This final argument is what Atomically etxn ebdy will get translated to *)
                            (let: tph := Begin etxn' in
                             Txn__ConditionalCommit' (Var tph) ebdy') t.

End translate.


Section initP.

Definition kinds_mapsto_valid (kinds : gmap u64 defs.bufDataKind)
           (a : addr_proof.addr) (obj : {K : defs.bufDataKind & defs.bufDataT K}) :=
  addr_proof.valid_addr a
  ∧ defs.valid_off (buf_proof.objKind obj) (addr_proof.addrOff a)
    ∧ kinds !! addr_proof.addrBlock a = Some (buf_proof.objKind obj).

Definition bufObj_to_obj bufObj : obj :=
  match sep_jrnl_invariant.objData bufObj with
  | buf.defs.bufBit b => objBit b
  | buf.defs.bufInode data | buf.defs.bufBlock data => objBytes data
  end.

Definition twophase_initP kind_sz (σimpl: @goose_lang.state disk_op disk_model) (σspec : @goose_lang.state jrnl_op jrnl_model) : Prop :=
  ∃ sz kinds,
    let σj := {| jrnlData := (bufObj_to_obj <$> recovery_proof.kind_heap0 kinds);
                 jrnlKinds := kinds;
                 jrnlAllocs := ∅
              |} in
  ((513 + Z.of_nat sz) * block_bytes * 8 < 2^64)%Z ∧
  (null_non_alloc σspec.(heap)) ∧
  (σimpl.(world) = init_disk ∅ (513 + sz)) ∧
  (σspec.(world) = Closed σj) ∧
  dom (gset _) kinds = list_to_set (U64 <$> (seqZ 513 sz)) ∧
  size (recovery_proof.kind_heap0 kinds) = kind_sz.

End initP.
