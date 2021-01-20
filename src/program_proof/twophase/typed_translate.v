From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.


Section translate.

  (* TODO: specialize to txn spec and disk ffi *)

  (* Records defining spec language extensions *)
  Notation spec_op := jrnl_op.
  Notation spec_ffi := jrnl_model.
  Notation spec_semantics := jrnl_semantics.
  Notation spec_ty := jrnl_ty.
  Existing Instances jrnl_op jrnl_model jrnl_semantics jrnl_ty.

  (* Records for the target language *)
  Notation impl_op := disk_op.
  Context (impl_ffi: ffi_model).
  Context (impl_semantics: ext_semantics impl_op impl_ffi).
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
    (* TODO: fix this once the ext types are defined *)
    | extT x => False
    | _ => False
    end.

  Local Reserved Notation "Γ @ t ⊢ e1 -- e2 : A" (at level 74, t, e1, e2, A at next level).
  Local Reserved Notation "Γ @ t ⊢v v1 -- v2 : A" (at level 74, t, v1, v2, A at next level).

  (* TODO: (1) add a parameter for the binder for buftxn that we'll insert
           (2) add the ext ops for ReadBuf/Overwrite *)

  Inductive atomic_expr_transTy (Γ: SCtx) (tph : iexpr) : sexpr -> iexpr -> sty -> Prop :=
  | var_transTy x t :
      Γ !! x = Some t ->
      Γ @ tph ⊢ Var x -- Var x : t
  | app_transTy f1 f2 x1 x2 t1 t2 :
      Γ @ tph ⊢ x1 -- x2 : t1 ->
      Γ @ tph ⊢ f1 -- f2 : arrowT t1 t2 ->
      Γ @ tph ⊢ App f1 x1 -- App f2 x2 : t2
  | val_expr_transTy v1 v2 t :
      atomic_val_transTy Γ tph v1 v2 t ->
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
      Γ @ tph ⊢ Panic msg -- Panic msg : t
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
  | readbuf_transTy e e' :
      Γ @ tph ⊢ e -- e' : addrT ->
     (* XXX: we want to call a wrapper around TwoPhase__ReadBuf that converts to a pure list *)
      Γ @ tph ⊢ ExternalOp (ext := spec_op) ReadBufOp e -- (TwoPhase__ReadBuf tph e') : listT byteT
  | overwrite_transTy e1 e1' e2 e2' :
      Γ @ tph ⊢ e1 -- e1' : addrT ->
      Γ @ tph ⊢ e2 -- e2' : listT byteT ->
     (* XXX: we want to call a wrapper around TwoPhase__OverWrite that converts to a pure list *)
      Γ @ tph ⊢ ExternalOp (ext := spec_op) OverWriteOp e1 e2 -- (TwoPhase__OverWrite tph e1' e2') : unitT

  where "Γ @ tph ⊢ e1 -- e2 : A" := (atomic_expr_transTy Γ tph e1 e2 A)

  with atomic_val_transTy (Γ: SCtx) (tph : iexpr) : sval -> ival -> sty -> Prop :=
  | val_base_lit_transTy v t :
      base_lit_hasTy v t ->
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
  | rec_val_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ ∅) @ tph ⊢ e -- e' : t2 ->
      Γ @ tph ⊢v RecV f x e -- RecV f x e' : arrowT t1 t2
  where "Γ @ tph ⊢v v1 -- v2 : A" := (atomic_val_transTy Γ tph v1 v2 A).

End translate.
