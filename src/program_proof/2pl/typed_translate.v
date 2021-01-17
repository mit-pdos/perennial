From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl.


Section translate.

  (* TODO: specialize to txn spec and disk ffi *)

  (* Records defining spec language extensions *)
  Context (spec_op: ext_op).
  Context (spec_ffi: ffi_model).
  Context (spec_semantics: ext_semantics spec_op spec_ffi).
  Context (spec_ty: ext_types spec_op).

  (* Records for the target language *)
  Context (impl_op: ext_op).
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

  Local Reserved Notation "Γ ⊢ e1 -- e2 : A" (at level 74, e1, e2, A at next level).
  Local Reserved Notation "Γ ⊢v v1 -- v2 : A" (at level 74, v1, v2, A at next level).

  (* TODO: (1) add a parameter for the binder for buftxn that we'll insert
           (2) add the ext ops for ReadBuf/Overwrite *)

  Inductive atomic_expr_transTy (Γ: SCtx) : sexpr -> iexpr -> sty -> Prop :=
  | var_transTy x t :
      Γ !! x = Some t ->
      Γ ⊢ Var x -- Var x : t
  | app_transTy f1 f2 x1 x2 t1 t2 :
      Γ ⊢ x1 -- x2 : t1 ->
      Γ ⊢ f1 -- f2 : arrowT t1 t2 ->
      Γ ⊢ App f1 x1 -- App f2 x2 : t2
  | val_expr_transTy v1 v2 t :
      atomic_val_transTy Γ v1 v2 t ->
      Γ ⊢ Val v1 -- Val v2 : t
  | rec_expr_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e -- e' : t2 ->
      Γ ⊢ Rec f x e -- Rec f x e' : arrowT t1 t2
  (** control flow *)
  | if_transTy cond cond' e1 e1' e2 e2' t :
      Γ ⊢ cond -- cond' : boolT ->
      Γ ⊢ e1 -- e1' : t ->
      Γ ⊢ e2 -- e2' : t ->
      Γ ⊢ If cond e1 e2 -- If cond' e1' e2' : t

  (** primitives operations *)
  | panic_expr_transTy msg t :
      Γ ⊢ Panic msg -- Panic msg : t
  | arbitrary_int_expr_transTy :
      Γ ⊢ ArbitraryInt -- ArbitraryInt : uint64T
  | cast_u64_op_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt64Op e1 -- UnOp ToUInt64Op e2 : uint64T
  | cast_u32_op_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt32Op e1 -- UnOp ToUInt32Op e2 : uint32T
  | cast_u8_op_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt8Op e1 -- UnOp ToUInt8Op e2 : byteT
  | cast_string_op_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      is_byteTy t = true ->
      Γ ⊢ UnOp ToStringOp e1 -- UnOp ToStringOp e2 : stringT
  | un_op_transTy op e1 e2 t1 t :
      un_op_ty op = Some (t1, t) ->
      Γ ⊢ e1 -- e2 : t1 ->
      Γ ⊢ UnOp op e1 -- UnOp op e2 : t
  | eq_op_transTy e1 e1' e2 e2' t :
      Γ ⊢ e1 -- e1' : t ->
      Γ ⊢ e2 -- e2' : t ->
      is_comparableTy t = true ->
      Γ ⊢ BinOp EqOp e1 e2 -- BinOp EqOp e1' e2' : boolT
  | bin_op_64_transTy op e1 e1' e2 e2' t1 t2 t :
      bin_op_ty op uint64T = Some (t1, t2, t) ->
      Γ ⊢ e1 -- e1' : t1 ->
      Γ ⊢ e2 -- e2' : t2 ->
      Γ ⊢ BinOp op e1 e2 -- BinOp op e1' e2' : t
  | bin_op_32_transTy op e1 e1' e2 e2' t1 t2 t :
      bin_op_ty op uint32T = Some (t1, t2, t) ->
      Γ ⊢ e1 -- e1' : t1 ->
      Γ ⊢ e2 -- e2' : t2 ->
      Γ ⊢ BinOp op e1 e2 -- BinOp op e1' e2' : t
  | str_plus_transTy e1 e1' e2 e2' :
      Γ ⊢ e1 -- e1' : stringT ->
      Γ ⊢ e2 -- e2' : stringT ->
      Γ ⊢ BinOp PlusOp e1 e2 -- BinOp PlusOp e1' e2' : stringT

  (** data *)
  | pair_transTy e1 e1' e2 e2' t1 t2 :
      Γ ⊢ e1 -- e1' : t1 ->
      Γ ⊢ e2 -- e2' : t2 ->
      Γ ⊢ Pair e1 e2 -- Pair e1' e2' : prodT t1 t2
  | fst_transTy e e' t1 t2 :
      Γ ⊢ e -- e' : prodT t1 t2 ->
      Γ ⊢ Fst e -- Fst e' : t1
  | snd_transTy e e' t1 t2 :
      Γ ⊢ e -- e' : prodT t1 t2 ->
      Γ ⊢ Snd e -- Snd e' : t2
  | cons_transTy ehd ehd' etl etl' t :
      Γ ⊢  ehd -- ehd' : t ->
      Γ ⊢  etl -- etl' : listT t ->
      Γ ⊢  ListCons ehd etl -- ListCons ehd' etl' : listT t
  | listmatch_hasTy el el' nilfun nilfun' consfun consfun' tl tret :
      Γ ⊢ el -- el' : listT tl ->
      Γ ⊢ nilfun -- nilfun' : arrowT unitT tret ->
      Γ ⊢ consfun -- consfun' : arrowT (prodT tl (listT tl)) tret ->
      Γ ⊢ ListMatch el nilfun consfun -- ListMatch el' nilfun' consfun' : tret
  | inl_transTy e e' t1 t2 :
      Γ ⊢ e -- e' : t1 ->
      Γ ⊢ InjL e -- InjL e' : sumT t1 t2
  | inr_transTy e e' t1 t2 :
      Γ ⊢ e -- e' : t2 ->
      Γ ⊢ InjR e -- InjR e' : sumT t1 t2
  | case_transTy cond cond' e1 e1' e2 e2' t1 t2 t :
      Γ ⊢ cond -- cond' : sumT t1 t2 ->
      Γ ⊢ e1 -- e1' : arrowT t1 t ->
      Γ ⊢ e2 -- e2' : arrowT t2 t ->
      Γ ⊢ Case cond e1 e2 -- Case cond' e1' e2' : t

  where "Γ ⊢ e1 -- e2 : A" := (atomic_expr_transTy Γ e1 e2 A)

  with atomic_val_transTy (Γ: SCtx) : sval -> ival -> sty -> Prop :=
  | val_base_lit_transTy v t :
      base_lit_hasTy v t ->
      Γ ⊢v (LitV v) -- (LitV v) : t
  | val_pair_transTy v1 v1' v2 v2' t1 t2 :
      Γ ⊢v v1 -- v1' : t1 ->
      Γ ⊢v v2 -- v2' : t2 ->
      Γ ⊢v PairV v1 v2 -- PairV v1' v2' : prodT t1 t2
  | val_nil_transTy t :
      Γ ⊢v ListNilV -- ListNilV : listT t
  | val_cons_hasTy vhd vhd' vtl vtl' t :
      Γ ⊢v vhd -- vhd' : t ->
      Γ ⊢v vtl -- vtl' : listT t ->
      Γ ⊢v ListConsV vhd vtl -- ListConsV vhd' vtl' : listT t
  | val_injL_transTy v1 v1' t1 t2 :
      Γ ⊢v v1 -- v1' : t1 ->
      Γ ⊢v InjLV v1 -- InjLV v1' : sumT t1 t2
  | val_injR_transTy v2 v2' t1 t2 :
      Γ ⊢v v2 -- v2' : t2 ->
      Γ ⊢v InjRV v2 -- InjRV v2' : sumT t1 t2
  | rec_val_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ ∅) ⊢ e -- e' : t2 ->
      Γ ⊢v RecV f x e -- RecV f x e' : arrowT t1 t2
  where "Γ ⊢v v1 -- v2 : A" := (atomic_val_transTy Γ v1 v2 A).

End translate.
