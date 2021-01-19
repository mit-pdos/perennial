From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl.


(* Defines typed translation between two Goose lang extensions *)


Section translate.

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

  (* The translation is not necessarily assumed to be a function, so in principle
     there could be many translations of a particular piece of code. In reality,
     you would want to prove that all well-typed programs have a valid translation *)
  Context (spec_trans : sval -> ival -> Prop).

  (* This is a typed relation for translating code expressions in atomic blocks *)
  (* Not all variables in a context can be used in the body of an Atomically e expression.
     For example, consider let x := (λ _, impure_code) in Atomically x. So this relation
     should filter out elements of SCtx that do not have appropriate types before
     trying to type the body of the expression *)
  Context (spec_atomic_transTy : SCtx -> sexpr -> iexpr -> sty -> sexpr -> iexpr -> sty -> Prop).


  Reserved Notation "Γ ⊢ e1 -- e2 : A" (at level 74, e1, e2, A at next level).
  Reserved Notation "Γ ⊢v v1 -- v2 : A" (at level 74, v1, v2, A at next level).

  (* I require variable bindings to be the same between translations. I think this is
     OK, and it simplifies the definition of ctxs that has to be used *)
  Inductive expr_transTy (Γ: SCtx) : sexpr -> iexpr -> sty -> Prop :=
  | var_transTy x t :
      Γ !! x = Some t ->
      Γ ⊢ Var x -- Var x : t
  | app_transTy f1 f2 x1 x2 t1 t2 :
      Γ ⊢ x1 -- x2 : t1 ->
      Γ ⊢ f1 -- f2 : arrowT t1 t2 ->
      Γ ⊢ App f1 x1 -- App f2 x2 : t2
  | val_expr_transTy v1 v2 t :
      val_transTy Γ v1 v2 t ->
      Γ ⊢ Val v1 -- Val v2 : t
  | rec_expr_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e -- e' : t2 ->
      Γ ⊢ Rec f x e -- Rec f x e' : arrowT t1 t2
  | fork_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      Γ ⊢ Fork e1 -- Fork e2 : unitT
  | atomically_transTy el1 el2 tl e1 e2 t :
      Γ ⊢ el1 -- el2 : tl ->
      spec_atomic_transTy Γ el1 el2 tl e1 e2 t ->
      Γ ⊢ Atomically el1 e1 -- e2 : t
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
  (*
  | mapNil_transTy def def' vt :
      Γ ⊢ def -- def' : vt ->
      Γ ⊢ InjL def -- InjL def' : mapValT vt
  | mapCons_transTy k k' v v' vt m m':
      Γ ⊢ k -- k' : uint64T ->
      Γ ⊢ v -- v' : vt ->
      Γ ⊢ m -- m' : mapValT vt ->
      Γ ⊢ InjR (Pair (Pair k v) m) -- InjR (Pair (Pair k' v') m') : mapValT vt
  | case_map_transTy cond cond' e1 e1' e2 e2' vt t :
      Γ ⊢ cond -- cond' : mapValT vt ->
      Γ ⊢ e1 -- e1' : arrowT vt t ->
      Γ ⊢ e2 -- e2' : arrowT (prodT (prodT uint64T vt ) (mapValT vt)) t ->
      Γ ⊢ Case cond e1 e2 -- Case cond' e1' e2' : t
  *)
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

  (** pointers *)
  | alloc_transTy n n' v v' t :
      storable t →
      flatten_ty t ≠ [] →
      Γ ⊢ n -- n' : uint64T ->
      Γ ⊢ v -- v' : t ->
      Γ ⊢ AllocN n v -- AllocN n' v': arrayT t
  (* This rule means we require all external types to have the same size at the
     spec level as in their implementation.  *)
  | offset_op_transTy e1 e1' e2 e2' t :
      Γ ⊢ e1 -- e1' : arrayT t ->
      Γ ⊢ e2 -- e2' : uint64T ->
      Γ ⊢ BinOp (OffsetOp (ty_size t)) e1 e2 -- BinOp (OffsetOp (ty_size t)) e1' e2' : arrayT t
  | array_struct_transTy e e' t :
      Γ ⊢ e -- e' : arrayT t ->
      Γ ⊢ e -- e' : structRefT (flatten_ty t)
  | struct_offset_op_transTy e1 e1' (k: Z) ts :
      0 ≤ k →
      Z.to_nat k < length ts →
      Γ ⊢ e1 -- e1' : structRefT ts ->
      Γ ⊢ BinOp (OffsetOp k) e1 #1 -- BinOp (OffsetOp k) e1' #1 : structRefT (drop (Z.to_nat k) ts)
  | load_transTy l l' t ts :
      Γ ⊢ l -- l' : structRefT (t::ts) ->
      Γ ⊢ Load l -- Load l' : t
  | store_transTy l l' v v' t ts :
      Γ ⊢ l -- l' : structRefT (t::ts) ->
      Γ ⊢ v -- v' : t ->
      Γ ⊢ Store l v -- Store l' v' : unitT
  | read_transTy l l' t ts :
      Γ ⊢ l -- l' : structRefT (t::ts) ->
      Γ ⊢ Read l -- Read l' : t
  | cmpxchg_transTy l l' v1 v1' v2 v2' t ts :
      is_unboxedTy t = true ->
      Γ ⊢ l -- l' : structRefT (t::ts) ->
      Γ ⊢ v1 -- v1' : t ->
      Γ ⊢ v2 -- v2' : t ->
      Γ ⊢ CmpXchg l v1 v2 -- CmpXchg l' v1' v2' : prodT t boolT

  (** I/O *)
  | input_hasTy sel sel' :
      Γ ⊢ sel -- sel' : uint64T ->
      Γ ⊢ Input sel -- Input sel' : uint64T
  | output_hasTy v v' :
      Γ ⊢ v -- v' : uint64T ->
      Γ ⊢ Output v -- Output v' : unitT


  | external_transTy (v: sval) v' (earg: sexpr) earg' t1 t2 :
      get_ext_tys v (t1, t2) ->
      spec_trans v v' ->
      Γ ⊢ earg -- earg' : t1 ->
      Γ ⊢ v earg -- v' earg' : t2

  where "Γ ⊢ e1 -- e2 : A" := (expr_transTy Γ e1 e2 A)

  with val_transTy (Γ: SCtx) : sval -> ival -> sty -> Prop :=
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
  (*
  | mapNilV_transTy v v' t :
      Γ ⊢v v -- v' : t ->
      Γ ⊢v MapNilV v  -- MapNilV v': mapValT t
  *)
  where "Γ ⊢v v1 -- v2 : A" := (val_transTy Γ v1 v2 A).

End translate.
