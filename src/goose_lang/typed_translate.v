From Perennial.goose_lang Require Import lang notation map typing.


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

  Context (spec_val_trans : sval -> ival).
  Context (spec_op_trans : @external spec_op -> iexpr).
  (* XXX: need some assumptions that the previous two arguments make sense
     in particular, should be total in the sense that all well typed extension rules
     should have a translation rule *)

  Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

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
  | panic_expr_transTy msg t :
      Γ ⊢ Panic msg -- Panic msg : t
  | fork_transTy e1 e2 t :
      Γ ⊢ e1 -- e2 : t ->
      Γ ⊢ Fork e1 -- Fork e2 : unitT
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
  | offset_op_transTy e1 e1' e2 e2' t :
      Γ ⊢ e1 -- e1' : arrayT t ->
      Γ ⊢ e2 -- e2' : uint64T ->
      Γ ⊢ BinOp OffsetOp e1 e2 -- BinOp OffsetOp e1' e2' : arrayT t
  (* JDT: Worried about compilation of abstract types in structs. Might there be an issue
          with the way flattening is done, if, say, the implementation of an abstract type is
          as a struct? But perhaps not, as Tej pointed out abstract type has to be wrapped by a pointer
          to enforce abstraction anyway *)
  | struct_offset_op_transTy e1 e1' (v: Z) ts :
      Γ ⊢ e1 -- e1' : structRefT ts ->
      Γ ⊢ BinOp OffsetOp e1 #v -- BinOp OffsetOp e1' #v : structRefT (skipn (Z.to_nat v) ts)
  | struct_offset_op_collapse_transTy e1 e1' (v1 v2: Z) ts :
      Γ ⊢ BinOp OffsetOp (BinOp OffsetOp e1 #v1) #v2 --
          BinOp OffsetOp (BinOp OffsetOp e1' #v1) #v2 : structRefT ts ->
      Γ ⊢ BinOp OffsetOp e1 #(v1 + v2) -- BinOp OffsetOp e1' #(v1 + v2): structRefT ts
  | eq_op_transTy e1 e1' e2 e2' t :
      Γ ⊢ e1 -- e1' : t ->
      Γ ⊢ e2 -- e2' : t ->
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
  | if_transTy cond cond' e1 e1' e2 e2' t :
      Γ ⊢ cond -- cond' : boolT ->
      Γ ⊢ e1 -- e1' : t ->
      Γ ⊢ e2 -- e2' : t ->
      Γ ⊢ If cond e1 e2 -- If cond' e1' e2' : t
  | alloc_transTy n n' v v' t :
      Γ ⊢ n -- n' : uint64T ->
      Γ ⊢ v -- v' : t ->
      Γ ⊢ AllocN n v -- AllocN n' v': arrayT t
  | load_transTy l l' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ Load l -- Load l' : t
  (* XXX: need to fix this and next four to be for compound
     use of prepare followed by finish *)
  | prepare_write_transTy l l' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ PrepareWrite l -- PrepareWrite l' : unitT
  | finish_store_transTy l l' v v' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ v -- v' : t ->
      Γ ⊢ FinishStore l v -- FinishStore l' v' : unitT
  | start_read_transTy l l' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ StartRead l -- StartRead l' : t
  | finish_read_transTy l l' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ FinishRead l -- FinishRead l' : unitT
  | cmpxchg_transTy l l' v1 v1' v2 v2' t :
      Γ ⊢ l -- l' : refT t ->
      Γ ⊢ v1 -- v1' : t ->
      Γ ⊢ v2 -- v2' : t ->
      Γ ⊢ CmpXchg l v1 v2 -- CmpXchg l' v1' v2' : prodT t boolT
  | external_transTy op e e' t1 t2 :
      get_ext_tys op = (t1, t2) ->
      Γ ⊢ e -- e' : t1 ->
      Γ ⊢ ExternalOp op e -- (spec_op_trans op) e' : t2
  (* Is this sound given the rules about flattening? *)
  | struct_weaken_transTy e e' ts1 ts2 :
      Γ ⊢ e -- e' : structRefT (ts1 ++ ts2) ->
      Γ ⊢ e -- e' : structRefT ts1
  | array_ref_transTy e e' t :
      Γ ⊢ e -- e' : arrayT t ->
      Γ ⊢ e -- e' : refT t
  (* XXX: remove this from the unary rules *)
  (*
  | e_any_transTy e t :
      Γ ⊢ e : t ->
      Γ ⊢ e : anyT
                     *)
  where "Γ ⊢ e1 -- e2 : A" := (expr_transTy Γ e1 e2 A)
  with val_transTy (Γ: SCtx) : sval -> ival -> sty -> Prop :=
  | val_base_lit_translateTy v t :
      base_lit_hasTy v t -> val_transTy Γ (LitV v) (LitV v) t
  | val_pair_transTy v1 v1' v2 v2' t1 t2 :
      Γ ⊢v v1 -- v1' : t1 ->
      Γ ⊢v v2 -- v2' : t2 ->
      Γ ⊢v PairV v1 v2 -- PairV v1' v2' : prodT t1 t2
  | val_injL_transTy v1 v1' t1 t2 :
      Γ ⊢v v1 -- v1' : t1 ->
      Γ ⊢v InjLV v1 -- InjLV v1' : sumT t1 t2
  | val_injR_transTy v2 v2' t1 t2 :
      Γ ⊢v v2 -- v2' : t2 ->
      Γ ⊢v InjRV v2 -- InjRV v2' : sumT t1 t2
  | rec_val_transTy f x e e' t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e -- e' : t2 ->
      Γ ⊢v RecV f x e -- RecV f x e' : arrowT t1 t2
  | mapNilV_transTy v v' t :
      Γ ⊢v v -- v' : t ->
      Γ ⊢v MapNilV v  -- MapNilV v': mapValT t
  (* Remove from unary rules *)
  (*
  | val_any_transTy v v't :
      Γ ⊢v v : t ->
      Γ ⊢v v : anyT
  *)
  | ext_def_transTy x:
      Γ ⊢v val_ty_def x -- (spec_val_trans (val_ty_def x)) : extT x
  where "Γ ⊢v v1 -- v2 : A" := (val_transTy Γ v1 v2 A).

End translate.
