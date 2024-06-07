From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang Require Export typed_mem.impl struct.impl slice.
Require Import Coq.Program.Equality.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Inductive has_go_type_aux (F : val → go_type → Prop) : val → go_type → Prop :=
  | has_go_type_aux_bool (b : bool) : has_go_type_aux F #b boolT
  | has_go_type_aux_uint64 (x : w64) : has_go_type_aux F #x uint64T
  | has_go_type_aux_uint32 (x : w32) : has_go_type_aux F #x uint32T
  | has_go_type_aux_uint16 : has_go_type_aux F nil uint16T
  | has_go_type_aux_uint8 (x : w8) : has_go_type_aux F #x uint8T

  | has_go_type_aux_int64 (x : w64) : has_go_type_aux F #x int64T
  | has_go_type_aux_int32 (x : w32) : has_go_type_aux F #x int32T
  | has_go_type_aux_int16 : has_go_type_aux F nil int16T
  | has_go_type_aux_int8 (x : w8) : has_go_type_aux F #x int8T

  | has_go_type_aux_string (s : string) : has_go_type_aux F #(str s) stringT
  | has_go_type_aux_slice elem (s : slice.t) : has_go_type_aux F (slice_val s) (sliceT elem)
  | has_go_type_aux_slice_nil elem : has_go_type_aux F slice_nil (sliceT elem)

  | has_go_type_aux_struct
      (d : descriptor) fvs
      (H : Forall (λ '(f, v),
                     match (assocl_lookup d f) with
                     | None => True
                     | Some t => F v t
                     end
                  ) fvs)
    : has_go_type_aux F (struct.mk_f d fvs) (structT d)
  | has_go_type_aux_ptr (l : loc) : has_go_type_aux F #l ptrT
  | has_go_type_aux_func f e v : has_go_type_aux F (RecV f e v) funcT
  | has_go_type_aux_func_nil : has_go_type_aux F nil funcT

  (* FIXME: interface_val *)
  | has_go_type_aux_interface (s : slice.t) : has_go_type_aux F (slice_val s) interfaceT
  | has_go_type_aux_interface_nil : has_go_type_aux F interface_nil interfaceT

  | has_go_type_aux_mapT kt vt (l : loc) : has_go_type_aux F #l (mapT kt vt)
  | has_go_type_aux_chanT t (l : loc) : has_go_type_aux F #l (chanT t)
  .


  Definition has_go_type_step_indexed (n : nat) : val → go_type → Prop :=
    fold_right (λ a f, has_go_type_aux f) (λ _ _, False) (seq 0 n).

  Definition has_go_type (v : val) (t : go_type) : Prop :=
    ∃ n, has_go_type_step_indexed n v t
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    dependent induction t; simpl.
    all: try (exists 1%nat; econstructor).
    replace (foldr PairV _ _) with (struct.mk_f decls []).
    { exists 1%nat. econstructor. done. }
    induction decls.
    { done. }
    {
      destruct a.
      simpl.
      rewrite IHdecls.
      simpl. done.
    }
  Qed.

End goose_lang.
