From Coq Require Import Logic.FunctionalExtensionality.
From iris.bi.lib Require Import fractional.
From Perennial.goose_lang Require Export lang lifting ipersist.
From stdpp Require Import list.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export postlang.

Section defs.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} `{!GoContext}.

Class IntoValComparable (V : Type) `{!IntoVal V} :=
  {
    #[global] into_val_inj :: Inj (=) (=) (into_val (V:=V));
    #[global] into_val_eqdec :: EqDecision V ;
    into_val_comparable : (∀ (v : V), is_comparable #v);
  }.

Class TypedPointsto (V : Type) `{!IntoVal V} :=
{
  typed_pointsto_def (l : loc) (dq : dfrac) (v : V) : iProp Σ
}.
Global Hint Mode TypedPointsto ! - : typeclass_instances.

Program Definition typed_pointsto := sealed @typed_pointsto_def.
Definition typed_pointsto_unseal : typed_pointsto = _ := seal_eq _.
Global Arguments typed_pointsto {_ _ _} (l dq v).
Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

(** [IntoValTyped V t] provides proofs that loading and storing [t] respects
    the typed points-to for `V`.

    [typed_pointsto_def] is in [IntoValProof] rather than here because `l ↦ v`
    not explicitly mention `t`, and there can be multiple `t`s for a single `V`
    (e.g. int64 and uint64 both have w64). *)
Class IntoValTyped (V : Type) (t : go.type) `{TypedPointsto V} :=
  {
    wp_alloc : ({{{ True }}}
                  alloc t #()
                {{{ l, RET #l; l ↦ (zero_val V) }}});
    wp_load : (∀ l dq (v : V), {{{ l ↦{dq} v }}}
                                 load t #l
                               {{{ RET #v; l ↦{dq} v }}});
    wp_store : (∀ l (v w : V), {{{ l ↦ v }}}
                                 store t #l #w
                               {{{ RET #(); l ↦ w }}});
  }.
(* [t] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTyped - ! - - : typeclass_instances.
End defs.

(* Non-maximally insert the arguments related to [t], [IntoVal], etc., so that
   typeclass search won't be invoked until wp_apply actually unifies the [t]. *)
Global Arguments wp_alloc {_ _ _ _ _ _ _} [_ _ _ _ _] (Φ).
Global Arguments wp_load {_ _ _ _ _ _ _} [_ _ _ _ _] (l dq v Φ).
Global Arguments wp_store {_ _ _ _ _ _ _} [_ _ _ _ _] (l v w Φ).

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Set Default Proof Using "Type".

Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {Hvalid : go.ValidCore}.

(** TypedPointsto instances *)
Program Global Instance typed_pointsto_loc : TypedPointsto loc :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_w64 : TypedPointsto w64 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_w32 : TypedPointsto w32 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_w16 : TypedPointsto w16 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_w8 : TypedPointsto w8 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_bool : TypedPointsto bool :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_string : TypedPointsto go_string :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_slice : TypedPointsto slice.t :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_func : TypedPointsto func.t :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.

Program Global Instance typed_pointsto_array (V : Type) `{!IntoVal V} n
  `{!TypedPointsto V} `{!IntoValTyped V t} : TypedPointsto (array.t t V n) :=
  {|
    typed_pointsto_def l dq v :=
      ([∗ list] i ↦ ve ∈ (vec_to_list v.(array.vec)), array_index_ref t (Z.of_nat i) l ↦ ve)%I;
  |}.

(** IntoValComparable instances *)
Ltac solve_into_val_comparable :=
  split;
  [rewrite into_val_unseal; intros ??; by inversion 1|
    apply _ |
    rewrite into_val_unseal; done].

Global Instance into_val_comparable_loc : IntoValComparable loc.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_w64 : IntoValComparable w64.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_w32 : IntoValComparable w32.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_w16 : IntoValComparable w16.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_w8 : IntoValComparable w8.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_bool : IntoValComparable bool.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_string : IntoValComparable go_string.
Proof. solve_into_val_comparable. Qed.

Global Instance into_val_comparable_slice : IntoValComparable slice.t.
Proof. solve_into_val_comparable. Qed.

End into_val_instances.
