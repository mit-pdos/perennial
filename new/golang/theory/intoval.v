From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
From iris.bi.lib Require Import fractional.
From Perennial.goose_lang Require Export lang lifting ipersist.
From stdpp Require Import list.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export postlang.

Section defs.
(** Proven (i.e. untrusted) definitions and properties associated with types `V`
    that have an `IntoVal` instance. *)
Class IntoValProof (V : Type) `{IntoVal V} :=
  {
    typed_pointsto_def `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
      (l : loc) (dq : dfrac) (v : V) : iProp Σ;
    #[global] to_val_inj :: Inj (=) (=) (to_val (V:=V));
    #[global] to_val_eqdec :: EqDecision V ;
  }.
Program Definition typed_pointsto := sealed @typed_pointsto_def.
Definition typed_pointsto_unseal : typed_pointsto = _ := seal_eq _.
Arguments typed_pointsto {_ _ _ _ _ _ _ _ _ _} (l dq v).
Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
(** [IntoValTyped V t] provides proofs that loading and storing [t] respects
    the typed points-to for `V`.

    [typed_pointsto_def] is in [IntoValProof] rather than here because `l ↦ v`
    not explicitly mention `t`, and there can be multiple `t`s for a single `V`
    (e.g. int64 and uint64 both have w64). *)
Class IntoValTyped (V : Type) (t : go.type) `{!IntoVal V} `{!IntoValProof V} :=
  {
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
