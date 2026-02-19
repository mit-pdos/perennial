From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.generics.helpers unittest.generics.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : generics.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) helpers := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) helpers := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) generics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) generics := build_get_is_pkg_init_wf.

Section generic_proofs.
Context `[!ZeroVal T'] `[!TypedPointsto T'] `[!IntoValTyped T' T].
Collection W' := sem + package_sem + IntoValTyped0.
Local Set Default Proof Using "W'".

Lemma wp_BoxGet (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    #(functions generics.BoxGet [T]) #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start as "_". wp_auto. wp_end.
Qed.

Lemma wp_Box__Get (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    b @! (generics.Box T) @! "Get" #()
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start as "_". wp_auto. wp_end.
Qed.

Lemma wp_Box__Get' l (b: generics.Box.t T') :
  {{{ is_pkg_init generics ∗ l ↦ b }}}
    l @! (go.PointerType $ generics.Box T) @! "Get" #()
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_Box__Get. wp_end.
Qed.

Lemma wp_makeGenericBox (value : T') :
  {{{ is_pkg_init generics }}}
    #(functions generics.makeGenericBox [T]) #value
  {{{ RET #(generics.Box.mk T' value); True }}}.
Proof.
  wp_start. wp_auto. wp_end.
Qed.
End generic_proofs.

Lemma wp_BoxGet2 (b: generics.Box.t w64) :
  {{{ is_pkg_init generics }}}
    @! generics.BoxGet2 #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start. wp_auto. wp_end.
Qed.

Lemma wp_makeBox :
  {{{ is_pkg_init generics }}}
    @! generics.makeBox #()
  {{{ RET #(generics.Box.mk _ (W64 42)); True }}}.
Proof.
  wp_start. wp_end.
Qed.

Lemma wp_useBoxGet :
  {{{ is_pkg_init generics }}}
    @! generics.useBoxGet #()
  {{{ RET #(W64 42); True }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_makeGenericBox.
  wp_apply (wp_Box__Get' with "[$x]"). wp_end.
Qed.

Lemma wp_useContainer :
  {{{ is_pkg_init generics }}}
    @! generics.useContainer #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_bind. wp_apply wp_map_make1 as "% Hm".
  wp_apply (wp_map_insert with "Hm") as "Hm".
  wp_alloc Z_ptr as "Z". wp_auto.
  wp_apply (wp_map_insert with "Hm") as "Hm".
  wp_alloc Z'_ptr as "Z'". wp_auto.
  wp_end.
Qed.

Lemma wp_useMultiParam :
  {{{ is_pkg_init generics }}}
    @! generics.useMultiParam #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto. wp_end.
Qed.

Lemma wp_multiParamFunc `[!ZeroVal A'] `[!TypedPointsto A'] `[!IntoValTyped A' A]
`[!ZeroVal B'] `[!TypedPointsto B'] `[!IntoValTyped B' B]
  (x: A') (y: B') :
  {{{ is_pkg_init generics }}}
    #(functions generics.multiParamFunc [A; B]) #x #y
  {{{ s, RET #s; s ↦* [y] }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_slice_literal as "% Hsl".
  { iIntros. wp_auto. iFrame. }
  wp_end.
Qed.

Lemma wp_useMultiParamFunc :
  {{{ is_pkg_init generics }}}
    @! generics.useMultiParamFunc #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_apply wp_multiParamFunc as "% H". wp_end.
Qed.

End wps.
