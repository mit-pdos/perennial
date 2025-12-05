From New.generatedproof.github_com.sanjit_bhat.pav Require Import safemarshal.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.tchajed Require Import marshal.

Module safemarshal.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit safemarshal := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf safemarshal := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop safemarshal get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined safemarshal }}}
    safemarshal.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init safemarshal }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.

  wp_apply (marshal.wp_initialize' with "[$Hown]").
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  iIntros "(Hown & #?)". wp_auto.
  wp_call. iFrame. iEval (rewrite is_pkg_init_unfold).
  simpl. iFrame "#". done.
Qed.

End proof.

Module bool.

Definition pure_enc (obj : bool) :=
  [if obj then W8 1 else W8 0].

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_enc obj sl_b b :
  {{{
    is_pkg_init marshal ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1
  }}}
  @! marshal.WriteBool #sl_b #obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! safemarshal.ReadByte #sl_b
  {{{
    obj sl_tail err, RET (#obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj' tail', ⌜wish b obj' tail'⌝
    | false =>
      ∃ tail,
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End bool.

Module w8.

Definition pure_enc (obj : w8) :=
  [obj].

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_enc obj sl_b b :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1
  }}}
  @! safemarshal.WriteByte #sl_b #obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! safemarshal.ReadByte #sl_b
  {{{
    obj sl_tail err, RET (#obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj' tail', ⌜wish b obj' tail'⌝
    | false =>
      ∃ tail,
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End w8.

Module w64.

Definition pure_enc obj :=
  u64_le obj.

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_enc obj sl_b b :
  {{{
    is_pkg_init marshal ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1
  }}}
  @! marshal.WriteInt #sl_b #obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! safemarshal.ReadInt #sl_b
  {{{
    obj sl_tail err, RET (#obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj' tail', ⌜wish b obj' tail'⌝
    | false =>
      ∃ tail,
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End w64.

Module Slice1D.
Definition t := list w8.

Definition pure_enc obj :=
  w64.pure_enc (length obj) ++ obj.

Definition valid (obj : t) :=
  sint.Z (W64 (length obj)) = length obj.

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hsl_obj" ∷ ptr_obj ↦*{d} obj
  }}}
  @! safemarshal.WriteSlice1D #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    ptr_obj ↦*{d} obj ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init safemarshal ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! safemarshal.ReadSlice1D #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      ptr_obj ↦*{d} obj ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End Slice1D.

End safemarshal.
