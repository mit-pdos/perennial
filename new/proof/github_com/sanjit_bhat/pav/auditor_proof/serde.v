From New.generatedproof.github_com.sanjit_bhat.pav Require Import auditor.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.auditor_proof Require Import base.

Module auditor.

Module UpdateReply.
Record t :=
  mk' {
    Err: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(Err).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (auditor.UpdateReply.mk obj.(Err)).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! auditor.UpdateReplyEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! auditor.UpdateReplyDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End UpdateReply.

Module GetArg.
Record t :=
  mk' {
    Epoch: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(Epoch).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (auditor.GetArg.mk obj.(Epoch)).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! auditor.GetArgEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! auditor.GetArgDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End GetArg.

Module GetReply.
Record t :=
  mk' {
    Link: list w8;
    ServLinkSig: list w8;
    AdtrLinkSig: list w8;
    VrfPk: list w8;
    ServVrfSig: list w8;
    AdtrVrfSig: list w8;
    Err: w64;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(Link) ++
  safemarshal.Slice1D.pure_enc obj.(ServLinkSig) ++
  safemarshal.Slice1D.pure_enc obj.(AdtrLinkSig) ++
  safemarshal.Slice1D.pure_enc obj.(VrfPk) ++
  safemarshal.Slice1D.pure_enc obj.(ServVrfSig) ++
  safemarshal.Slice1D.pure_enc obj.(AdtrVrfSig) ++
  safemarshal.w64.pure_enc obj.(Err).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(Link) ∧
  safemarshal.Slice1D.valid obj.(ServLinkSig) ∧
  safemarshal.Slice1D.valid obj.(AdtrLinkSig) ∧
  safemarshal.Slice1D.valid obj.(VrfPk) ∧
  safemarshal.Slice1D.valid obj.(ServVrfSig) ∧
  safemarshal.Slice1D.valid obj.(AdtrVrfSig).

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

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Link sl_ServLinkSig sl_AdtrLinkSig sl_VrfPk sl_ServVrfSig sl_AdtrVrfSig,
  "Hstruct" ∷ ptr ↦{d} (auditor.GetReply.mk sl_Link sl_ServLinkSig sl_AdtrLinkSig sl_VrfPk sl_ServVrfSig sl_AdtrVrfSig obj.(Err)) ∗

  "Hsl_Link" ∷ sl_Link ↦*{d} obj.(Link) ∗
  "Hsl_ServLinkSig" ∷ sl_ServLinkSig ↦*{d} obj.(ServLinkSig) ∗
  "Hsl_AdtrLinkSig" ∷ sl_AdtrLinkSig ↦*{d} obj.(AdtrLinkSig) ∗
  "Hsl_VrfPk" ∷ sl_VrfPk ↦*{d} obj.(VrfPk) ∗
  "Hsl_ServVrfSig" ∷ sl_ServVrfSig ↦*{d} obj.(ServVrfSig) ∗
  "Hsl_AdtrVrfSig" ∷ sl_AdtrVrfSig ↦*{d} obj.(AdtrVrfSig).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! auditor.GetReplyEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! auditor.GetReplyDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End GetReply.

End auditor.
