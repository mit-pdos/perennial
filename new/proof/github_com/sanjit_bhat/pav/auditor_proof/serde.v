From New.generatedproof.github_com.sanjit_bhat.pav Require Import auditor.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.auditor_proof Require Import base.

Module auditor.

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

Module SignedLink.
Record t :=
  mk' {
    Link: list w8;
    ServSig: list w8;
    AdtrSig: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(Link) ++
  safemarshal.Slice1D.pure_enc obj.(ServSig) ++
  safemarshal.Slice1D.pure_enc obj.(AdtrSig).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(Link) ∧
  safemarshal.Slice1D.valid obj.(ServSig) ∧
  safemarshal.Slice1D.valid obj.(AdtrSig).

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
  ∃ sl_Link sl_ServSig sl_AdtrSig,
  "Hstruct" ∷ ptr ↦{d} (auditor.SignedLink.mk sl_Link sl_ServSig sl_AdtrSig) ∗

  "Hsl_Link" ∷ sl_Link ↦*{d} obj.(Link) ∗
  "Hsl_ServSig" ∷ sl_ServSig ↦*{d} obj.(ServSig) ∗
  "Hsl_AdtrSig" ∷ sl_AdtrSig ↦*{d} obj.(AdtrSig).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! auditor.SignedLinkEncode #sl_b #ptr_obj
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
  @! auditor.SignedLinkDecode #sl_b
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
End SignedLink.

Module SignedVrf.
Record t :=
  mk' {
    VrfPk: list w8;
    ServSig: list w8;
    AdtrSig: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(VrfPk) ++
  safemarshal.Slice1D.pure_enc obj.(ServSig) ++
  safemarshal.Slice1D.pure_enc obj.(AdtrSig).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(VrfPk) ∧
  safemarshal.Slice1D.valid obj.(ServSig) ∧
  safemarshal.Slice1D.valid obj.(AdtrSig).

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
  ∃ sl_VrfPk sl_ServSig sl_AdtrSig,
  "Hstruct" ∷ ptr ↦{d} (auditor.SignedVrf.mk sl_VrfPk sl_ServSig sl_AdtrSig) ∗

  "Hsl_VrfPk" ∷ sl_VrfPk ↦*{d} obj.(VrfPk) ∗
  "Hsl_ServSig" ∷ sl_ServSig ↦*{d} obj.(ServSig) ∗
  "Hsl_AdtrSig" ∷ sl_AdtrSig ↦*{d} obj.(AdtrSig).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init auditor ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! auditor.SignedVrfEncode #sl_b #ptr_obj
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
  @! auditor.SignedVrfDecode #sl_b
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
End SignedVrf.

Module GetReply.
Record t :=
  mk' {
    Link: SignedLink.t;
    Vrf: SignedVrf.t;
    Err: bool;
  }.

Definition pure_enc obj :=
  SignedLink.pure_enc obj.(Link) ++
  SignedVrf.pure_enc obj.(Vrf) ++
  safemarshal.bool.pure_enc obj.(Err).

Definition valid obj :=
  SignedLink.valid obj.(Link) ∧
  SignedVrf.valid obj.(Vrf).

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
  ∃ ptr_Link ptr_Vrf,
  "Hstruct" ∷ ptr ↦{d} (auditor.GetReply.mk ptr_Link ptr_Vrf obj.(Err)) ∗

  "Hown_Link" ∷ SignedLink.own ptr_Link obj.(Link) d ∗
  "Hown_Vrf" ∷ SignedVrf.own ptr_Vrf obj.(Vrf) d.

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
