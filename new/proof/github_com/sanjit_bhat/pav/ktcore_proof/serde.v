From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import safemarshal.
From New.proof.github_com.tchajed Require Import marshal.
From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import base.

Notation VrfSigTag := 0 (only parsing).
Notation LinkSigTag := 1 (only parsing).

Module ktcore.

Module VrfSig.
Record t :=
  mk' {
    SigTag: w8;
    VrfPk: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  sint.Z (W64 (length obj.(VrfPk))) = length obj.(VrfPk) ∧

  enc = [obj.(SigTag)] ++ u64_le (length obj.(VrfPk)) ++ obj.(VrfPk).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_VrfPk,
  "Hstruct" ∷ ptr ↦{d} (ktcore.VrfSig.mk obj.(SigTag) sl_VrfPk) ∗

  "Hsl_VrfPk" ∷ sl_VrfPk ↦*{d} obj.(VrfPk).

Definition wish b obj tail : iProp Σ :=
  ∃ enc,
  "%Henc_obj" ∷ ⌜encodes obj enc⌝ ∗
  "%Heq_tail" ∷ ⌜b = enc ++ tail⌝.

Lemma wish_det b obj0 obj1 tail0 tail1 :
  wish b obj0 tail0 -∗
  wish b obj1 tail1 -∗
  ⌜obj0 = obj1 ∧ tail0 = tail1⌝.
Proof. Admitted.

Lemma wp_enc sl_b b ptr_obj obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.VrfSigEncode #sl_b #ptr_obj
  {{{
    sl_b' enc, RET #sl_b';
    "Hsl_b" ∷ sl_b' ↦* (b ++ enc) ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b' 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d ∗
    "%Henc" ∷ ⌜encodes obj enc⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.VrfSigEncode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, wish b obj tail
    | false =>
      ∃ obj tail,
      "#Hwish" ∷ wish b obj tail ∗
      "Hown_obj" ∷ own ptr_obj obj d ∗
      "Hsl_tail" ∷ sl_tail ↦*{d} tail
    end
  }}}.
Proof. Admitted.

End proof.
End VrfSig.

End ktcore.
