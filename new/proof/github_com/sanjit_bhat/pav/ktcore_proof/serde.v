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

  enc =
    [obj.(SigTag)] ++
    u64_le (length obj.(VrfPk)) ++ obj.(VrfPk).

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

Module LinkSig.
Record t :=
  mk' {
    SigTag: w8;
    Epoch: w64;
    Link: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  sint.Z (W64 (length obj.(Link))) = length obj.(Link) ∧

  enc =
    [obj.(SigTag)] ++
    u64_le obj.(Epoch) ++
    u64_le (length obj.(Link)) ++ obj.(Link).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Link,
  "Hstruct" ∷ ptr ↦{d} (ktcore.LinkSig.mk obj.(SigTag) obj.(Epoch) sl_Link) ∗

  "Hsl_Link" ∷ sl_Link ↦*{d} obj.(Link).

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
  @! ktcore.LinkSigEncode #sl_b #ptr_obj
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
  @! ktcore.LinkSigDecode #sl_b
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
End LinkSig.

Module MapLabel.
Record t :=
  mk' {
    Uid: w64;
    Ver: w64;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  enc =
    u64_le obj.(Uid) ++
    u64_le obj.(Ver).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (ktcore.MapLabel.mk obj.(Uid) obj.(Ver)).

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
  @! ktcore.MapLabelEncode #sl_b #ptr_obj
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
  @! ktcore.MapLabelDecode #sl_b
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
End MapLabel.

Module CommitOpen.
Record t :=
  mk' {
    Val: list w8;
    Rand: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  sint.Z (W64 (length obj.(Val))) = length obj.(Val) ∧
  sint.Z (W64 (length obj.(Rand))) = length obj.(Rand) ∧

  enc =
    u64_le (length obj.(Val)) ++ obj.(Val) ++
    u64_le (length obj.(Rand)) ++ obj.(Rand).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Val sl_Rand,
  "Hstruct" ∷ ptr ↦{d} (ktcore.CommitOpen.mk sl_Val sl_Rand) ∗

  "Hsl_Val" ∷ sl_Val ↦*{d} obj.(Val) ∗
  "Hsl_Rand" ∷ sl_Rand ↦*{d} obj.(Rand).

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
  @! ktcore.CommitOpenEncode #sl_b #ptr_obj
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
  @! ktcore.CommitOpenDecode #sl_b
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
End CommitOpen.

Module Memb.
Record t :=
  mk' {
    LabelProof: list w8;
    PkOpen: CommitOpen.t;
    MerkleProof: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  ∃ enc_PkOpen,
  sint.Z (W64 (length obj.(LabelProof))) = length obj.(LabelProof) ∧
  sint.Z (W64 (length obj.(MerkleProof))) = length obj.(MerkleProof) ∧

  enc =
    u64_le (length obj.(LabelProof)) ++ obj.(LabelProof) ++
    enc_PkOpen ++
    u64_le (length obj.(MerkleProof)) ++ obj.(MerkleProof).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_LabelProof ptr_PkOpen sl_MerkleProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.Memb.mk sl_LabelProof ptr_PkOpen sl_MerkleProof) ∗

  "Hsl_LabelProof" ∷ sl_LabelProof ↦*{d} obj.(LabelProof) ∗
  "Hown_PkOpen" ∷ CommitOpen.own ptr_PkOpen obj.(PkOpen) d ∗
  "Hsl_MerkleProof" ∷ sl_MerkleProof ↦*{d} obj.(MerkleProof).

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
  @! ktcore.MembEncode #sl_b #ptr_obj
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
  @! ktcore.MembDecode #sl_b
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
End Memb.

Module NonMemb.
Record t :=
  mk' {
    LabelProof: list w8;
    MerkleProof: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  sint.Z (W64 (length obj.(LabelProof))) = length obj.(LabelProof) ∧
  sint.Z (W64 (length obj.(MerkleProof))) = length obj.(MerkleProof) ∧

  enc =
    u64_le (length obj.(LabelProof)) ++ obj.(LabelProof) ++
    u64_le (length obj.(MerkleProof)) ++ obj.(MerkleProof).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_LabelProof sl_MerkleProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.NonMemb.mk sl_LabelProof sl_MerkleProof) ∗

  "Hsl_LabelProof" ∷ sl_LabelProof ↦*{d} obj.(LabelProof) ∗
  "Hsl_MerkleProof" ∷ sl_MerkleProof ↦*{d} obj.(MerkleProof).

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
  @! ktcore.NonMembEncode #sl_b #ptr_obj
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
  @! ktcore.NonMembDecode #sl_b
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
End NonMemb.

Module UpdateProof.
Record t :=
  mk' {
    MapLabel: list w8;
    MapVal: list w8;
    NonMembProof: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  sint.Z (W64 (length obj.(MapLabel))) = length obj.(MapLabel) ∧
  sint.Z (W64 (length obj.(MapVal))) = length obj.(MapVal) ∧
  sint.Z (W64 (length obj.(NonMembProof))) = length obj.(NonMembProof) ∧

  enc =
    u64_le (length obj.(MapLabel)) ++ obj.(MapLabel) ++
    u64_le (length obj.(MapVal)) ++ obj.(MapVal) ++
    u64_le (length obj.(NonMembProof)) ++ obj.(NonMembProof).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_MapLabel sl_MapVal sl_NonMembProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.UpdateProof.mk sl_MapLabel sl_MapVal sl_NonMembProof) ∗

  "Hsl_MapLabel" ∷ sl_MapLabel ↦*{d} obj.(MapLabel) ∗
  "Hsl_MapVal" ∷ sl_MapVal ↦*{d} obj.(MapVal) ∗
  "Hsl_NonMembProof" ∷ sl_NonMembProof ↦*{d} obj.(NonMembProof).

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
  @! ktcore.UpdateProofEncode #sl_b #ptr_obj
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
  @! ktcore.UpdateProofDecode #sl_b
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
End UpdateProof.

Module AuditProof.
Record t :=
  mk' {
    Updates: list UpdateProof.t;
    LinkSig: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  ∃ enc_Updates,
  sint.Z (W64 (length obj.(Updates))) = length obj.(Updates) ∧
  Forall2 (λ o e, UpdateProof.encodes o e) obj.(Updates) enc_Updates ∧
  sint.Z (W64 (length obj.(LinkSig))) = length obj.(LinkSig) ∧

  enc =
    u64_le (length obj.(Updates)) ++ mjoin enc_Updates ++
    u64_le (length obj.(LinkSig)) ++ obj.(LinkSig).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl0_Updates sl1_Updates sl_LinkSig,
  "Hstruct" ∷ ptr ↦{d} (ktcore.AuditProof.mk sl0_Updates sl_LinkSig) ∗

  "Hsl0_Updates" ∷ sl0_Updates ↦*{d} sl1_Updates ∗
  "Hsl1_Updates" ∷ ([∗ list] ptr;obj ∈ sl1_Updates;obj.(Updates),
    UpdateProof.own ptr obj d) ∗
  "Hsl_LinkSig" ∷ sl_LinkSig ↦*{d} obj.(LinkSig).

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
  @! ktcore.AuditProofEncode #sl_b #ptr_obj
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
  @! ktcore.AuditProofDecode #sl_b
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
End AuditProof.

End ktcore.
