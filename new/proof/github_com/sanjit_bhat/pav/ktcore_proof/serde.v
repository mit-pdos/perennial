From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import base.

Notation VrfSigTag := 0 (only parsing).
Notation LinkSigTag := 1 (only parsing).

(** core serde spec requirements:
- deterministic encoding of object.
- optional correctness: encoded object decodes to same object.
- security: specs usable even for weak caller.
- "composable". e.g., predicates on struct re-use field predicates.

impl:
- [pure_enc] gives deterministic encoding.
- [wish] optionally transports correctness from encoder to decoder.
it's implemented by saying "the bytestream is encoded obj with tail".
however, there's an additional restriction for variable-size objects
(e.g., lists) that the length is in-bounds.
[wish_det] deterministically maps an encoding to its object and tail.
- higher-level objects can define [pure_enc] and [wish] i.t.o. the
[pure_enc] and [wish] of lower-level objects. *)

Module ktcore.

Module VrfSig.
Record t :=
  mk' {
    SigTag: w8;
    VrfPk: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.w8.pure_enc obj.(SigTag) ++
  safemarshal.Slice1D.pure_enc obj.(VrfPk).

Definition wish b obj tail :=
  ∃ t0,
  safemarshal.w8.wish b obj.(SigTag) t0 ∧
  safemarshal.Slice1D.wish t0 obj.(VrfPk) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_VrfPk,
  "Hstruct" ∷ ptr ↦{d} (ktcore.VrfSig.mk obj.(SigTag) sl_VrfPk) ∗

  "Hsl_VrfPk" ∷ sl_VrfPk ↦*{d} obj.(VrfPk).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.VrfSigEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.VrfSigDecode #sl_b
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
End VrfSig.

Module LinkSig.
Record t :=
  mk' {
    SigTag: w8;
    Epoch: w64;
    Link: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.w8.pure_enc obj.(SigTag) ++
  safemarshal.w64.pure_enc obj.(Epoch) ++
  safemarshal.Slice1D.pure_enc obj.(Link).

Definition wish b obj tail :=
  ∃ t0 t1,
  safemarshal.w8.wish b obj.(SigTag) t0 ∧
  safemarshal.w64.wish t0 obj.(Epoch) t1 ∧
  safemarshal.Slice1D.wish t1 obj.(Link) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Link,
  "Hstruct" ∷ ptr ↦{d} (ktcore.LinkSig.mk obj.(SigTag) obj.(Epoch) sl_Link) ∗

  "Hsl_Link" ∷ sl_Link ↦*{d} obj.(Link).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.LinkSigEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.LinkSigDecode #sl_b
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
End LinkSig.

Module MapLabel.
Record t :=
  mk' {
    Uid: w64;
    Ver: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(Uid) ++
  safemarshal.w64.pure_enc obj.(Ver).

Definition wish b obj tail :=
  ∃ t0,
  safemarshal.w64.wish b obj.(Uid) t0 ∧
  safemarshal.w64.wish t0 obj.(Ver) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (ktcore.MapLabel.mk obj.(Uid) obj.(Ver)).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.MapLabelEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.MapLabelDecode #sl_b
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
End MapLabel.

Module CommitOpen.
Record t :=
  mk' {
    Val: list w8;
    Rand: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(Val) ++
  safemarshal.Slice1D.pure_enc obj.(Rand).

Definition wish b obj tail :=
  ∃ t0,
  safemarshal.Slice1D.wish b obj.(Val) t0 ∧
  safemarshal.Slice1D.wish t0 obj.(Rand) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Val sl_Rand,
  "Hstruct" ∷ ptr ↦{d} (ktcore.CommitOpen.mk sl_Val sl_Rand) ∗

  "Hsl_Val" ∷ sl_Val ↦*{d} obj.(Val) ∗
  "Hsl_Rand" ∷ sl_Rand ↦*{d} obj.(Rand).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.CommitOpenEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.CommitOpenDecode #sl_b
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
End CommitOpen.

Module Memb.
Record t :=
  mk' {
    LabelProof: list w8;
    PkOpen: CommitOpen.t;
    MerkleProof: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(LabelProof) ++
  CommitOpen.pure_enc obj.(PkOpen) ++
  safemarshal.Slice1D.pure_enc obj.(MerkleProof).

Definition wish b obj tail :=
  ∃ t0 t1,
  safemarshal.Slice1D.wish b obj.(LabelProof) t0 ∧
  CommitOpen.wish t0 obj.(PkOpen) t1 ∧
  safemarshal.Slice1D.wish t1 obj.(MerkleProof) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_LabelProof ptr_PkOpen sl_MerkleProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.Memb.mk sl_LabelProof ptr_PkOpen sl_MerkleProof) ∗

  "Hsl_LabelProof" ∷ sl_LabelProof ↦*{d} obj.(LabelProof) ∗
  "Hown_PkOpen" ∷ CommitOpen.own ptr_PkOpen obj.(PkOpen) d ∗
  "Hsl_MerkleProof" ∷ sl_MerkleProof ↦*{d} obj.(MerkleProof).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.MembEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.MembDecode #sl_b
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
End Memb.

Module NonMemb.
Record t :=
  mk' {
    LabelProof: list w8;
    MerkleProof: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(LabelProof) ++
  safemarshal.Slice1D.pure_enc obj.(MerkleProof).

Definition wish b obj tail :=
  ∃ t0,
  safemarshal.Slice1D.wish b obj.(LabelProof) t0 ∧
  safemarshal.Slice1D.wish t0 obj.(MerkleProof) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_LabelProof sl_MerkleProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.NonMemb.mk sl_LabelProof sl_MerkleProof) ∗

  "Hsl_LabelProof" ∷ sl_LabelProof ↦*{d} obj.(LabelProof) ∗
  "Hsl_MerkleProof" ∷ sl_MerkleProof ↦*{d} obj.(MerkleProof).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.NonMembEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.NonMembDecode #sl_b
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
End NonMemb.

Module UpdateProof.
Record t :=
  mk' {
    MapLabel: list w8;
    MapVal: list w8;
    NonMembProof: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(MapLabel) ++
  safemarshal.Slice1D.pure_enc obj.(MapVal) ++
  safemarshal.Slice1D.pure_enc obj.(NonMembProof).

Definition wish b obj tail :=
  ∃ t0 t1,
  safemarshal.Slice1D.wish b obj.(MapLabel) t0 ∧
  safemarshal.Slice1D.wish t0 obj.(MapVal) t1 ∧
  safemarshal.Slice1D.wish t1 obj.(NonMembProof) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_MapLabel sl_MapVal sl_NonMembProof,
  "Hstruct" ∷ ptr ↦{d} (ktcore.UpdateProof.mk sl_MapLabel sl_MapVal sl_NonMembProof) ∗

  "Hsl_MapLabel" ∷ sl_MapLabel ↦*{d} obj.(MapLabel) ∗
  "Hsl_MapVal" ∷ sl_MapVal ↦*{d} obj.(MapVal) ∗
  "Hsl_NonMembProof" ∷ sl_NonMembProof ↦*{d} obj.(NonMembProof).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.UpdateProofEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.UpdateProofDecode #sl_b
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
End UpdateProof.

Module UpdateProofSlice1D.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc (length obj) ++ mjoin (UpdateProof.pure_enc <$> obj).

(* more complex: cascading wishes across object list to [tail]. *)
Definition wish b obj tail :=
  ∃ tails t0,
  tails !! 0%nat = Some t0 ∧
  list.last tails = Some tail ∧

  safemarshal.w64.wish b (length obj) t0 ∧
  (∀ k o tPrev tNext,
    obj !! k = Some o →
    tails !! k = Some tPrev →
    tails !! S k = Some tNext →
    UpdateProof.wish tPrev o tNext).

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr0,
  ptr ↦*{d} ptr0 ∗
  ([∗ list] ptr;obj ∈ ptr0;obj,
    UpdateProof.own ptr obj d).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.UpdateProofSlice1DEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.UpdateProofSlice1DDecode #sl_b
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
End UpdateProofSlice1D.

Module AuditProof.
Record t :=
  mk' {
    Updates: list UpdateProof.t;
    LinkSig: list w8;
  }.

Definition pure_enc obj :=
  UpdateProofSlice1D.pure_enc obj.(Updates) ++
  safemarshal.Slice1D.pure_enc obj.(LinkSig).

Definition wish b obj tail :=
  ∃ t0,
  UpdateProofSlice1D.wish b obj.(Updates) t0 ∧
  safemarshal.Slice1D.wish t0 obj.(LinkSig) tail.

Lemma wish_det {b obj0 obj1 tail0 tail1} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr_Updates sl_LinkSig,
  "Hstruct" ∷ ptr ↦{d} (ktcore.AuditProof.mk ptr_Updates sl_LinkSig) ∗

  "Hsl_Updates" ∷ UpdateProofSlice1D.own ptr_Updates obj.(Updates) d ∗
  "Hsl_LinkSig" ∷ sl_LinkSig ↦*{d} obj.(LinkSig).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.AuditProofEncode #sl_b #ptr_obj
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
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.AuditProofDecode #sl_b
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
End AuditProof.

End ktcore.
