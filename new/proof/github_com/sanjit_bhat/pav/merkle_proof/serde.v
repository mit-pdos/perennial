From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base.

Module MerkleProof.
Record t :=
  mk' {
    Siblings: list w8;
    IsOtherLeaf: bool;
    LeafLabel: list w8;
    LeafVal: list w8;
  }.

Definition encodes (obj : t) (enc : list w8) : Prop :=
  uint.Z (W64 (length obj.(Siblings))) = length obj.(Siblings) ∧
  uint.Z (W64 (length obj.(LeafLabel))) = length obj.(LeafLabel) ∧
  uint.Z (W64 (length obj.(LeafVal))) = length obj.(LeafVal) ∧

  enc = u64_le (length obj.(Siblings)) ++ obj.(Siblings) ++
  [(if obj.(IsOtherLeaf) then W8 1 else W8 0)] ++
  u64_le (length obj.(LeafLabel)) ++ obj.(LeafLabel) ++
  u64_le (length obj.(LeafVal)) ++ obj.(LeafVal).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof.
  intros ? (?&?&? & Henc0) (?&?&? & Henc). subst.
  list_simplifier. move: H => Henc.
  apply app_inj_1 in Henc as [Hlen_sib Henc]; [|len].
  apply (inj u64_le) in Hlen_sib.
  apply app_inj_1 in Henc as [Heq_sib Henc]; [|word].
  inv Henc as [[Heq_found Henc']].
  apply app_inj_1 in Henc' as [Hlen_label Henc]; [|len].
  apply (inj u64_le) in Hlen_label.
  apply app_inj_1 in Henc as [Heq_label Henc]; [|word].
  apply app_inj_1 in Henc as [Hlen_val Henc]; [|len].
  apply (inj u64_le) in Hlen_val.
  assert (obj0.(IsOtherLeaf) = obj1.(IsOtherLeaf)) as ?.
  { by repeat case_match. }
  apply app_inj_1 in Henc as [Heq_val Henc]; [|word].
  destruct obj0, obj1. by simplify_eq/=.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.
Context `{!merkle.GlobalAddrs}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Siblings sl_LeafLabel sl_LeafVal,
  "Hstruct" ∷ ptr ↦{d} (merkle.MerkleProof.mk sl_Siblings
    obj.(IsOtherLeaf) sl_LeafLabel sl_LeafVal) ∗

  "Hsl_Siblings" ∷ sl_Siblings ↦*{d} obj.(Siblings) ∗
  "Hsl_LeafLabel" ∷ sl_LeafLabel ↦*{d} obj.(LeafLabel) ∗
  "Hsl_LeafVal" ∷ sl_LeafVal ↦*{d} obj.(LeafVal).

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init merkle ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  merkle @ "MerkleProofDecode" #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    let wish := (λ enc obj tail,
      ("%Henc_obj" ∷ ⌜ encodes obj enc ⌝ ∗
      "%Heq_tail" ∷ ⌜ b = enc ++ tail ⌝) : iProp Σ) in
    "Hgenie" ∷
      (⌜ err = false ⌝ ∗-∗
      ∃ enc obj tail, wish enc obj tail) ∗
    "Herr" ∷
      (∀ enc obj tail, wish enc obj tail -∗
      "Hown_obj" ∷ own ptr_obj obj d ∗
      "Hsl_tail" ∷ sl_tail ↦*{d} tail)
  }}}.
Proof. Admitted.

End proof.
End MerkleProof.
