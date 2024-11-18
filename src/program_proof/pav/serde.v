From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

Module PreSigDig.
Record t :=
  mk {
    Epoch: w64;
    Dig: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Epoch) ++ u64_le (length obj.(Dig)) ++ obj.(Dig).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Lemma inj obj0 obj1 : encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Dig,
  "Hptr_Epoch" ∷ ptr ↦[SigDig :: "Epoch"] #obj.(Epoch) ∗
  "Hptr_Dig" ∷ ptr ↦[SigDig :: "Dig"] (slice_val sl_Dig) ∗
  "#Hsl_Dig" ∷ own_slice_small sl_Dig byteT DfracDiscarded obj.(Dig).
End defs.
End PreSigDig.

Module SigDig.
Record t :=
  mk {
    Epoch: w64;
    Dig: list w8;
    Sig: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Epoch) ++ u64_le (length obj.(Dig)) ++ obj.(Dig) ++ u64_le (length obj.(Sig)) ++ obj.(Sig).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Dig sl_Sig,
  "#Hptr_Epoch" ∷ ptr ↦[SigDig :: "Epoch"]□ #obj.(Epoch) ∗
  "#Hptr_Dig" ∷ ptr ↦[SigDig :: "Dig"]□ (slice_val sl_Dig) ∗
  "#Hsl_Dig" ∷ own_slice_small sl_Dig byteT DfracDiscarded obj.(Dig) ∗
  "#Hptr_Sig" ∷ ptr ↦[SigDig :: "Sig"]□ (slice_val sl_Sig) ∗
  "#Hsl_Sig" ∷ own_slice_small sl_Sig byteT DfracDiscarded obj.(Sig).
End defs.
End SigDig.

Module MapValPre.
Record t :=
  mk {
    Epoch: w64;
    PkCommit: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Epoch) ++ u64_le (length obj.(PkCommit)) ++ obj.(PkCommit).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
Lemma inj obj0 obj1 : encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.
End MapValPre.

Module AdtrEpochInfo.
Record t :=
  mk {
    Dig: list w8;
    ServSig: list w8;
    AdtrSig: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le (length obj.(Dig)) ++ obj.(Dig) ++ u64_le (length obj.(ServSig)) ++ obj.(ServSig) ++ u64_le (length obj.(AdtrSig)) ++ obj.(AdtrSig).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Dig sl_ServSig sl_AdtrSig,
  "#Hptr_Dig" ∷ ptr ↦[AdtrEpochInfo :: "Dig"]□ (slice_val sl_Dig) ∗
  "#Hsl_Dig" ∷ own_slice_small sl_Dig byteT DfracDiscarded obj.(Dig) ∗
  "#Hptr_ServSig" ∷ ptr ↦[AdtrEpochInfo :: "ServSig"]□ (slice_val sl_ServSig) ∗
  "#Hsl_ServSig" ∷ own_slice_small sl_ServSig byteT DfracDiscarded obj.(ServSig) ∗
  "#Hptr_AdtrSig" ∷ ptr ↦[AdtrEpochInfo :: "AdtrSig"]□ (slice_val sl_AdtrSig) ∗
  "#Hsl_AdtrSig" ∷ own_slice_small sl_AdtrSig byteT DfracDiscarded obj.(AdtrSig).
End defs.
End AdtrEpochInfo.

Module MapLabelPre.
Record t :=
  mk {
    Uid: w64;
    Ver: w64;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Uid) ++ u64_le obj.(Ver).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
End MapLabelPre.

Module UpdateProof.
Record t : Type :=
  mk {
      Updates : gmap string (list w8);
      Sig: list w8
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ (updates_mref : loc) (updatesM : gmap string (Slice.t)) sig_sl,
    "HUpdates" ∷ ptr ↦[UpdateProof :: "Updates"] #updates_mref ∗
    "HSig" ∷ ptr ↦[UpdateProof :: "Sig"] (slice_val sig_sl) ∗
    "#HUpdatesM" ∷ own_map updates_mref DfracDiscarded updatesM ∗
    "#HUpdatesMSl" ∷ ([∗ map] k ↦ sl; upd ∈ updatesM; obj.(Updates),
                       own_slice_small sl byteT DfracDiscarded upd) ∗
    "#HSigSl" ∷ own_slice_small sig_sl byteT DfracDiscarded obj.(Sig)
.

End defs.
End UpdateProof.

Module CommitOpen.
Record t :=
  mk {
    Pk: list w8;
    Rand: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  (u64_le $ length obj.(Pk)) ++ obj.(Pk) ++ (u64_le $ length obj.(Rand)) ++ obj.(Rand).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
Lemma inj obj0 obj1 : encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_pk sl_rand,
  "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded obj.(Pk) ∗
  "Hptr_pk" ∷ ptr ↦[CommitOpen :: "Pk"] (slice_val sl_pk) ∗
  "#Hsl_rand" ∷ own_slice_small sl_rand byteT DfracDiscarded obj.(Rand) ∗
  "Hptr_rand" ∷ ptr ↦[CommitOpen :: "Rand"] (slice_val sl_rand).
End defs.
End CommitOpen.
