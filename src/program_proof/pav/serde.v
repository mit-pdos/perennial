From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.
From Perennial.program_proof.pav Require Import misc.

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
  "Hptr_Epoch" ∷ ptr ↦[PreSigDig :: "Epoch"] #obj.(Epoch) ∗
  "Hptr_Dig" ∷ ptr ↦[PreSigDig :: "Dig"] (slice_val sl_Dig) ∗
  "#Hsl_Dig" ∷ own_slice_small sl_Dig byteT DfracDiscarded obj.(Dig).

Lemma wp_enc obj sl_enc (enc : list w8) ptr :
  {{{
    "Hsl_enc" ∷ own_slice sl_enc byteT (DfracOwn 1) enc ∗
    "Hown_obj" ∷ own ptr obj
  }}}
  PreSigDigEncode (slice_val sl_enc) #ptr
  {{{
    sl_enc', RET (slice_val sl_enc');
    "Hsl_enc" ∷ own_slice sl_enc' byteT (DfracOwn 1) (enc ++ encodesF obj) ∗
    "Hown_obj" ∷ own ptr obj
  }}}.
Proof. Admitted.

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

Section defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_pk_commit,
  "Hptr_epoch" ∷ ptr ↦[MapValPre :: "Epoch"] #obj.(Epoch) ∗
  "Hptr_pk_commit" ∷ ptr ↦[MapValPre :: "PkCommit"] (slice_val sl_pk_commit) ∗
  "#Hsl_pk_commit" ∷ own_slice_small sl_pk_commit byteT DfracDiscarded obj.(PkCommit).

Lemma wp_enc obj sl_enc (enc : list w8) ptr :
  {{{
    "Hsl_enc" ∷ own_slice sl_enc byteT (DfracOwn 1) enc ∗
    "Hown_obj" ∷ own ptr obj
  }}}
  MapValPreEncode (slice_val sl_enc) #ptr
  {{{
    sl_enc', RET (slice_val sl_enc');
    "Hsl_enc" ∷ own_slice sl_enc' byteT (DfracOwn 1) (enc ++ encodesF obj) ∗
    "Hown_obj" ∷ own ptr obj
  }}}.
Proof. Admitted.

(* TODO: not fully sure how to prove this, but probably relies
on the inj lemma. *)
Lemma enc_inj obj0 tail0 obj1 tail1 :
  encodesF obj0 ++ tail0 = encodesF obj1 ++ tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Lemma wp_dec sl_enc dq enc :
  {{{
    "Hsl_enc" ∷ own_slice_small sl_enc byteT dq enc
  }}}
  MapValPreDecode (slice_val sl_enc)
  {{{
    ptr_obj sl_tail (err : bool), RET (#ptr_obj, slice_val sl_tail, #err);
    "%Hgenie" ∷ (⌜ ∀ obj tail, enc = encodesF obj ++ tail → err = false ⌝) ∗
    (* TODO: with curr structure, genie user needs to apply enc_inj to unify
    their obj and tail with the one they get back from Herr.
    is there any way to rewrite the spec to avoid this? *)
    "Herr" ∷ (⌜ err = false ⌝ -∗
      ∃ obj tail,
      "Hown_obj" ∷ own ptr_obj obj ∗
      "Hsl_tail" ∷ own_slice_small sl_tail byteT dq tail ∗
      "%Henc_obj" ∷ ⌜ enc = encodesF obj ++ tail ⌝)
  }}}.
Proof. Admitted.

End defs.
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

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  "Hptr_uid" ∷ ptr ↦[MapLabelPre :: "Uid"] #obj.(Uid) ∗
  "Hptr_ver" ∷ ptr ↦[MapLabelPre :: "Ver"] #obj.(Ver).

Lemma wp_enc obj sl_enc (enc : list w8) ptr :
  {{{
    "Hsl_enc" ∷ own_slice sl_enc byteT (DfracOwn 1) enc ∗
    "Hown_obj" ∷ own ptr obj
  }}}
  MapLabelPreEncode (slice_val sl_enc) #ptr
  {{{
    sl_enc', RET (slice_val sl_enc');
    "Hsl_enc" ∷ own_slice sl_enc' byteT (DfracOwn 1) (enc ++ encodesF obj) ∗
    "Hown_obj" ∷ own ptr obj
  }}}.
Proof. Admitted.
End defs.
End MapLabelPre.

Module UpdateProof.
Record t : Type :=
  mk {
      Updates : gmap byte_string (list w8);
      Sig: list w8
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ (updates_mref : loc) (updatesM : gmap byte_string (Slice.t)) sl_sig,
    "Hptr_updates" ∷ ptr ↦[UpdateProof :: "Updates"] #updates_mref ∗
    "Hptr_sig" ∷ ptr ↦[UpdateProof :: "Sig"] (slice_val sl_sig) ∗
    "#HUpdatesM" ∷ own_map updates_mref DfracDiscarded updatesM ∗
    "#HUpdatesMSl" ∷ ([∗ map] k ↦ sl; upd ∈ updatesM; obj.(Updates),
                       own_slice_small sl byteT DfracDiscarded upd) ∗
    "#Hsl_sig" ∷ own_slice_small sl_sig byteT DfracDiscarded obj.(Sig)
.

End defs.
End UpdateProof.

Module CommitOpen.
Record t :=
  mk {
    d: dfrac;
    Val: list w8;
    Rand: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  (u64_le $ length obj.(Val)) ++ obj.(Val) ++ (u64_le $ length obj.(Rand)) ++ obj.(Rand).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
Lemma inj obj0 obj1 : encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_val sl_rand,
  "Hsl_val" ∷ own_slice_small sl_val byteT obj.(d) obj.(Val) ∗
  "Hptr_val" ∷ ptr ↦[CommitOpen :: "Val"] (slice_val sl_val) ∗
  "Hsl_rand" ∷ own_slice_small sl_rand byteT obj.(d) obj.(Rand) ∗
  "Hptr_rand" ∷ ptr ↦[CommitOpen :: "Rand"] (slice_val sl_rand).

Lemma wp_enc sl_enc (enc : list w8) ptr_obj obj :
  {{{
    "Hsl_enc" ∷ own_slice sl_enc byteT (DfracOwn 1) enc ∗
    "Hown_obj" ∷ own ptr_obj obj
  }}}
  CommitOpenEncode (slice_val sl_enc) #ptr_obj
  {{{
    sl_enc', RET (slice_val sl_enc');
    "Hsl_enc" ∷ own_slice sl_enc' byteT (DfracOwn 1) (enc ++ encodesF obj) ∗
    "Hown_obj" ∷ own ptr_obj obj
  }}}.
Proof. Admitted.
End defs.
End CommitOpen.

Module Memb.
Record t :=
  mk {
    LabelProof: list w8;
    EpochAdded: w64;
    PkOpen: CommitOpen.t;
    MerkProof: list $ list $ list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_label_proof ptr_pk_open sl_merk_proof,
  "#Hsl_label_proof" ∷ own_slice_small sl_label_proof byteT DfracDiscarded obj.(LabelProof) ∗
  "Hptr_label_proof" ∷ ptr ↦[Memb :: "LabelProof"] (slice_val sl_label_proof) ∗
  "Hptr_epoch_added" ∷ ptr ↦[Memb :: "EpochAdded"] #obj.(EpochAdded) ∗
  "Hown_pk_open" ∷ CommitOpen.own ptr_pk_open obj.(PkOpen) ∗
  "Hptr_pk_open" ∷ ptr ↦[Memb :: "PkOpen"] #ptr_pk_open ∗
  "#His_merk_proof" ∷ is_Slice3D sl_merk_proof obj.(MerkProof) ∗
  "Hptr_merk_proof" ∷ ptr ↦[Memb :: "MerkProof"] (slice_val sl_merk_proof).
End defs.
End Memb.

Module MembHide.
Record t :=
  mk {
    LabelProof: list w8;
    MapVal: list w8;
    MerkProof: list $ list $ list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_label_proof sl_map_val sl_merk_proof,
  "#Hsl_label_proof" ∷ own_slice_small sl_label_proof byteT DfracDiscarded obj.(LabelProof) ∗
  "Hptr_label_proof" ∷ ptr ↦[MembHide :: "LabelProof"] (slice_val sl_label_proof) ∗
  "#Hsl_map_val" ∷ own_slice_small sl_map_val byteT DfracDiscarded obj.(MapVal) ∗
  "Hptr_map_val" ∷ ptr ↦[MembHide :: "MapVal"] (slice_val sl_map_val) ∗
  "#His_merk_proof" ∷ is_Slice3D sl_merk_proof obj.(MerkProof) ∗
  "Hptr_merk_proof" ∷ ptr ↦[MembHide :: "MerkProof"] (slice_val sl_merk_proof).
End defs.
End MembHide.

Module NonMemb.
Record t :=
  mk {
    LabelProof: list w8;
    MerkProof: list $ list $ list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_label_proof sl_merk_proof,
  "#Hsl_label_proof" ∷ own_slice_small sl_label_proof byteT DfracDiscarded obj.(LabelProof) ∗
  "Hptr_label_proof" ∷ ptr ↦[NonMemb :: "LabelProof"] (slice_val sl_label_proof) ∗
  "#His_merk_proof" ∷ is_Slice3D sl_merk_proof obj.(MerkProof) ∗
  "Hptr_merk_proof" ∷ ptr ↦[NonMemb :: "MerkProof"] (slice_val sl_merk_proof).
End defs.
End NonMemb.
