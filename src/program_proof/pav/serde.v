From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.
From Perennial.program_proof.pav Require Import misc.

(* Patterns:
1. use dfrac wherever possible in ownership preds.
allows modularity in ownership usage.
2. write encodesF separately from encodes.
this makes it easier for wish lemmas to talk about encoding things.
3. state injectivity with tail. this is used in code.
4. have wp_dec give back encodes, which should
additionally talk about things like no overflow,
which are required to prove injectivity. *)

Module PreSigDig.
Record t :=
  mk {
    Epoch: w64;
    Dig: list w8;
  }.

Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Epoch) ++ u64_le (length obj.(Dig)) ++ obj.(Dig).

Definition encodes (enc : list w8) (obj : t) : Prop :=
  uint.Z (W64 (length obj.(Dig))) = length obj.(Dig) ∧
  enc = encodesF obj.

Lemma inj obj0 obj1 enc0 enc1 tail0 tail1 :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes enc0 obj0 →
  encodes enc1 obj1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_Dig,
  "Hptr_Epoch" ∷ ptr ↦[PreSigDig :: "Epoch"]{d} #obj.(Epoch) ∗
  "Hptr_Dig" ∷ ptr ↦[PreSigDig :: "Dig"]{d} (slice_val sl_Dig) ∗
  "Hsl_Dig" ∷ own_slice_small sl_Dig byteT d obj.(Dig).

Lemma wp_enc obj sl_b (b : list w8) ptr d :
  {{{
    "Hsl_b" ∷ own_slice sl_b byteT (DfracOwn 1) b ∗
    "Hobj" ∷ own ptr obj d
  }}}
  PreSigDigEncode (slice_val sl_b) #ptr
  {{{
    sl_b' enc, RET (slice_val sl_b');
    "%Henc" ∷ ⌜ encodes enc obj ⌝ ∗
    "Hsl_b" ∷ own_slice sl_b' byteT (DfracOwn 1) (b ++ enc) ∗
    "Hobj" ∷ own ptr obj d
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
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_Dig sl_Sig,
  "Hptr_Epoch" ∷ ptr ↦[SigDig :: "Epoch"]{d} #obj.(Epoch) ∗
  "Hptr_Dig" ∷ ptr ↦[SigDig :: "Dig"]{d} (slice_val sl_Dig) ∗
  "Hsl_Dig" ∷ own_slice_small sl_Dig byteT d obj.(Dig) ∗
  "Hptr_Sig" ∷ ptr ↦[SigDig :: "Sig"]{d} (slice_val sl_Sig) ∗
  "Hsl_Sig" ∷ own_slice_small sl_Sig byteT d obj.(Sig).
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
  uint.Z (W64 (length obj.(PkCommit))) = length obj.(PkCommit) ∧
  enc = encodesF obj.

Lemma inj obj0 obj1 enc0 enc1 tail0 tail1 :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes enc0 obj0 →
  encodes enc1 obj1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof. Admitted.

Section defs.
Context `{!heapGS Σ}.
Definition own ptr obj d : iProp Σ :=
  ∃ sl_pk_commit,
  "Hptr_epoch" ∷ ptr ↦[MapValPre :: "Epoch"]{d} #obj.(Epoch) ∗
  "Hptr_pk_commit" ∷ ptr ↦[MapValPre :: "PkCommit"]{d} (slice_val sl_pk_commit) ∗
  "Hsl_pk_commit" ∷ own_slice_small sl_pk_commit byteT d obj.(PkCommit).

Lemma wp_enc obj sl_b (b : list w8) ptr d :
  {{{
    "Hsl_b" ∷ own_slice sl_b byteT (DfracOwn 1) b ∗
    "Hobj" ∷ own ptr obj d
  }}}
  MapValPreEncode (slice_val sl_b) #ptr
  {{{
    sl_b' enc, RET (slice_val sl_b');
    "%Henc" ∷ ⌜ encodes enc obj ⌝ ∗
    "Hsl_b" ∷ own_slice sl_b' byteT (DfracOwn 1) (b ++ enc) ∗
    "Hobj" ∷ own ptr obj d
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b dq b :
  {{{
    "Hsl_b" ∷ own_slice_small sl_b byteT dq b
  }}}
  MapValPreDecode (slice_val sl_b)
  {{{
    ptr_obj sl_tail (err : bool), RET (#ptr_obj, slice_val sl_tail, #err);
    let wish := (λ enc obj tail,
      ("%Henc" ∷ ⌜ encodes enc obj ⌝ ∗
      "%Heq_tail" ∷ ⌜ b = enc ++ tail ⌝) : iProp Σ) in
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗
      ∃ enc obj tail, wish enc obj tail) ∗
    "Herr" ∷
      (∀ enc obj tail, wish enc obj tail -∗
      "Hown_obj" ∷ own ptr_obj obj (DfracOwn 1) ∗
      "Hsl_tail" ∷ own_slice_small sl_tail byteT dq tail)
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
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_Dig sl_ServSig sl_AdtrSig,
  "Hptr_Dig" ∷ ptr ↦[AdtrEpochInfo :: "Dig"]{d} (slice_val sl_Dig) ∗
  "Hsl_Dig" ∷ own_slice_small sl_Dig byteT d obj.(Dig) ∗
  "Hptr_ServSig" ∷ ptr ↦[AdtrEpochInfo :: "ServSig"]{d} (slice_val sl_ServSig) ∗
  "Hsl_ServSig" ∷ own_slice_small sl_ServSig byteT d obj.(ServSig) ∗
  "Hptr_AdtrSig" ∷ ptr ↦[AdtrEpochInfo :: "AdtrSig"]{d} (slice_val sl_AdtrSig) ∗
  "Hsl_AdtrSig" ∷ own_slice_small sl_AdtrSig byteT d obj.(AdtrSig).
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
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  "Hptr_uid" ∷ ptr ↦[MapLabelPre :: "Uid"]{d} #obj.(Uid) ∗
  "Hptr_ver" ∷ ptr ↦[MapLabelPre :: "Ver"]{d} #obj.(Ver).

Lemma wp_enc obj sl_b (b : list w8) ptr d :
  {{{
    "Hsl_b" ∷ own_slice sl_b byteT (DfracOwn 1) b ∗
    "Hobj" ∷ own ptr obj d
  }}}
  MapLabelPreEncode (slice_val sl_b) #ptr
  {{{
    sl_b' enc, RET (slice_val sl_b');
    "%Henc" ∷ ⌜ encodes enc obj ⌝ ∗
    "Hsl_b" ∷ own_slice sl_b' byteT (DfracOwn 1) (b ++ enc) ∗
    "Hobj" ∷ own ptr obj d
  }}}.
Proof. Admitted.
End defs.
End MapLabelPre.

Module UpdateProof.
Record t : Type :=
  mk {
    Updates : gmap (list w8) (list w8);
    Sig: list w8
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ (updates_mref : loc) (updatesM : gmap byte_string (Slice.t)) sl_sig,
  "Hptr_updates" ∷ ptr ↦[UpdateProof :: "Updates"]{d} #updates_mref ∗
  "Hptr_sig" ∷ ptr ↦[UpdateProof :: "Sig"]{d} (slice_val sl_sig) ∗
  "HUpdatesM" ∷ own_map updates_mref d updatesM ∗
  "HUpdatesMSl" ∷ ([∗ map] k ↦ sl;y ∈ updatesM;obj.(Updates),
    own_slice_small sl byteT d y) ∗
  "Hsl_sig" ∷ own_slice_small sl_sig byteT d obj.(Sig).

End defs.
End UpdateProof.

Module CommitOpen.
Record t :=
  mk {
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

Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_val sl_rand,
  "Hsl_val" ∷ own_slice_small sl_val byteT d obj.(Val) ∗
  "Hptr_val" ∷ ptr ↦[CommitOpen :: "Val"]{d} (slice_val sl_val) ∗
  "Hsl_rand" ∷ own_slice_small sl_rand byteT d obj.(Rand) ∗
  "Hptr_rand" ∷ ptr ↦[CommitOpen :: "Rand"]{d} (slice_val sl_rand).

Lemma wp_enc sl_enc (enc : list w8) ptr_obj obj d :
  {{{
    "Hsl_enc" ∷ own_slice sl_enc byteT (DfracOwn 1) enc ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  CommitOpenEncode (slice_val sl_enc) #ptr_obj
  {{{
    sl_enc', RET (slice_val sl_enc');
    "Hsl_enc" ∷ own_slice sl_enc' byteT (DfracOwn 1) (enc ++ encodesF obj) ∗
    "Hown_obj" ∷ own ptr_obj obj d
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
    MerkleProof: list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_label_proof ptr_pk_open sl_merk_proof,
  "Hsl_labelP" ∷ own_slice_small sl_label_proof byteT d obj.(LabelProof) ∗
  "Hptr_labelP" ∷ ptr ↦[Memb :: "LabelProof"]{d} (slice_val sl_label_proof) ∗
  "Hptr_ep_add" ∷ ptr ↦[Memb :: "EpochAdded"]{d} #obj.(EpochAdded) ∗
  "Hpk_open" ∷ CommitOpen.own ptr_pk_open obj.(PkOpen) d ∗
  "Hptr_pk_open" ∷ ptr ↦[Memb :: "PkOpen"]{d} #ptr_pk_open ∗
  "Hsl_merkP" ∷ own_slice_small sl_merk_proof byteT d obj.(MerkleProof) ∗
  "Hptr_merkP" ∷ ptr ↦[Memb :: "MerkleProof"]{d} (slice_val sl_merk_proof).
End defs.
End Memb.

Module MembHide.
Record t :=
  mk {
    LabelProof: list w8;
    MapVal: list w8;
    MerkleProof: list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_label_proof sl_map_val sl_merk_proof,
  "Hsl_labelP" ∷ own_slice_small sl_label_proof byteT d obj.(LabelProof) ∗
  "Hptr_labelP" ∷ ptr ↦[MembHide :: "LabelProof"]{d} (slice_val sl_label_proof) ∗
  "Hsl_map_val" ∷ own_slice_small sl_map_val byteT d obj.(MapVal) ∗
  "Hptr_map_val" ∷ ptr ↦[MembHide :: "MapVal"]{d} (slice_val sl_map_val) ∗
  "Hsl_merkP" ∷ own_slice_small sl_merk_proof byteT d obj.(MerkleProof) ∗
  "Hptr_merkP" ∷ ptr ↦[MembHide :: "MerkleProof"]{d} (slice_val sl_merk_proof).
End defs.
End MembHide.

Module NonMemb.
Record t :=
  mk {
    LabelProof: list w8;
    MerkleProof: list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) d : iProp Σ :=
  ∃ sl_label_proof sl_merk_proof,
  "Hsl_labelP" ∷ own_slice_small sl_label_proof byteT d obj.(LabelProof) ∗
  "Hptr_labelP" ∷ ptr ↦[NonMemb :: "LabelProof"]{d} (slice_val sl_label_proof) ∗
  "Hsl_merkP" ∷ own_slice_small sl_merk_proof byteT d obj.(MerkleProof) ∗
  "Hptr_merkP" ∷ ptr ↦[NonMemb :: "MerkleProof"]{d} (slice_val sl_merk_proof).
End defs.
End NonMemb.
