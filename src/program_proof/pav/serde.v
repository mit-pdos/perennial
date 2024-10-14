From Perennial.program_proof Require Import grove_prelude.

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
End PreSigDig.

Module MapValPre.
Record t :=
  mk {
    Epoch: w64;
    PkComm: list w8;
  }.
Definition encodesF (obj : t) : list w8 :=
  u64_le obj.(Epoch) ++ u64_le (length obj.(PkComm)) ++ obj.(PkComm).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
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
Definition own (ptr : loc) (obj : t) : iProp Σ. Admitted.
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
