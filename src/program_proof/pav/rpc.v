From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import misc.

Module chainSepSome.
Record t :=
  mk {
    epoch: w64;
    prevLink: list w8;
    data: list w8;
  }.

Definition encodesF (obj : t) : list w8 :=
  [(W8 1)] ++ u64_le obj.(epoch) ++ u64_le (length obj.(prevLink)) ++ obj.(prevLink) ++ u64_le (length obj.(data)) ++ obj.(data).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Lemma inj obj0 obj1 :
  encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj sl_prevLink sl_data d0 d1 : iProp Σ :=
  "Hepoch" ∷ ptr ↦[chainSepSome :: "epoch"] #obj.(epoch) ∗
  "HprevLink" ∷ ptr ↦[chainSepSome :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
  "Hdata" ∷ ptr ↦[chainSepSome :: "data"] (slice_val sl_data) ∗
  "Hsl_data" ∷ own_slice_small sl_data byteT d1 obj.(data).

Lemma wp_encode obj ptr sl_prevLink sl_data d0 d1 :
  {{{
    "Hobj" ∷ own ptr obj sl_prevLink sl_data d0 d1
  }}}
    chainSepSome__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj sl_prevLink sl_data d0 d1 ∗
    "Hsl_enc" ∷ own_slice_small sl_enc byteT (DfracOwn 1) enc ∗
    "%Henc" ∷ ⌜encodes enc obj⌝
  }}}.
Proof. Admitted.
End local_defs.
End chainSepSome.

Module servSepLink.
Record t :=
  mk {
    link: list w8;
  }.

Definition encodesF (obj : t) : list w8 :=
  [(W8 0)] ++ u64_le (length obj.(link)) ++ obj.(link).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Lemma inj obj0 obj1 :
  encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj sl_link d0 : iProp Σ :=
  "Hlink" ∷ ptr ↦[servSepLink :: "link"] (slice_val sl_link) ∗
  "Hsl_link" ∷ own_slice_small sl_link byteT d0 obj.(link).

Lemma wp_encode obj ptr sl_link d0 :
  {{{
    "Hobj" ∷ own ptr obj sl_link d0
  }}}
    servSepLink__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj sl_link d0 ∗
    "Hsl_enc" ∷ own_slice_small sl_enc byteT (DfracOwn 1) enc ∗
    "%Henc" ∷ ⌜encodes enc obj⌝
  }}}.
Proof. Admitted.
End local_defs.
End servSepLink.

Module servSepPut.
Record t :=
  mk {
    epoch: w64;
    id: list w8;
    val: list w8;
  }.

Definition encodesF (obj : t) : list w8 :=
  [(W8 1)] ++ u64_le obj.(epoch) ++ u64_le (length obj.(id)) ++ obj.(id) ++ u64_le (length obj.(val)) ++ obj.(val).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

(* TODO: use stdpp Inj. *)
Lemma inj obj0 obj1 :
  encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj sl_id sl_val d0 d1 : iProp Σ :=
  "Hepoch" ∷ ptr ↦[servSepPut :: "epoch"] #obj.(epoch) ∗
  "Hid" ∷ ptr ↦[servSepPut :: "id"] (slice_val sl_id) ∗
  "Hsl_id" ∷ own_slice_small sl_id byteT d0 obj.(id) ∗
  "Hval" ∷ ptr ↦[servSepPut :: "val"] (slice_val sl_val) ∗
  "Hsl_val" ∷ own_slice_small sl_val byteT d1 obj.(val).

Lemma wp_encode obj ptr sl_id sl_val d0 d1 :
  {{{
    "Hobj" ∷ own ptr obj sl_id sl_val d0 d1
  }}}
    servSepPut__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj sl_id sl_val d0 d1 ∗
    "Hsl_enc" ∷ own_slice_small sl_enc byteT (DfracOwn 1) enc ∗
    "%Henc" ∷ ⌜encodes enc obj⌝
  }}}.
Proof. Admitted.
End local_defs.
End servSepPut.

Section other.
(* Note: the more general version of this lemma has a set of encodings
   that are within the same domain.
   if any two of these hold, we can prove false.
   there'd need to be a side req that each encoding has a diff tag. *)
Lemma servSep_disj {enc obj0 obj1} :
  servSepLink.encodes enc obj0 → servSepPut.encodes enc obj1 → False.
Proof.
  intros HencLink HencPut.
  rewrite /servSepLink.encodes /servSepLink.encodesF in HencLink.
  rewrite /servSepPut.encodes /servSepPut.encodesF in HencPut.
  naive_solver.
Qed.
End other.

Module signedLink.
Record t :=
  mk {
    epoch: w64;
    prevLink: list w8;
    dig: list w8;
    sig: list w8;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink sl_dig sl_sig d0 d1 d2,
  "Hptr_epoch" ∷ ptr ↦[signedLink :: "epoch"] #obj.(epoch) ∗
  "Hptr_prevLink" ∷ ptr ↦[signedLink :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
  "Hptr_dig" ∷ ptr ↦[signedLink :: "dig"] (slice_val sl_dig) ∗
  "Hsl_dig" ∷ own_slice_small sl_dig byteT d1 obj.(dig) ∗
  "Hptr_sig" ∷ ptr ↦[signedLink :: "sig"] (slice_val sl_sig) ∗
  "Hsl_sig" ∷ own_slice_small sl_sig byteT d2 obj.(sig).
End local_defs.
End signedLink.

Module signedPut.
Record t :=
  mk {
    epoch: w64;
    id: list w8;
    val: list w8;
    sig: list w8;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_id sl_val sl_sig d0 d1 d2,
  "Hptr_epoch" ∷ ptr ↦[signedPut :: "epoch"] #obj.(epoch) ∗
  "Hptr_id" ∷ ptr ↦[signedPut :: "id"] (slice_val sl_id) ∗
  "Hsl_id" ∷ own_slice_small sl_id byteT d0 obj.(id) ∗
  "Hptr_val" ∷ ptr ↦[signedPut :: "val"] (slice_val sl_val) ∗
  "Hsl_val" ∷ own_slice_small sl_val byteT d1 obj.(val) ∗
  "Hptr_sig" ∷ ptr ↦[signedPut :: "sig"] (slice_val sl_sig) ∗
  "Hsl_sig" ∷ own_slice_small sl_sig byteT d2 obj.(sig).
End local_defs.
End signedPut.

Module evidServLink.
Record t :=
  mk {
    sigLn0: signedLink.t;
    sigLn1: signedLink.t;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ ptr_sigLn0 ptr_sigLn1,
  "Hown_sigLn0" ∷ signedLink.own ptr_sigLn0 obj.(sigLn0) ∗
  "Hptr_sigLn0" ∷ ptr ↦[evidServLink :: "sigLn0"] #ptr_sigLn0 ∗
  "Hown_sigLn1" ∷ signedLink.own ptr_sigLn1 obj.(sigLn1) ∗
  "Hptr_sigLn1" ∷ ptr ↦[evidServLink :: "sigLn1"] #ptr_sigLn1.
End local_defs.
End evidServLink.

Module evidServPut.
Record t :=
  mk {
    sigLn: signedLink.t;
    sigPut: signedPut.t;
    (* merkle inclusion. *)
    val: list w8;
    proof: list (list (list w8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ ptr_sigLn ptr_sigPut sl_val sl_proof d0,
  "Hown_sigLn" ∷ signedLink.own ptr_sigLn obj.(sigLn) ∗
  "Hptr_sigLn" ∷ ptr ↦[evidServPut :: "sigLn"] #ptr_sigLn ∗
  "Hown_sigPut" ∷ signedPut.own ptr_sigPut obj.(sigPut) ∗
  "Hptr_sigPut" ∷ ptr ↦[evidServPut :: "sigPut"] #ptr_sigPut ∗
  "Hptr_val" ∷ ptr ↦[evidServPut :: "val"] (slice_val sl_val) ∗
  "Hsl_val" ∷ own_slice_small sl_val byteT d0 obj.(val) ∗
  "Hptr_proof" ∷ ptr ↦[evidServPut :: "proof"] (slice_val sl_proof) ∗
  "#Hsl_proof" ∷ is_Slice3D sl_proof obj.(proof).
End local_defs.
End evidServPut.

Module servPutReply.
Record t :=
  mk {
    putEpoch: w64;
    prevLink: list w8;
    dig: list w8;
    linkSig: list w8;
    putSig: list w8;
    error: bool;
  }.

Section local_defs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink sl_dig sl_linkSig sl_putSig d0 d1 d2 d3,
  "Herror" ∷ ptr ↦[servPutReply :: "error"] #obj.(error) ∗
  if negb obj.(error) then
    "HputEpoch" ∷ ptr ↦[servPutReply :: "putEpoch"] #obj.(putEpoch) ∗
    "HprevLink" ∷ ptr ↦[servPutReply :: "prevLink"] (slice_val sl_prevLink) ∗
    "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
    "Hdig" ∷ ptr ↦[servPutReply :: "dig"] (slice_val sl_dig) ∗
    "Hsl_dig" ∷ own_slice_small sl_dig byteT d1 obj.(dig) ∗
    "HlinkSig" ∷ ptr ↦[servPutReply :: "linkSig"] (slice_val sl_linkSig) ∗
    "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d2 obj.(linkSig) ∗
    "HputSig" ∷ ptr ↦[servPutReply :: "putSig"] (slice_val sl_putSig) ∗
    "Hsl_putSig" ∷ own_slice_small sl_putSig byteT d3 obj.(putSig)
  else True.
End local_defs.
End servPutReply.
