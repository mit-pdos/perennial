From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common.

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
Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink sl_data d0 d1,
  "Hepoch" ∷ ptr ↦[chainSepSome :: "epoch"] #obj.(epoch) ∗
  "HprevLink" ∷ ptr ↦[chainSepSome :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
  "Hdata" ∷ ptr ↦[chainSepSome :: "data"] (slice_val sl_data) ∗
  "Hsl_data" ∷ own_slice_small sl_data byteT d1 obj.(data).

Lemma wp_encode ptr obj :
  {{{
    "Hobj" ∷ own ptr obj
  }}}
    chainSepSome__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj ∗
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
Definition own ptr obj : iProp Σ :=
  ∃ sl_link d0,
  "Hlink" ∷ ptr ↦[servSepLink :: "link"] (slice_val sl_link) ∗
  "Hsl_link" ∷ own_slice_small sl_link byteT d0 obj.(link).

Lemma wp_encode ptr obj :
  {{{
    "Hobj" ∷ own ptr obj
  }}}
    servSepLink__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj ∗
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

Lemma inj obj0 obj1 :
  encodesF obj0 = encodesF obj1 → obj0 = obj1.
Proof. Admitted.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_id sl_val d0 d1,
  "Hepoch" ∷ ptr ↦[servSepPut :: "epoch"] #obj.(epoch) ∗
  "Hid" ∷ ptr ↦[servSepPut :: "id"] (slice_val sl_id) ∗
  "Hsl_id" ∷ own_slice_small sl_id byteT d0 obj.(id) ∗
  "Hval" ∷ ptr ↦[servSepPut :: "val"] (slice_val sl_val) ∗
  "Hsl_val" ∷ own_slice_small sl_val byteT d1 obj.(val).

Lemma wp_encode ptr obj :
  {{{
    "Hobj" ∷ own ptr obj
  }}}
    servSepPut__encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hobj" ∷ own ptr obj ∗
    "Hsl_enc" ∷ own_slice_small sl_enc byteT (DfracOwn 1) enc ∗
    "%Henc" ∷ ⌜encodes enc obj⌝
  }}}.
Proof. Admitted.
End local_defs.
End servSepPut.

Module evidServLink.
Record t :=
  mk {
    epoch0: w64;
    prevLink0: list w8;
    dig0: list w8;
    sig0: list w8;

    epoch1: w64;
    prevLink1: list w8;
    dig1: list w8;
    sig1: list w8;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink0 sl_dig0 sl_sig0 sl_prevLink1 sl_dig1 sl_sig1 d0 d1 d2 d3 d4 d5,
  "Hepoch0" ∷ ptr ↦[evidServLink :: "epoch0"] #obj.(epoch0) ∗
  "HprevLink0" ∷ ptr ↦[evidServLink :: "prevLink0"] (slice_val sl_prevLink0) ∗
  "Hsl_prevLink0" ∷ own_slice_small sl_prevLink0 byteT d0 obj.(prevLink0) ∗
  "Hdig0" ∷ ptr ↦[evidServLink :: "dig0"] (slice_val sl_dig0) ∗
  "Hsl_dig0" ∷ own_slice_small sl_dig0 byteT d1 obj.(dig0) ∗
  "Hsig0" ∷ ptr ↦[evidServLink :: "sig0"] (slice_val sl_sig0) ∗
  "Hsl_sig0" ∷ own_slice_small sl_sig0 byteT d2 obj.(sig0) ∗

  "Hepoch1" ∷ ptr ↦[evidServLink :: "epoch1"] #obj.(epoch1) ∗
  "HprevLink1" ∷ ptr ↦[evidServLink :: "prevLink1"] (slice_val sl_prevLink1) ∗
  "Hsl_prevLink1" ∷ own_slice_small sl_prevLink1 byteT d3 obj.(prevLink1) ∗
  "Hdig1" ∷ ptr ↦[evidServLink :: "dig1"] (slice_val sl_dig1) ∗
  "Hsl_dig1" ∷ own_slice_small sl_dig1 byteT d4 obj.(dig1) ∗
  "Hsig1" ∷ ptr ↦[evidServLink :: "sig1"] (slice_val sl_sig1) ∗
  "Hsl_sig1" ∷ own_slice_small sl_sig1 byteT d5 obj.(sig1).
End local_defs.
End evidServLink.

Module evidServPut.
Record t :=
  mk {
    epoch: w64;
    (* For signed link. *)
    prevLink: list w8;
    dig: list w8;
    linkSig: list w8;
    (* For signed put. *)
    id: list w8;
    val0: list w8;
    putSig: list w8;
    (* For merkle inclusion. *)
    val1: list w8;
    proof: list (list (list w8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink sl_dig sl_linkSig sl_id sl_val0 sl_putSig sl_val1 sl_proof d0 d1 d2 d3 d4 d5 d6,
  "Hepoch" ∷ ptr ↦[evidServPut :: "epoch"] #obj.(epoch) ∗

  "HprevLink" ∷ ptr ↦[evidServPut :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT d0 obj.(prevLink) ∗
  "Hdig" ∷ ptr ↦[evidServPut :: "dig"] (slice_val sl_dig) ∗
  "Hsl_dig" ∷ own_slice_small sl_dig byteT d1 obj.(dig) ∗
  "HlinkSig" ∷ ptr ↦[evidServPut :: "linkSig"] (slice_val sl_linkSig) ∗
  "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d2 obj.(linkSig) ∗

  "Hid" ∷ ptr ↦[evidServPut :: "id"] (slice_val sl_id) ∗
  "Hsl_id" ∷ own_slice_small sl_id byteT d3 obj.(id) ∗
  "Hval0" ∷ ptr ↦[evidServPut :: "val0"] (slice_val sl_val0) ∗
  "Hsl_val0" ∷ own_slice_small sl_val0 byteT d4 obj.(val0) ∗
  "HputSig" ∷ ptr ↦[evidServPut :: "putSig"] (slice_val sl_putSig) ∗
  "Hsl_putSig" ∷ own_slice_small sl_putSig byteT d5 obj.(putSig) ∗

  "Hval1" ∷ ptr ↦[evidServPut :: "val1"] (slice_val sl_val1) ∗
  "Hsl_val1" ∷ own_slice_small sl_val1 byteT d6 obj.(val1) ∗
  "Hproof" ∷ ptr ↦[evidServPut :: "proof"] (slice_val sl_proof) ∗
  "#Hsl_proof" ∷ is_Slice3D sl_proof obj.(proof).
End local_defs.
End evidServPut.

Section other.
(* Note: the more general version of this lemma has a set of encodings
   that are within the same domain.
   if any two of these hold, we can prove false.
   there'd need to be a side req that each encoding has a diff tag. *)
Lemma servSep enc obj0 obj1 :
  servSepLink.encodes enc obj0 ∧ servSepPut.encodes enc obj1 → False.
Proof.
  intros [HencLink HencPut].
  rewrite /servSepLink.encodes /servSepLink.encodesF in HencLink.
  rewrite /servSepPut.encodes /servSepPut.encodesF in HencPut.
  naive_solver.
Qed.
End other.

Module servPutReply.
Record t :=
  mk {
    putEpoch: w64;
    prev2Link: list w8;
    prevDig: list w8;
    linkSig: list w8;
    putSig: list w8;
    error: bool;
  }.

Section local_defs.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_prev2Link sl_prevDig sl_linkSig sl_putSig d0 d1 d2 d3,
  "Herror" ∷ ptr ↦[servPutReply :: "error"] #obj.(error) ∗
  if negb obj.(error) then
    "HputEpoch" ∷ ptr ↦[servPutReply :: "putEpoch"] #obj.(putEpoch) ∗
    "Hprev2Link" ∷ ptr ↦[servPutReply :: "prev2Link"] (slice_val sl_prev2Link) ∗
    "Hsl_prev2Link" ∷ own_slice_small sl_prev2Link byteT d0 obj.(prev2Link) ∗
    "HprevDig" ∷ ptr ↦[servPutReply :: "prevDig"] (slice_val sl_prevDig) ∗
    "Hsl_prevDig" ∷ own_slice_small sl_prevDig byteT d1 obj.(prevDig) ∗
    "HlinkSig" ∷ ptr ↦[servPutReply :: "linkSig"] (slice_val sl_linkSig) ∗
    "Hsl_linkSig" ∷ own_slice_small sl_linkSig byteT d2 obj.(linkSig) ∗
    "HputSig" ∷ ptr ↦[servPutReply :: "putSig"] (slice_val sl_putSig) ∗
    "Hsl_putSig" ∷ own_slice_small sl_putSig byteT d3 obj.(putSig)
    (* Valid sigpreds, proving that the server completed the op. *)
    (*
    "#HprevLink" ∷ is_hash (chainSepSome.encodesF (chainSepSome.mk (word.sub obj.(putEpoch) (W64 1)) obj.(prev2Link) obj.(prevDig))) prevLink ∗
    "Hlink_sigpred" ∷ serv_sigpred_link γmonoLinks (servSepLink.mk prevLink) ∗
    "Hput_sigpred" ∷ serv_sigpred_put γmonoTrees (servSepPut.mk obj.(putEpoch) id val)
    *)
  else True.

End local_defs.
End servPutReply.
