From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.

Module chainSepSome.
Record t :=
  mk {
    epoch: w64;
    prevLink: list w8;
    data: list w8;
  }.

Definition encodesF (obj : t) : list w8 :=
  [(W8 1)] ++ u64_le obj.(epoch) ++ obj.(prevLink) ++ obj.(data).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_prevLink sl_data,
  "Hepoch" ∷ ptr ↦[chainSepSome :: "epoch"] #obj.(epoch) ∗
  "HprevLink" ∷ ptr ↦[chainSepSome :: "prevLink"] (slice_val sl_prevLink) ∗
  "Hsl_prevLink" ∷ own_slice_small sl_prevLink byteT (DfracOwn 1) obj.(prevLink) ∗
  "Hdata" ∷ ptr ↦[chainSepSome :: "data"] (slice_val sl_data) ∗
  "Hsl_data" ∷ own_slice_small sl_data byteT (DfracOwn 1) obj.(data).

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
  [(W8 0)] ++ obj.(link).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_link,
  "Hlink" ∷ ptr ↦[servSepLink :: "link"] (slice_val sl_link) ∗
  "Hsl_link" ∷ own_slice_small sl_link byteT (DfracOwn 1) obj.(link).

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
  [(W8 1)] ++ u64_le obj.(epoch) ++ obj.(id) ++ obj.(val).
Definition encodes (enc : list w8) (obj : t) : Prop :=
  enc = encodesF obj.
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
  ∃ sl_prevLink0 sl_dig0 sl_sig0 sl_prevLink1 sl_dig1 sl_sig1,
  "Hepoch0" ∷ ptr ↦[evidServLink :: "epoch0"] #obj.(epoch0) ∗
  "HprevLink0" ∷ ptr ↦[evidServLink :: "prevLink0"] (slice_val sl_prevLink0) ∗
  "Hsl_prevLink0" ∷ own_slice_small sl_prevLink0 byteT (DfracOwn 1) obj.(prevLink0) ∗
  "Hdig0" ∷ ptr ↦[evidServLink :: "dig0"] (slice_val sl_dig0) ∗
  "Hsl_dig0" ∷ own_slice_small sl_dig0 byteT (DfracOwn 1) obj.(dig0) ∗
  "Hsig0" ∷ ptr ↦[evidServLink :: "sig0"] (slice_val sl_sig0) ∗
  "Hsl_sig0" ∷ own_slice_small sl_sig0 byteT (DfracOwn 1) obj.(sig0) ∗

  "Hepoch1" ∷ ptr ↦[evidServLink :: "epoch1"] #obj.(epoch1) ∗
  "HprevLink1" ∷ ptr ↦[evidServLink :: "prevLink1"] (slice_val sl_prevLink1) ∗
  "Hsl_prevLink1" ∷ own_slice_small sl_prevLink1 byteT (DfracOwn 1) obj.(prevLink1) ∗
  "Hdig1" ∷ ptr ↦[evidServLink :: "dig1"] (slice_val sl_dig1) ∗
  "Hsl_dig1" ∷ own_slice_small sl_dig1 byteT (DfracOwn 1) obj.(dig1) ∗
  "Hsig1" ∷ ptr ↦[evidServLink :: "sig1"] (slice_val sl_sig1) ∗
  "Hsl_sig1" ∷ own_slice_small sl_sig1 byteT (DfracOwn 1) obj.(sig1).
End local_defs.
End evidServLink.

Section evidence.
Context `{!heapGS Σ, !mono_listG (list w8) Σ}.

Definition serv_sigpred_link γ (data : servSepLink.t) : iProp Σ :=
  ∃ (links : list (list w8)) (epoch : w64) (prevLink : list w8) (currDig : list w8),
  "#Hlinks" ∷ mono_list_lb_own γ links ∗
  "#Hlink" ∷ is_hash data.(servSepLink.link) (chainSepSome.encodesF (chainSepSome.mk epoch prevLink currDig)) ∗
  "%HlookPrev" ∷ ⌜links !! (uint.nat epoch - 1) = Some prevLink⌝ ∗
  "%HlookCurr" ∷ ⌜links !! uint.nat epoch = Some data.(servSepLink.link)⌝.

(* Note: False for now so we don't have to consider put promises. *)
Definition serv_sigpred_put (γ : gname) (data : servSepPut.t) : iProp Σ := False.

Definition serv_sigpred γ : (list w8 → iProp Σ) :=
  λ data,
    ((
      ∃ dataSepLink,
        ⌜servSepLink.encodes data dataSepLink⌝ ∗
        serv_sigpred_link γ dataSepLink
    )%I
    ∨
    (
      ∃ dataSepPut,
        ⌜servSepPut.encodes data dataSepPut⌝ ∗
        serv_sigpred_put γ dataSepPut
    )%I)%I.

Lemma wp_evidServLink_check ptr_evid evid pk γ hon :
  {{{
    "Hevid" ∷ evidServLink.own ptr_evid evid ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γ) hon
  }}}
  evidServLink__check #ptr_evid (slice_val pk)
  {{{
    (err : bool), RET #err;
    "Hevid" ∷ evidServLink.own ptr_evid evid ∗
    if negb err then
      "%Hhon" ∷ ⌜hon = false⌝
    else True%I
  }}}.
Proof.
  rewrite /evidServLink__check.
  iIntros (Φ) "H HΦ"; iNamed "H".
  iDestruct "Hevid" as (??????) "H"; iNamed "H".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep0) "Hptr_linkSep0".
  iDestruct (struct_fields_split with "Hptr_linkSep0") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (chainSepSome.wp_encode with "[epoch prevLink data Hsl_prevLink0 Hsl_dig0]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink0; iFrame.
  }
  iIntros (sl_link0Enc link0Enc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep0";
    iRename "Hsl_enc" into "Hsl_link0Enc";
    rename Henc into Henc_link0.
  wp_apply (wp_Hash with "Hsl_link0Enc");
    iIntros (sl_link0 link0) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_link0Enc";
    iRename "Hhash" into "Hsl_link0";
    iRename "His_hash" into "His_hash_link0".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_enc0) "Hptr_enc0".
  iDestruct (struct_fields_split with "Hptr_enc0") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link Hsl_link0]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame.
  }
  iIntros (sl_enc0 enc0) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_enc0";
    iRename "Hsl_enc" into "Hsl_enc0";
    rename Henc into Henc_enc0.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_enc0 Hsl_sig0]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_sig0";
    iRename "Hmsg" into "Hsl_enc0".
  destruct ok.
Admitted.
End evidence.
