From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.base_logic Require Import ghost_map.

Module chainSepNone.
Definition encoding : list w8 := [(W8 0)].
Section local_defs.
Context `{!heapGS Σ}.
Definition hashes_to (h : list w8) : iProp Σ :=
  is_hash encoding h.
End local_defs.
End chainSepNone.

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

Section servpreds.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition serv_sigpred_link γmonoLinks (data : servSepLink.t) : iProp Σ :=
  ∃ (epoch : w64) (prevLink dig : list w8),
  "#Hbind" ∷ is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink dig)) data.(servSepLink.link) ∗
  "#HidxPrev" ∷ mono_list_idx_own γmonoLinks (uint.nat (word.sub epoch (W64 1))) prevLink ∗
  "#HidxCurr" ∷ mono_list_idx_own γmonoLinks (uint.nat epoch) data.(servSepLink.link).

Definition serv_sigpred_put γmonoTrs (data : servSepPut.t) : iProp Σ :=
  ∃ γtr,
  "Htr" ∷ mono_list_idx_own γmonoTrs (uint.nat data.(servSepPut.epoch)) γtr ∗
  "Hentry" ∷ data.(servSepPut.id) ↪[γtr]□ data.(servSepPut.val).

Definition serv_sigpred γmonoLinks γmonoTrs : (list w8 → iProp Σ) :=
  λ data,
    ((
      ∃ dataSepLink,
        ⌜servSepLink.encodes data dataSepLink⌝ ∗
        serv_sigpred_link γmonoLinks dataSepLink
    )%I
    ∨
    (
      ∃ dataSepPut,
        ⌜servSepPut.encodes data dataSepPut⌝ ∗
        serv_sigpred_put γmonoTrs dataSepPut
    )%I)%I.
End servpreds.

Section evidence.
Context `{!heapGS Σ, !mono_listG (list w8) Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Lemma wp_evidServLink_check ptr_evid evid pk γmonoLinks γmonoTrs hon :
  {{{
    "Hevid" ∷ evidServLink.own ptr_evid evid ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γmonoLinks γmonoTrs) hon
  }}}
  evidServLink__check #ptr_evid (slice_val pk)
  {{{
    (err : bool), RET #err;
    if negb err then
      "%Hhon" ∷ ⌜hon = false⌝
    else True%I
  }}}.
Proof. Admitted.
(*
  rewrite /evidServLink__check.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hevid".

  (* first link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep0) "Hptr_linkSep0".
  iDestruct (struct_fields_split with "Hptr_linkSep0") as "H";
    iNamed "H"; iClear "tag".
  iMod (own_slice_small_persist with "Hsl_prevLink0") as "#Hsl_prevLink0".
  wp_apply (chainSepSome.wp_encode with "[epoch prevLink data Hsl_prevLink0 Hsl_dig0]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink0, sl_dig0; iFrame "#∗".
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
  iMod (own_slice_small_persist with "Hsl_link0") as "#Hsl_link0".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_enc0) "Hptr_enc0".
  iDestruct (struct_fields_split with "Hptr_enc0") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_enc0 enc0) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_enc0";
    iRename "Hsl_enc" into "Hsl_enc0";
    rename Henc into Henc_enc0.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_enc0 Hsl_sig0]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_sig0";
    iRename "Hmsg" into "Hsl_enc0";
    iRename "HP" into "Hsigpred0".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* second link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep1) "Hptr_linkSep1".
  iDestruct (struct_fields_split with "Hptr_linkSep1") as "H";
    iNamed "H"; iClear "tag".
  iMod (own_slice_small_persist with "Hsl_prevLink1") as "#Hsl_prevLink1".
  wp_apply (chainSepSome.wp_encode with "[epoch prevLink data Hsl_prevLink1 Hsl_dig1]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink1, sl_dig1; iFrame "#∗".
  }
  iIntros (sl_link1Enc link1Enc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep1";
    iRename "Hsl_enc" into "Hsl_link1Enc";
    rename Henc into Henc_link1.
  wp_apply (wp_Hash with "Hsl_link1Enc");
    iIntros (sl_link1 link1) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_link1Enc";
    iRename "Hhash" into "Hsl_link1";
    iRename "His_hash" into "His_hash_link1".
  iMod (own_slice_small_persist with "Hsl_link1") as "#Hsl_link1".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_enc1) "Hptr_enc1".
  iDestruct (struct_fields_split with "Hptr_enc1") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_enc1 enc1) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_enc1";
    iRename "Hsl_enc" into "Hsl_enc1";
    rename Henc into Henc_enc1.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_enc1 Hsl_sig1]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_sig1";
    iRename "Hmsg" into "Hsl_enc1".
    iRename "HP" into "Hsigpred1".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* epochs are equal. *)
  wp_loadField.
  wp_loadField.
  wp_if_destruct; rename Heqb into Hepoch_eq.
  1: {
    (* TODO: why does:
      wp_apply (wp_BytesEqual "[$Hsl_link0 $Hsl_link1]").
      not work? *)
    wp_apply wp_BytesEqual; [iFrame "#"|].
    iIntros "_".
    case_bool_decide; [by iApply "HΦ"|]; rename H into Hlink_ne.
    destruct hon; [|by iApply "HΦ"].
    iDestruct "Hsigpred0" as "[[%sepLink0 [%Henc_link0' Hsigpred0]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }
    iDestruct "Hsigpred1" as "[[%sepLink1 [%Henc_link1' Hsigpred1]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }

    (* open binding, apply val divergence to prove false. *)
    iExFalso.
    rewrite ->Henc_link0' in Henc_enc0;
      apply servSepLink.inj in Henc_enc0 as ->.
    rewrite ->Henc_link1' in Henc_enc1;
      apply servSepLink.inj in Henc_enc1 as ->.
    iDestruct "Hsigpred0" as (epoch0 prevLink0 dig0) "H"; iNamed "H";
      iRename "Hbind" into "Hbind0";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr0".
    iDestruct "Hsigpred1" as (epoch1 prevLink1 dig1) "H"; iNamed "H";
      iRename "Hbind" into "Hbind1";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr1".
    iDestruct (hash_inj with "[$His_hash_link0] [$Hbind0]") as %->.
    iDestruct (hash_inj with "[$His_hash_link1] [$Hbind1]") as %->.
    apply chainSepSome.inj in Henc_link0 as [=]; subst.
    apply chainSepSome.inj in Henc_link1 as [=]; subst.
    iEval (rewrite Hepoch_eq) in "HidxCurr0".
    iDestruct (mono_list_idx_agree with "[$HidxCurr0] [$HidxCurr1]") as %[=].
    done.
  }

  (* epochs are off by one, but apart from that,
     almost same analysis as epoch equals case. *)
  wp_loadField.
  wp_loadField.
  wp_if_destruct; rename Heqb into Hepoch_off_eq.
  1: {
    wp_loadField.
    wp_apply wp_BytesEqual; [iFrame "#"|].
    iIntros "_".
    case_bool_decide; [by iApply "HΦ"|]; rename H into Hlink_ne.
    destruct hon; [|by iApply "HΦ"].
    iDestruct "Hsigpred0" as "[[%sepLink0 [%Henc_link0' Hsigpred0]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }
    iDestruct "Hsigpred1" as "[[%sepLink1 [%Henc_link1' Hsigpred1]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }

    iExFalso.
    rewrite ->Henc_link0' in Henc_enc0;
      apply servSepLink.inj in Henc_enc0 as ->.
    rewrite ->Henc_link1' in Henc_enc1;
      apply servSepLink.inj in Henc_enc1 as ->.
    iDestruct "Hsigpred0" as (epoch0 prevLink0 dig0) "H"; iNamed "H";
      iRename "Hbind" into "Hbind0";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr0".
    iDestruct "Hsigpred1" as (epoc10 prevLink1 dig1) "H"; iNamed "H";
      iRename "Hbind" into "Hbind1";
      iRename "HidxPrev" into "HidxPrev1";
      iClear "HidxCurr".
    iDestruct (hash_inj with "[$His_hash_link0] [$Hbind0]") as %->.
    iDestruct (hash_inj with "[$His_hash_link1] [$Hbind1]") as %->.
    apply chainSepSome.inj in Henc_link0 as [=]; subst.
    apply chainSepSome.inj in Henc_link1 as [=]; subst.
    iEval (rewrite Hepoch_off_eq) in "HidxCurr0".
    iDestruct (mono_list_idx_agree with "[$HidxCurr0] [$HidxPrev1]") as %[=].
    done.
  }
  by iApply "HΦ".
Qed.
*)

Lemma wp_evidServPut_check ptr_evid evid pk γmonoLinks γmonoTrees hon :
  {{{
    "Hevid" ∷ evidServPut.own ptr_evid evid ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γmonoLinks γmonoTrees) hon
  }}}
  evidServPut__check #ptr_evid (slice_val pk)
  {{{
    (err : bool), RET #err;
    if negb err then
      "%Hhon" ∷ ⌜hon = false⌝
    else True%I
  }}}.
Proof. Admitted.
(*
  rewrite /evidServPut__check.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hevid".

  (* verify link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep) "Hptr_linkSep".
  iMod (own_slice_small_persist with "Hsl_prevLink") as "#Hsl_prevLink".
  iMod (own_slice_small_persist with "Hsl_dig") as "#Hsl_dig".
  wp_apply (chainSepSome.wp_encode with "[Hptr_linkSep]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    iDestruct (struct_fields_split with "Hptr_linkSep") as "H"; iNamed "H".
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink, sl_dig; iFrame "#∗".
  }
  iIntros (sl_linkEnc linkEnc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep";
    iRename "Hsl_enc" into "Hsl_linkEnc";
    rename Henc into Henc_link.
  wp_apply (wp_Hash with "Hsl_linkEnc");
    iIntros (sl_link link) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_linkEnc";
    iRename "Hhash" into "Hsl_link";
    iRename "His_hash" into "His_hash_link".
  iMod (own_slice_small_persist with "Hsl_link") as "#Hsl_link".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_preLinkSig) "Hptr_preLinkSig".
  iDestruct (struct_fields_split with "Hptr_preLinkSig") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_preLinkSig preLinkSig) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_preLinkSig";
    iRename "Hsl_enc" into "Hsl_preLinkSig";
    rename Henc into Henc_preLinkSig.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_preLinkSig Hsl_linkSig]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_linkSig";
    iRename "Hmsg" into "Hsl_preLinkSig";
    iRename "HP" into "HlinkSigPred".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* verify put promise sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_strPrePut) "Hptr_strPrePut".
  iMod (own_slice_small_persist with "Hsl_id") as "#Hsl_id".
  iMod (own_slice_small_persist with "Hsl_val0") as "#Hsl_val0".
  wp_apply (servSepPut.wp_encode with "[Hptr_strPrePut]").
  {
    instantiate (1:=servSepPut.mk _ _ _).
    iDestruct (struct_fields_split with "Hptr_strPrePut") as "H"; iNamed "H".
    rewrite /servSepPut.own /=.
    iExists sl_id, sl_val0.
    iFrame "#∗".
  }
  iIntros (sl_prePut prePut) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_prePut";
    iRename "Hsl_enc" into "Hsl_prePut";
    rename Henc into Henc_prePut.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_prePut Hsl_putSig]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_putSig";
    iRename "Hmsg" into "Hsl_prePut";
    iRename "HP" into "HputSigPred".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* check merkle proof. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iMod (own_slice_small_persist with "Hsl_val1") as "#Hsl_val1".
  wp_apply (wp_CheckProof with "[Hid]"); [iFrame "#∗"|].
  iIntros (err0) "Herr0".
  destruct err0; [wp_pures; by iApply "HΦ"|].
  wp_loadField.
  wp_loadField.
  wp_apply wp_BytesEqual; [iFrame "#"|]; iIntros "_".

  (* final stretch. *)
  case_bool_decide; [by iApply "HΦ"|]; move: H => Hval_eq.
  destruct hon; [|by iApply "HΦ"].
  iExFalso.

  (* process link sig. *)
  iDestruct "HlinkSigPred" as "[[%sepLink [%Henc_link' #HlinkSigPred]] | [% [% _]]]".
  2: { exfalso. eauto using servSep. }
  rewrite ->Henc_link' in Henc_preLinkSig;
    apply servSepLink.inj in Henc_preLinkSig as ->.
  iDestruct "HlinkSigPred" as (epoch prevLink dig) "H"; iNamed "H";
    iClear "HidxPrev";
    iRename "HidxCurr" into "HidxCurr".
  iDestruct (hash_inj with "[$His_hash_link] [$Hbind]") as %->; iClear "Hbind".
  apply chainSepSome.inj in Henc_link as [=]; subst.

  (* process put sig. *)
  iDestruct "HputSigPred" as "[[% [% _]] | [%sepPut [%Henc_put' #HputSigPred]]]".
  { exfalso. eauto using servSep. }
  rewrite ->Henc_put' in Henc_prePut;
    apply servSepPut.inj in Henc_prePut as ->.
  iDestruct ("HputSigPred" $! link with "[$HidxCurr]") as "{HputSigPred} [%prevLink' [%dig' H]]";
    iNamed "H".
  simpl.
  iDestruct (hash_inj with "[$His_hash_link] [$Hbind]") as %Heq; iClear "Hbind".
  apply chainSepSome.inj in Heq as [=]; subst.

  (* derive contra from conflicting is_path_val's. *)
  iDestruct (is_path_val_inj with "[$Hmerkle] [$Herr0]") as %[=].
  done.
Qed.
*)
End evidence.
