From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi cryptoutil hashchain merkle.

From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import
  serde.

Module ktcore.
Import serde.ktcore.

Section blame.
(* [BlameSpec] is defined completely outside separation logic,
so it could even be transported via the adequacy theorem. *)

Inductive BlameTys :=
  | BlameServSig
  | BlameServFull
  | BlameAdtrSig
  | BlameAdtrFull
  | BlameClients
  | BlameUnknown.

Axiom BlameTys_EqDecision : EqDecision BlameTys.
Global Existing Instance BlameTys_EqDecision.

Axiom BlameTys_Countable : Countable BlameTys.
Global Existing Instance BlameTys_Countable.

Definition Blame := gset BlameTys.

Definition blame_to_u64 (err : Blame) : w64. Admitted.

(* [BlameSpec] formalizes the notion of blaming a set of parties who
are responsible for a bad thing happening.
[interp] maps parties to is_good flags. *)
Definition BlameSpec (err : Blame) (interp : gmap BlameTys bool) :=
  err = ∅ ∨
  err = {[ BlameUnknown ]} ∨
  (* exists bad party in blame set. *)
  (∃ p, p ∈ err ∧ interp !! p = Some false).

(* TODO: curr spec allows Blame'ing more parties than are strictly responsible.
e.g., if only server is responsible for a merkle proof not verifying,
the client dev can blame both ServerFull and AuditorFull.
to fix, need notion of "minimal party set".
e.g., this might be a def, which intuitively requires that for any Blamed party,
all remaining parties are good.

TODO: i'm not sure if this is provable.
we can't unconditionally prove that someone is good.
we can only prove that someone must be bad after observing a bad event.

TODO: minmality should take into account that ServSig is a strictly
more minimal assumption than ServFull. *)
Definition minimal (err : Blame) (interp : gmap BlameTys bool) :=
  ∀ p p', p ∈ err → p' ∈ (err ∖ {[p]}) → interp !! p' = Some true.

Lemma blame_add_interp err interp0 interp1 :
  BlameSpec err interp0 →
  interp0 ⊆ interp1 →
  BlameSpec err interp1.
Proof.
  rewrite /BlameSpec.
  intros HB Hsub.
  destruct_or!; try naive_solver.
  destruct HB as (p&?&?).
  right. right.
  exists p. split; try done.
  by eapply map_subseteq_spec.
Qed.

End blame.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Lemma rw_Blame0 err :
  blame_to_u64 err = W64 0 ↔ err = ∅.
Proof. Admitted.

Lemma rw_BlameNone :
  ktcore.BlameNone = # (blame_to_u64 ∅).
Proof. Admitted.

(* TODO: would be nice to re-use Blame defs from code file.
rewriting on code.BlameServFull (#(W64 1)) doesn't work on #(W64 1) goal. *)
Lemma rw_BlameServSig :
  # (W64 1) = # (blame_to_u64 {[ BlameServSig ]}).
Proof. Admitted.

Lemma rw_BlameServFull :
  # (W64 2) = # (blame_to_u64 {[ BlameServFull ]}).
Proof. Admitted.

Lemma rw_BlameAdtrSig :
  # (W64 4) = # (blame_to_u64 {[ BlameAdtrSig ]}).
Proof. Admitted.

Lemma rw_BlameAdtrFull :
  # (W64 8) = # (blame_to_u64 {[ BlameAdtrFull ]}).
Proof. Admitted.

Lemma rw_BlameClients :
  # (W64 16) = # (blame_to_u64 {[ BlameClients ]}).
Proof. Admitted.

Lemma rw_BlameUnknown :
  # (W64 32) = # (blame_to_u64 {[ BlameUnknown ]}).
Proof. Admitted.

Lemma rw_BlameServClients :
  # (W64 18) = # (blame_to_u64 {[ BlameServFull; BlameClients ]}).
Proof. Admitted.

Lemma blame_none interp : BlameSpec ∅ interp.
Proof. rewrite /BlameSpec. naive_solver. Qed.

Lemma blame_unknown interp : BlameSpec {[ BlameUnknown ]} interp.
Proof. rewrite /BlameSpec. naive_solver. Qed.

(* iProp form so it can be iApply'd and proven with iris resources. *)
Lemma blame_one party good interp :
  (* written as "not good" bc goodness is how to learn contra. *)
  (¬ ⌜good = true⌝ : iProp Σ) -∗
  ⌜BlameSpec {[ party ]} (<[party:=good]>interp)⌝.
Proof.
  iPureIntro. intros ?. right. right.
  destruct good; try done.
  exists party.
  split; [set_solver|by simplify_map_eq/=].
Qed.

Lemma blame_two party0 party1 good0 good1 interp :
  (⌜party0 ≠ party1⌝ : iProp Σ) ∗
  ¬ ⌜(good0 = true ∧ good1 = true)⌝ -∗
  ⌜BlameSpec {[ party0; party1 ]} (<[party0:=good0]>(<[party1:=good1]>interp))⌝.
Proof.
  iPureIntro. intros [? Heq%Classical_Prop.not_and_or]. right. right.
  destruct Heq as [?|?].
  - destruct good0; try done.
    exists party0.
    split; [set_solver|by simplify_map_eq/=].
  - destruct good1; try done.
    exists party1.
    split; [set_solver|by simplify_map_eq/=].
Qed.

Definition wish_VrfSig pk vrfPk sig : iProp Σ :=
  let obj := VrfSig.mk' (W8 VrfSigTag) vrfPk in
  let enc := VrfSig.pure_enc obj in
  "#His_sig" ∷ cryptoffi.is_sig pk enc sig ∗
  "%Hvalid" ∷ ⌜VrfSig.valid obj⌝.

Lemma wp_SignVrf ptr_sk pk P sl_vrfPk vrfPk :
  let enc := VrfSig.pure_enc (VrfSig.mk' (W8 VrfSigTag) vrfPk) in
  {{{
    is_pkg_init ktcore ∗
    "#Hown_sig_sk" ∷ cryptoffi.own_sig_sk ptr_sk pk P ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "HP" ∷ P enc
  }}}
  @! ktcore.SignVrf #ptr_sk #sl_vrfPk
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#Hwish_vrfSig" ∷ wish_VrfSig pk vrfPk sig
  }}}.
Proof.
  simpl. wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPrivateKey_Sign with "[$Hsl_b $HP]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_VerifyVrfSig sl_pk pk sl_vrfPk vrfPk sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! ktcore.VerifyVrfSig #sl_pk #sl_vrfPk #sl_sig
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_VrfSig pk vrfPk sig
      | false =>
        "#Hwish_vrfSig" ∷ wish_VrfSig pk vrfPk sig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPublicKey_Verify with "[Hsl_b]") as "* H".
  { iFrame "∗#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  destruct err.
  - iIntros "@". by iApply "Hgenie0".
  - by iFrame.
Qed.

Definition wish_LinkSig pk ep link sig : iProp Σ :=
  let obj := LinkSig.mk' (W8 LinkSigTag) ep link in
  let enc := LinkSig.pure_enc obj in
  "#His_sig" ∷ cryptoffi.is_sig pk enc sig ∗
  "%Hvalid" ∷ ⌜LinkSig.valid obj⌝.

Lemma wp_SignLink ptr_sk pk P epoch sl_link link :
  let enc := LinkSig.pure_enc (LinkSig.mk' (W8 LinkSigTag) epoch link) in
  {{{
    is_pkg_init ktcore ∗
    "#Hown_sig_sk" ∷ cryptoffi.own_sig_sk ptr_sk pk P ∗
    "#Hsl_link" ∷ sl_link ↦*□ link ∗
    "HP" ∷ P enc
  }}}
  @! ktcore.SignLink #ptr_sk #epoch #sl_link
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#Hwish_linkSig" ∷ wish_LinkSig pk epoch link sig
  }}}.
Proof.
  simpl. wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (LinkSig.wp_enc (LinkSig.mk' _ _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPrivateKey_Sign with "[$Hsl_b $HP]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_VerifyLinkSig sl_pk pk epoch sl_link link sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#Hsl_link" ∷ sl_link ↦*□ link ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! ktcore.VerifyLinkSig #sl_pk #epoch #sl_link #sl_sig
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_LinkSig pk epoch link sig
      | false =>
        "#Hwish_linkSig" ∷ wish_LinkSig pk epoch link sig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (LinkSig.wp_enc (LinkSig.mk' _ _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPublicKey_Verify with "[Hsl_b]") as "* H".
  { iFrame "∗#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  destruct err.
  - iIntros "@". by iApply "Hgenie0".
  - by iFrame.
Qed.

Lemma wp_ProveMapLabel ptr_sk pk (uid ver : w64) :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_sk" ∷ cryptoffi.own_vrf_sk ptr_sk pk
  }}}
  @! ktcore.ProveMapLabel #ptr_sk #uid #ver
  {{{
    sl_label label sl_proof proof, RET (#sl_label, #sl_proof);
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗
    "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc proof ∗
    "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPrivateKey_Prove with "[$Hsl_b]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_EvalMapLabel ptr_sk pk (uid ver : w64) :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_sk" ∷ cryptoffi.own_vrf_sk ptr_sk pk
  }}}
  @! ktcore.EvalMapLabel #ptr_sk #uid #ver
  {{{
    sl_label label, RET #sl_label;
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPrivateKey_Evaluate with "[$Hsl_b]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_CheckMapLabel ptr_pk pk (uid ver : w64) sl_proof proof :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_pk pk ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! ktcore.CheckMapLabel #ptr_pk #uid #ver #sl_proof
  {{{
    sl_label label (err : bool), RET (#sl_label, #err);
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hgenie" ∷
      match err with
      | true => ¬ cryptoffi.is_vrf_proof pk enc proof
      | false =>
        "#His_proof" ∷ cryptoffi.is_vrf_proof pk enc proof ∗
        "#His_out" ∷ cryptoffi.is_vrf_out pk enc label
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPublicKey_Verify with "[$Hsl_b]") as "* H".
  { iFrame "#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_GetMapVal ptr_pkOpen pkOpen :
  {{{
    is_pkg_init ktcore ∗
    "#Hown" ∷ CommitOpen.own ptr_pkOpen pkOpen (□)
  }}}
  @! ktcore.GetMapVal #ptr_pkOpen
  {{{
    sl_MapVal MapVal, RET #sl_MapVal;
    let enc := CommitOpen.pure_enc pkOpen in
    "Hsl_MapVal" ∷ sl_MapVal ↦* MapVal ∗
    "#His_MapVal" ∷ cryptoffi.is_hash (Some enc) MapVal
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply (CommitOpen.wp_enc (CommitOpen.mk' _ _) with "[$Hown]")
    as "* (Hsl_b&Hcap_b&_)".
  { iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". }
  simpl in *.
  wp_apply (cryptoutil.wp_Hash with "[$Hsl_b]") as "* @".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_GetCommitRand sl_commitSecret commitSecret sl_label label :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_commitSecret" ∷ sl_commitSecret ↦*□ commitSecret ∗
    "#Hsl_label" ∷ sl_label ↦*□ label
  }}}
  @! ktcore.GetCommitRand #sl_commitSecret #sl_label
  {{{
    sl_rand rand, RET #sl_rand;
    let enc := commitSecret ++ label in
    "Hsl_rand" ∷ sl_rand ↦* rand ∗
    "#His_CommitRand" ∷ cryptoffi.is_hash (Some enc) rand
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr]") as "H".
  { iFrame "#". }
  iNamedSuffix "H" "0".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr0]") as "H".
  { iFrame "#". }
  iNamedSuffix "H" "1".
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr1]") as "* @".
  { iDestruct own_slice_nil as "$". }
  simpl.
  iApply "HΦ".
  iFrame "∗#".
Qed.

Definition wish_Memb pk uid ver dig memb : iProp Σ :=
  ∃ label mapVal,
  let enc_label := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  let enc_val := ktcore.CommitOpen.pure_enc memb.(ktcore.Memb.PkOpen) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc_label memb.(ktcore.Memb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc_label label ∗
  "#His_mapVal" ∷ cryptoffi.is_hash (Some enc_val) mapVal ∗
  "#Hwish_memb" ∷ merkle.wish_Memb label mapVal memb.(ktcore.Memb.MerkleProof) dig.

Definition wish_ListMemb pk uid (prefixLen : w64) dig hist : iProp Σ :=
  ([∗ list] ver ↦ memb ∈ hist,
    wish_Memb pk uid (uint.Z prefixLen + ver) dig memb).

Definition wish_NonMemb pk uid ver dig nonMemb : iProp Σ :=
  ∃ label,
  let enc := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc nonMemb.(ktcore.NonMemb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label ∗
  "#Hwish_nonMemb" ∷ merkle.wish_NonMemb label nonMemb.(ktcore.NonMemb.MerkleProof) dig.

Definition wish_ListUpdate_aux prevDig updates digs : iProp Σ :=
  "%Hlen" ∷ ⌜length digs = S (length updates)⌝ ∗
  "%Hhead" ∷ ⌜head digs = Some prevDig⌝ ∗
  "#Hwish_upds" ∷ ([∗ list] i ↦ upd ∈ updates,
    ∃ dig0 dig1,
    "%Hlook0" ∷ ⌜digs !! i = Some dig0⌝ ∗
    "%Hlook1" ∷ ⌜digs !! (S i) = Some dig1⌝ ∗
    "#Hwish_upd" ∷ merkle.wish_Update upd.(ktcore.UpdateProof.MapLabel)
      upd.(ktcore.UpdateProof.MapVal) upd.(ktcore.UpdateProof.NonMembProof)
      dig0 dig1).

Lemma wish_ListUpdate_aux_det prevDig updates digs0 digs1 :
  wish_ListUpdate_aux prevDig updates digs0 -∗
  wish_ListUpdate_aux prevDig updates digs1 -∗
  ⌜digs0 = digs1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  (* pointwise-equality suffices since merkle.UpdateProof's det give hashes. *)
  (* no way to apply [list_eq_same_length] directly. *)
  iAssert (⌜∀ (i : nat) x y,
    digs0 !! i = Some x → digs1 !! i = Some y → x = y⌝)%I as %?.
  2: { iPureIntro. eapply list_eq_same_length; [done..|]. naive_solver. }
  iIntros (i ?? Hlook0 Hlook1).
  apply lookup_lt_Some in Hlook0 as ?.
  destruct i.
  { iPureIntro.
    rewrite !head_lookup in Hhead0, Hhead1.
    by simplify_eq/=. }
  list_elem updates i as upd.
  iDestruct (big_sepL_lookup with "Hwish_upds0") as "H0"; [done|].
  iDestruct (big_sepL_lookup with "Hwish_upds1") as "H1"; [done|].
  iNamedSuffix "H0" "0".
  iNamedSuffix "H1" "1".
  simplify_eq/=.
  by iDestruct (merkle.wish_Update_det with "Hwish_upd0 Hwish_upd1") as %[-> ->].
Qed.

Lemma wish_ListUpdate_aux_take n prevDig updates digs :
  wish_ListUpdate_aux prevDig updates digs -∗
  wish_ListUpdate_aux prevDig (take n updates) (take (S n) digs).
Proof.
  iNamed 1.
  repeat iSplit; try iPureIntro; [len|by destruct digs|].
  iApply big_sepL_forall.
  iIntros (?? Hlook).
  apply lookup_take_Some in Hlook as [Hlook ?].
  iDestruct (big_sepL_lookup with "Hwish_upds") as "@"; [done|].
  rewrite lookup_take_lt; [|word].
  rewrite lookup_take_lt; [|word].
  iFrame "#%".
Qed.

Definition wish_ListUpdate prevDig updates nextDig : iProp Σ :=
  ∃ digs,
  "#Hwish_aux" ∷ wish_ListUpdate_aux prevDig updates digs ∗
  "%Hlast" ∷ ⌜last digs = Some nextDig⌝.

Lemma wish_ListUpdate_det prevDig updates nextDig0 nextDig1 :
  wish_ListUpdate prevDig updates nextDig0 -∗
  wish_ListUpdate prevDig updates nextDig1 -∗
  ⌜nextDig0 = nextDig1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_ListUpdate_aux_det with "Hwish_aux0 Hwish_aux1") as %->.
  rewrite Hlast0 in Hlast1.
  by simplify_eq/=.
Qed.

Lemma wish_ListUpdate_grow dig0 updates dig1 upd dig2 :
  wish_ListUpdate dig0 updates dig1 -∗
  merkle.wish_Update
    upd.(UpdateProof.MapLabel)
    upd.(UpdateProof.MapVal)
    upd.(UpdateProof.NonMembProof)
    dig1 dig2 -∗
  wish_ListUpdate dig0 (updates ++ [upd]) dig2.
Proof.
  iIntros "@ #Hupd". iNamed "Hwish_aux".
  iExists (digs ++ [dig2]).
  repeat iSplit; try done; try iPureIntro.
  - len.
  - by rewrite head_app Hhead.
  - iApply big_sepL_forall.
    iIntros (?? Hlook).
    apply lookup_lt_Some in Hlook as ?.
    rewrite lookup_app_l; [|word].
    rewrite lookup_app_l; [|word].
    iDestruct (big_sepL_lookup with "Hwish_upds") as "@"; [done|].
    iFrame "#%".
  - iFrame "#". iPureIntro. split.
    + rewrite lookup_app_l; [|word].
      rewrite last_lookup in Hlast.
      rewrite -Hlast.
      f_equal. word.
    + rewrite lookup_app_r; [|word].
      rewrite list_lookup_singleton_Some.
      split; [word|done].
  - by rewrite last_snoc.
Qed.

(* TODO: might not need det property.
might not directly use this in BlameSpec "simulation" arg
across server and auditor. *)
Definition wish_ListAudit (prevEp : w64) prevDigs cut sigPk audits digs : iProp Σ :=
  ∃ prevDig newDigs,
  "%Heq_digs" ∷ ⌜digs = prevDigs ++ newDigs⌝ ∗
  "%Heq_prevDig" ∷ ⌜last prevDigs = Some prevDig⌝ ∗
  "%Hlen_newDigs" ∷ ⌜length newDigs = length audits⌝ ∗
  "#His_digs" ∷ ([∗ list] i ↦ aud ∈ audits,
    ∃ dig0 dig1,
    "%Hlook0" ∷ ⌜(prevDig :: newDigs) !! i = Some dig0⌝ ∗
    "%Hlook1" ∷ ⌜(prevDig :: newDigs) !! (S i) = Some dig1⌝ ∗
    "#Hwish_ListUpdate" ∷ wish_ListUpdate dig0 aud.(AuditProof.Updates) dig1) ∗
  "#His_sigs" ∷ ([∗ list] i ↦ aud ∈ audits,
    ∃ link,
    let ep := (uint.nat prevEp + S i)%nat in
    "#His_link" ∷ hashchain.is_chain (prevDigs ++ take (S i) newDigs)
      cut link (S ep) ∗
    "#Hwish_LinkSig" ∷ wish_LinkSig sigPk (W64 ep) link aud.(AuditProof.LinkSig)).

End proof.
End ktcore.
