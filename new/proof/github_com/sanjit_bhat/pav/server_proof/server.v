From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle sigpred.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde.

From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module server.
Import serde.server.

(* gmap from uid's to list of pks (indexed by version). *)
Definition keys_ty := gmap w64 (list $ list w8).

Module state.
Record t :=
  mk {
    (* pending map of all keys.
    client gives server permission to add to this.
    all writable post-conds only reference pending. *)
    pending: keys_ty;
    (* history of digs and keys.
    server can update this by adding dig that corresponds to curr pending.
    all read-only post-conds only reference hist. *)
    (* TODO: technically, can derive keys from dig,
    just like we derive link from digs in below specs.
    that would be a bit more work since a dig inverts to a merkle map,
    which requires a few more steps to connect to (uid, ver, pk). *)
    hist: list (list w8 * keys_ty);
  }.
End state.

Module cfg.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
    (* map from uid to gname. *)
    uidγ: gmap w64 gname;
    histγ: gname;
    (* for now, have sigpred GS be diff from serv.hist GS.
    serv.hist GS talks about keys, whereas auditor (sharing same sigpred),
    doesn't have the plaintext keys. *)
    sigpredγ: sigpred.cfg.t;
  }.
End cfg.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

(** invariants. *)

Implicit Types γ : cfg.t.
Implicit Types σ : state.t.

Definition gs_inv γ σ : iProp Σ :=
  "#Hpend" ∷ ([∗ map] uid ↦ pks ∈ σ.(state.pending),
    ∃ uidγ,
    "%Hlook_uidγ" ∷ ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
    "#Hpks" ∷ ([∗ list] ver ↦ pk ∈ pks,
      ∃ i,
      (* client owns mlist_auth for their uid.
      for adversarial uid, auth in inv. *)
      mono_list_idx_own uidγ i ((W64 ver), pk))) ∗
  (* client remembers lb's of this. *)
  "Hhist" ∷ mono_list_auth_own γ.(cfg.histγ) 1 σ.(state.hist).

Definition keys_sub : relation keys_ty := map_included (λ _, prefix).

(* TODO: unclear if we need to relate dig to keys in σ.(hist).
might be able to prove client correctness and serv specs without it.
note: serv can maintain inv that ties its merkle tree to both
lastDig and lastKeys. *)
Definition state_inv σ : iProp Σ :=
  "%Hpend" ∷ ⌜(∀ lastHist,
    last σ.(state.hist) = Some lastHist →
    keys_sub lastHist.2 σ.(state.pending))⌝ ∗
  "%Hhist" ∷ ⌜(∀ i hist0 hist1,
    σ.(state.hist) !! i = Some hist0 →
    σ.(state.hist) !! (S i) = Some hist1 →
    keys_sub hist0.2 hist1.2)⌝.

Axiom own_Server : ∀ γ σ, iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Definition serv_inv γ : iProp Σ :=
  ∃ σ,
  "Hserv" ∷ own_Server γ σ ∗
  "Hgs" ∷ gs_inv γ σ ∗
  "#Hstate" ∷ state_inv σ.

Definition is_Server (s : loc) γ : iProp Σ :=
  inv nroot (serv_inv γ).

(** state transition ops. *)

Lemma op_read s γ :
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    (λ σ, mono_list_lb_own γ.(cfg.histγ) σ.(state.hist)) σ)).
Proof.
  iIntros "#His_serv".
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iMod "Hmask" as "_".
  iNamed "Hgs".
  iDestruct (mono_list_lb_own_get with "Hhist") as "#Hlb".
  iMod ("Hclose" with "[-]") as "_"; by iFrame "∗#".
Qed.

Definition pure_put uid pk (ver : w64) (pend : keys_ty) :=
  let pks := pend !!! uid in
  (* drop put if not right version.
  this enforces a "linear" version history. *)
  if bool_decide (uint.nat ver ≠ length pks) then pend else
  <[uid:=pks ++ [pk]]>pend.

Lemma sub_over_put pend uid pk ver :
  keys_sub pend (pure_put uid pk ver pend).
Proof.
  rewrite /pure_put.
  case_bool_decide; [done|].
  rewrite /keys_sub.
  apply insert_included; [apply _|].
  rewrite lookup_total_alt.
  intros ? ->. simpl.
  by apply prefix_app_r.
Qed.

Lemma op_put s γ uid uidγ i ver pk :
  is_Server s γ -∗
  ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ -∗
  mono_list_idx_own uidγ i (ver, pk) -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    let σ' := set state.pending (pure_put uid pk ver) σ in
    (own_Server γ σ' ={∅,⊤}=∗ True)).
Proof.
  iIntros "#His_serv %Hlook_uidγ #Hmono_idx".
  iModIntro.
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); [|done].
  iModIntro.
  iFrame.

  destruct σ. simpl in *.
  iSplitL.
  - iNamed "Hgs". iFrame.
    rewrite /pure_put /=.
    case_bool_decide; [iFrame "#"|].
    iApply big_sepM_insert_2; [|iFrame "#"].
    iFrame "%".
    iApply big_sepL_snoc.
    iSplit.
    2: { iExists _. iExactEq "Hmono_idx". repeat f_equal. word. }
    rewrite lookup_total_alt.
    destruct (pending !! uid) eqn:Hlook;
      rewrite Hlook; simpl; [|done].
    iDestruct (big_sepM_lookup with "Hpend") as "@"; [done|].
    by simplify_eq/=.
  - iNamed "Hstate".
    iSplit; iPureIntro; simpl; [|done].
    intros.
    trans pending; [naive_solver|].
    apply sub_over_put.
Qed.

Lemma op_add_hist s γ dig :
  is_Server s γ -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    let σ' := set (state.hist) (.++ [(dig, σ.(state.pending))]) σ in
    (own_Server γ σ' ={∅,⊤}=∗ True)).
Proof.
  iIntros "#His_serv".
  iModIntro.
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iNamed "Hgs".
  iNamed "Hstate".
  iMod (mono_list_auth_own_update_app with "Hhist") as "[Hhist _]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); [|done].
  iModIntro.
  iFrame "∗∗#".

  destruct σ. simpl in *.
  iSplit; iPureIntro; simpl.
  - intros ? Hlast. rewrite last_snoc in Hlast.
    by simplify_eq/=.
  - intros i ?? Hlook0 Hlook1.
    apply lookup_lt_Some in Hlook1 as ?.
    autorewrite with len in *.
    destruct (decide (S i = length hist)).
    + rewrite lookup_app_l in Hlook0; [|lia].
      rewrite lookup_app_r in Hlook1; [|lia].
      apply list_lookup_singleton_Some in Hlook1 as [_ ?].
      replace i with (pred (length hist)) in Hlook0 by lia.
      rewrite -last_lookup in Hlook0.
      naive_solver.
    + rewrite !lookup_app_l in Hlook0, Hlook1; [|lia..].
      naive_solver.
Qed.

(** specs. *)

Lemma wp_Server_Put s γ uid sl_pk pk ver :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    (* caller doesn't need anything from Put. *)
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      let σ' := set state.pending (pure_put uid pk ver) σ in
      (own_Server γ σ' ={∅,⊤}=∗ True))
  }}}
  s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver
  {{{ RET #(); True }}}.
Proof. Admitted.

Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen
  {{{
    sl_chainProof sl_linkSig sl_hist ptr_bound err lastDig lastKeys lastLink σ,
    RET (#sl_chainProof, #sl_linkSig, #sl_hist, #ptr_bound, #err);
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "HQ" ∷ Q σ ∗
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗
    "#Hgenie" ∷
      match err with
      | true =>
        "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist) ∨
          uint.nat prevVerLen > length pks⌝
      | false =>
        ∃ chainProof linkSig hist bound,
        "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist) ∧
          uint.nat prevVerLen ≤ length pks⌝ ∗

        "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
        "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
        "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
        "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

        "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
          (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
          (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb γ.(cfg.vrf_pk) uid prevVerLen
          lastDig hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb γ.(cfg.vrf_pk) uid
          (W64 $ length pks) lastDig bound
      end
  }}}.
Proof. Admitted.

Lemma wp_Server_Audit s γ (prevEpoch : w64) Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "Audit" #prevEpoch
  {{{
    sl_proof err σ, RET (#sl_proof, #err);
    "HQ" ∷ Q σ ∗
    "#Hgenie" ∷
      match err with
      | true =>
        "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist)⌝
      | false =>
        ∃ proof prevDig,
        "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist)⌝ ∗

        "#Hsl_proof" ∷ ktcore.AuditProofSlice1D.own sl_proof proof (□) ∗

        "%Heq_prevDig" ∷ ⌜σ.(state.hist).*1 !! (uint.nat prevEpoch) = Some prevDig⌝ ∗
        "#Hwish_digs" ∷ ktcore.wish_ListAudit prevDig proof
          (drop (S $ uint.nat prevEpoch) σ.(state.hist).*1) ∗
        "#His_sigs" ∷ ([∗ list] k ↦ aud ∈ proof,
          ∃ link,
          let ep := S $ (uint.nat prevEpoch + k)%nat in
          "#His_link" ∷ hashchain.is_chain (take (S ep) σ.(state.hist).*1)
            None link (S ep) ∗
          "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
            (W64 ep) link aud.(ktcore.AuditProof.LinkSig))
        (* no need to explicitly state update labels and vals.
        those are tied down by UpdateProof, which is tied into server's digs.
        dig only commits to one map, which lets auditor know it shares
        same maps as server. *)
      end
  }}}.
Proof. Admitted.

Lemma wp_Server_Start s γ Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "Start" #()
  {{{
    ptr_chain chain ptr_vrf vrf last_link σ, RET (#ptr_chain, #ptr_vrf);
    "HQ" ∷ Q σ ∗
    "#Hptr_chain" ∷ StartChain.own ptr_chain chain (□) ∗
    "#Hptr_vrf" ∷ StartVrf.own ptr_vrf vrf (□) ∗

    "#His_PrevLink" ∷ hashchain.is_chain
      (take (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)
      None chain.(StartChain.PrevLink)
      (uint.nat chain.(StartChain.PrevEpochLen)) ∗
    "%His_ChainProof" ∷ ⌜hashchain.wish_Proof chain.(StartChain.ChainProof)
      (drop (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)⌝ ∗
    "#His_last_link" ∷ hashchain.is_chain σ.(state.hist).*1 None
      last_link (length σ.(state.hist)) ∗
    "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
      (W64 $ length σ.(state.hist) - 1) last_link chain.(StartChain.LinkSig) ∗

    "%Heq_VrfPk" ∷ ⌜γ.(cfg.vrf_pk) = vrf.(StartVrf.VrfPk)⌝ ∗
    "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.sig_pk) γ.(cfg.vrf_pk)
      vrf.(StartVrf.VrfSig)
  }}}.
Proof. Admitted.

End proof.
End server.
