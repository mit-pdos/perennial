From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

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

Module servγ.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
    (* map from uid to gname. *)
    uidγ: gmap w64 gname;
    histγ: gname;
  }.
End servγ.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
(* serverσ.hist. *)
Context `{!mono_listG (list w8 * keys_ty) Σ}.
(* each uid has a mono_list of (ver, pk). *)
Context `{!mono_listG (w64 * list w8) Σ}.

Definition pure_put σ uid pk (ver : w64) :=
  let pks := σ.(state.pending) !!! uid in
  (* drop put if not right version. *)
  if bool_decide (uint.nat ver ≠ length pks) then σ else
  set state.pending (<[uid:=pks ++ [pk]]>) σ.

(** server invariants and ghost state. *)

Implicit Types γ : servγ.t.
Implicit Types σ : state.t.

Definition serv_gs γ σ : iProp Σ :=
  "#Hpend" ∷ ([∗ map] uid ↦ pks ∈ σ.(state.pending),
    ∃ uidγ,
    "%Hlook_uidγ" ∷ ⌜γ.(servγ.uidγ) !! uid = Some uidγ⌝ ∗
    "#Hpks" ∷ ([∗ list] ver ↦ pk ∈ pks,
      ∃ i,
      (* NOTE: client owns mlist_auth for their uid.
      for adversarial uid, auth in inv. *)
      mono_list_idx_own uidγ i ((W64 ver), pk))) ∗
  (* NOTE: client remembers lb's of this. *)
  "Hhist" ∷ mono_list_auth_own γ.(servγ.histγ) 1 σ.(state.hist).

Lemma gs_put γ σ uid pk ver uidγ i :
  serv_gs γ σ -∗
  ⌜γ.(servγ.uidγ) !! uid = Some uidγ⌝ -∗
  mono_list_idx_own uidγ i (ver, pk) -∗
  serv_gs γ (pure_put σ uid pk ver).
Proof.
  iIntros "@ %Hlook_uidγ #Hmono_idx".
  iSplitR.
  - rewrite /pure_put.
    case_bool_decide; [iFrame "#"|].
    simpl.
    iApply big_sepM_insert_2; [|iFrame "#"].
    iFrame "%".
    iApply big_sepL_snoc.
    iSplit.
    2: { iExists _. iExactEq "Hmono_idx". repeat f_equal. word. }
    rewrite lookup_total_alt.
    destruct (σ.(state.pending) !! uid) eqn:Hlook;
      rewrite Hlook; simpl; [|done].
    iDestruct (big_sepM_lookup with "Hpend") as "@"; [done|].
    by simplify_eq/=.
  - rewrite /pure_put. case_bool_decide; iFrame.
Qed.

Axiom own_Server : ∀ γ σ, iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Definition serv_inv γ : iProp Σ :=
  ∃ σ,
  "Hserv" ∷ own_Server γ σ ∗
  "Hgs" ∷ serv_gs γ σ.

Definition is_Server (s : loc) γ : iProp Σ :=
  inv nroot (serv_inv γ).

#[global] Instance is_Server_pers s γ : Persistent (is_Server s γ).
Proof. apply _. Qed.

(** "low-level" specs for server methods. *)

(* RPC spec needs □ in front of atomic update. *)
Lemma wp_Server_Put s γ uid pk sl_pk ver :
  ∀ Φ,
  is_pkg_init server -∗
  is_Server s γ -∗
  sl_pk ↦*□ pk -∗
  (* writable. *)
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    (own_Server γ (pure_put σ uid pk ver) ={∅,⊤}=∗ True)) -∗
  (* fupd might be used after Put returns, so Φ goes separately. *)
  ▷ Φ #() -∗
  WP s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver {{ Φ }}.
Proof.
Admitted.

(* The RPC spec is the same, no □ bc this doesn't mutate σ. *)
(* for idiomatic spec, use GS to contradict BlameUnknown. *)
Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) :
  ∀ Φ,
  is_pkg_init server -∗
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ sl_chainProof sl_linkSig sl_hist ptr_bound (err : ktcore.Blame)
      lastDig lastKeys lastLink,
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗
    ((
      "%Herr" ∷ ⌜err = {[ ktcore.BlameUnknown ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist) ∨
        uint.nat prevVerLen > length pks⌝
    ) ∨ (
      ∃ chainProof (linkSig : list w8) hist bound,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist) ∧
        uint.nat prevVerLen ≤ length pks⌝ ∗

      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
        (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
      "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(servγ.sig_pk)
        (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
      "#Hwish_hist" ∷ ktcore.wish_ListMemb γ.(servγ.vrf_pk) uid prevVerLen
        lastDig hist ∗
      "%Heq_hist" ∷ ⌜Forall2
        (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
        (drop (uint.nat prevVerLen) pks) hist⌝ ∗
      "#Hwish_bound" ∷ ktcore.wish_NonMemb γ.(servγ.vrf_pk) uid
        (W64 $ length pks) lastDig bound
    )) -∗
    Φ #(sl_chainProof, sl_linkSig, sl_hist, ptr_bound, err))) -∗
  WP s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen {{ Φ }}.
Proof.
Admitted.

Lemma wp_Server_Audit s γ (prevEpoch : w64) :
  ∀ Φ,
  is_pkg_init server -∗
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ sl_proof (err : ktcore.Blame),
    ((
      "%Herr" ∷ ⌜err = {[ ktcore.BlameUnknown ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist)⌝
    ) ∨ (
      ∃ proof prevDig,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
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
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(servγ.sig_pk)
          (W64 ep) link aud.(ktcore.AuditProof.LinkSig))
      (* no need to explicitly state update labels and vals.
      those are tied down by UpdateProof, which is tied into server's digs.
      dig only commits to one map, which lets auditor know it shares
      same maps as server. *)
    )) -∗
    Φ #(sl_proof, err))) -∗
  WP s @ (ptrT.id server.Server.id) @ "Audit" #prevEpoch {{ Φ }}.
Proof.
Admitted.

Lemma wp_Server_Start s γ :
  ∀ Φ,
  is_pkg_init server -∗
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ ptr_reply reply last_link,
    "#Hsl_reply" ∷ StartReply.own ptr_reply reply (□) ∗

    "#His_PrevLink" ∷ hashchain.is_chain
      (take (uint.nat reply.(StartReply.PrevEpochLen)) σ.(state.hist).*1)
      None reply.(StartReply.PrevLink)
      (uint.nat reply.(StartReply.PrevEpochLen)) ∗
    "%His_ChainProof" ∷ ⌜hashchain.wish_Proof reply.(StartReply.ChainProof)
      (drop (uint.nat reply.(StartReply.PrevEpochLen)) σ.(state.hist).*1)⌝ ∗
    "#His_last_link" ∷ hashchain.is_chain σ.(state.hist).*1 None
      last_link (length σ.(state.hist)) ∗
    "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(servγ.sig_pk)
      (W64 $ length σ.(state.hist) - 1) last_link reply.(StartReply.LinkSig) ∗

    "%Heq_VrfPk" ∷ ⌜γ.(servγ.vrf_pk) = reply.(StartReply.VrfPk)⌝ ∗
    "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(servγ.sig_pk) γ.(servγ.vrf_pk)
      reply.(StartReply.VrfSig) -∗
    Φ #ptr_reply)) -∗
  WP s @ (ptrT.id server.Server.id) @ "Start" #() {{ Φ }}.
Proof.
Admitted.

(** RA-based (more client-centric) specs. *)

Lemma wp_Server_Put' s γ uid sl_pk pk ver uidγ i :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "%Hlook_uidγ" ∷ ⌜γ.(servγ.uidγ) !! uid = Some uidγ⌝ ∗
    "#Hmono_idx" ∷ mono_list_idx_own uidγ i (ver, pk)
  }}}
  s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#? @] Hpost".
  wp_apply (wp_Server_Put with "[//][//][//][][Hpost]").
  2: { by iApply "Hpost". }
  iModIntro.
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame.
  iIntros "Hserv".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); [|done].
  iModIntro.
  iFrame.
  iApply (gs_put with "Hgs [//][//]").
Qed.

End proof.
End server.
