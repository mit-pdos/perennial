From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
advrpc auditor core classes client cryptoffi evidence
  history logical_audit merkle rpc serde server.

Module ClientHist.
Record t :=
  mk {
    γ: gname;
    uid: w64;
    (* pks is the only difference from normal client struct. *)
    pks: list map_val_ty;
    ep_valid: w64;
    serv: Server.t;
    serv_is_good: bool;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; pks; ep_valid; serv; serv_is_good>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  "Hcli" ∷ Client.own ptr (Client.mk obj.(γ) obj.(uid) (W64 $ length obj.(pks))
    obj.(ep_valid) obj.(serv) obj.(serv_is_good)) ∗
  "#Hhist" ∷ is_hist obj.(γ) obj.(serv).(Server.vrf_pk) obj.(uid) obj.(pks) obj.(ep_valid).

End defs.
End ClientHist.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    let new_c := set ClientHist.pks (λ x, (x ++ [(ep, pk)]))
      (set ClientHist.ep_valid (λ _, word.add ep (W64 1)) c) in
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗
    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  destruct serv_is_good eqn:Heq_good.
  - wp_apply (wp_Client__Put_good with "[$Hcli $Hsl_pk //]").
   iIntros "*". iNamed 1. simpl in *.
    iApply "HΦ". iFrame. iSplit; [done|].
    rewrite Heq_err. iSplit; simpl in *.
    { rewrite length_app. simpl.
      replace (W64 (_ + _)%nat) with
        (word.add (W64 $ length pks) (W64 1)); [|word].
      iFrame. }
    iApply (hist_extend_put with "[$Hhist $His_put_post]"); word.
  - wp_apply (wp_Client__Put with "[$Hcli $Hsl_pk //]").
    iIntros "*". iNamed 1. simpl in *.
    iApply "HΦ". iFrame. iSplit; [done|].
    case_match; [iFrame "∗#"|]. iNamed "Herr".
    iSplit; simpl in *.
    { rewrite length_app. simpl.
      replace (W64 (_ + _)%nat) with
        (word.add (W64 $ length pks) (W64 1)); [|word].
      iFrame. }
    iApply (hist_extend_put with "[$Hhist $His_put_post]"); word.
Qed.

(* written in this structure to elicit the pure gs_hist,
into which the caller can transfer any is_cli_entry.
the caller can then use the sigpred invariants to translate
between different gs_hist map entries. *)
Definition logical_audit_post γcli γaudit serv_vrf_pk (bound : w64) : iProp Σ :=
  ∃ gs,
  "%Hlen_gs" ∷ ⌜ length gs = uint.nat bound ⌝ ∗
  "#Hlb_gs" ∷ mono_list_lb_own γaudit gs ∗
  "#Hinv_gs" ∷ audit_gs_inv gs ∗

  "#Hmap_transf" ∷ (□ ∀ (ep : w64) m dig uid ver val,

    ("%Hlook_adtr" ∷ ⌜ gs !! uint.nat ep = Some (m, dig) ⌝ ∗
    "#Hentry" ∷ is_cli_entry γcli serv_vrf_pk ep uid ver val)
    -∗

    (∃ label audit_val,
    "#Hvrf_out" ∷ is_vrf_out serv_vrf_pk (enc_label_pre uid ver) label ∗
    "#His_label" ∷ is_map_label serv_vrf_pk uid ver label ∗
    (* convert audit_val to MapValPre, then state opt reln connecting it to val. *)
    "%Henc_val" ∷ ⌜ option_Forall2 MapValPre.encodes val
      ((λ x, MapValPre.mk x.1 x.2) <$> audit_val) ⌝ ∗
    "%Hlook_adtr" ∷ ⌜ m !! label = audit_val ⌝)).

Lemma do_serv_audit ptr_c c :
  c.(Client.serv_is_good) = true →
  Client.own ptr_c c
  ==∗
  logical_audit_post c.(Client.γ) c.(Client.serv).(Server.γhist)
    c.(Client.serv).(Server.vrf_pk) c.(Client.next_epoch).
Proof.
  iIntros (Heq_good). iNamed 1.
  destruct (decide (uint.Z c.(Client.next_epoch) = uint.Z 0)).
  { iMod (mono_list_lb_own_nil (mono_listG0:=pavG_adtr) _) as "$".
    iModIntro. simpl.
    iSplit; [word|].
    iSplit. { rewrite /audit_gs_inv. naive_solver. }
    iModIntro. iIntros "*". by iNamed 1. }

  (* get gs from last sig. *)
  iModIntro.
  assert (∃ x, last digs = Some x) as [? Hlast_Some].
  { destruct digs. { simpl in *. word. }
    by apply last_is_Some. }
  odestruct (Hlast_digs _ Hlast_Some) as [? ->].
  rewrite last_lookup in Hlast_Some.
  replace (pred _) with
    (uint.nat (word.sub c.(Client.next_epoch) (W64 1))) in Hlast_Some; [|word].
  odestruct (Hagree_digs_sd _ _ Hlast_Some) as [? Hlook_sd].
  iDestruct (big_sepM_lookup with "His_sd") as "[% H]"; [done|].
  iNamed "H". iNamed "His_sigdig".
  rewrite Heq_good. simpl.
  iDestruct (is_sig_to_pred with "Hserv_sig_pk Hsig") as "H".
  iNamed "H".
  opose proof (PreSigDig.inj _ _ _ _ [] [] _ Henc Henc0); eauto.
  intuition. simplify_eq/=.

  (* fill in gs inv. *)
  iExists (take (uint.nat c.(Client.next_epoch)) gs).
  do 3 try iSplit.
  { apply lookup_lt_Some in Hlook_dig.
    rewrite length_take_le; [done|word]. }
  { iApply (mono_list_lb_own_le with "Hlb"). apply prefix_take. }
  { iApply (audit_gs_prefix with "Hinv_gs"). apply prefix_take. }
  iClear (Hlast_Some Hlook_sd Henc Hlook_dig Henc0) "Hsig Hinv_gs".

  (* prove transfer wand. *)
  iDestruct (mono_list_lb_own_get with "Hown_digs") as "#Hlb_digs".
  iIntros "!> *". iNamed 1. iNamed "Hentry". iFrame "Hvrf_out".
  (* learn that cli_entry uses dig that's also in adtr gs. *)
  pose proof Hlook_adtr as Hlt_ep.
  apply lookup_lt_Some in Hlt_ep.
  rewrite length_take in Hlt_ep.
  iDestruct (mono_list_lb_idx_lookup with "Hlb_digs Hlook_dig") as %Hlook_digs; [word|].
  opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd].
  iDestruct (big_sepM_lookup with "His_sd") as "H"; [done|].
  iNamed "H". iNamed "His_sigdig".
  iDestruct (is_sig_to_pred with "Hserv_sig_pk Hsig") as "H".
  iRename "Hlb" into "Hlb_adtr". iNamed "H".
  opose proof (PreSigDig.inj _ _ _ _ [] [] _ Henc Henc0); eauto.
  intuition. simplify_eq/=.
  iDestruct (mono_list_idx_own_get with "Hlb") as "Hidx"; [done|].
  iDestruct (mono_list_lb_idx_lookup with "Hlb_adtr Hidx") as %?; [word|].
  apply lookup_take_Some in Hlook_adtr as [Hlook_adtr _].
  list_simplifier.
  (* use merkle entry to learn that cli_entry in adtr's map too. *)
  iNamed "Hinv_gs".
  iDestruct (big_sepL_lookup with "His_digs") as "Hmap"; [done|].
  iNamed "Hmap".
  iDestruct (is_merkle_map_agree_entry with "His_map Hmerk_entry") as %Hlook_map.
  iPureIntro. clear -Hlower Hlook_map. simpl in *.
  Search big_sepM2 "lookup".
  opose proof (Hlower label).
  exists (m0 !! label).
  split; [|done].
  rewrite Hlook_map in H.
  naive_solver.

  2: { exists None.
    opose proof (map_Forall2_dom_L _ _ _ Hlower).
    apply not_elem_of_dom in Hlook_map.
    split; [constructor|].
    apply not_elem_of_dom. set_solver. }
  Search map_Forall2.

  - admit.
  -
  rewrite lookup_fmap in Hlook_map.
  iPureIntro. simpl in *. eexists _. split; [|done].
  naive_solver.
Qed.

Lemma logical_audit_get_msv (ep : w64) ptr_c c γaudit :
  uint.Z ep < uint.Z c.(ClientHist.ep_valid) →
  ClientHist.own ptr_c c -∗
  logical_audit_post c.(ClientHist.γ) γaudit
    c.(ClientHist.serv).(Server.vrf_pk) c.(ClientHist.ep_valid) -∗
  msv γaudit c.(ClientHist.serv).(Server.vrf_pk)
    ep c.(ClientHist.uid) (get_lat c.(ClientHist.pks) ep).
Proof.
  iIntros (Hlt_valid). iNamed 1. iClear "Hcli". iNamed 1.
  list_elem gs (uint.nat ep) as m. destruct m as [m dig].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; [done|].
  iFrame "Hidx".
  iNamed "Hhist". iSpecialize ("Hknow_eps" $! ep with "[//]").
  iNamed "Hknow_eps". iExists vals. iSplit.

  { (* get commitment from pk_commit_reln. *)
    iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
    destruct (get_lat _ _) as [[??]|] eqn:Hlat_pk,
      (last vals) as [[??]|] eqn:Hlat_commit; [|exfalso..|done];
      rewrite /get_lat last_lookup in Hlat_pk;
      rewrite last_lookup in Hlat_commit.
    + rewrite Hlen_vals in Hlat_pk.
      iDestruct (big_sepL2_lookup with "Hpk_commit_reln") as "?";
        [exact Hlat_pk|exact Hlat_commit|].
      iFrame "#".
    + apply lookup_lt_Some in Hlat_pk. apply lookup_ge_None in Hlat_commit. lia.
    + apply lookup_ge_None in Hlat_pk. apply lookup_lt_Some in Hlat_commit. lia. }
  iNamedSuffix "Hbound" "_bnd". iFrame "#".
  list_elem gs (uint.nat bound) as mbound.
  iExists _.
  iSplit; [|iClear "Hhist"; iDestruct "Hbound" as "[H|H]"; iNamed "H"].

  (* bring history into curr epoch using maps_mono. *)
  - iClear "Hbound". iApply (big_sepL_impl with "Hhist").
    iIntros (?[prior ?]) "!> %Hlook_vals #Hcli_entry".
    (* tedious: need prior ep < adtr_bound to get prior adtr map for map transf.
    get that by tracing val back to filtered hist and using hist validity. *)
    iDestruct (big_sepL2_lookup_2_some with "Hpk_commit_reln") as %[[??] Hlook_hist];
      [exact Hlook_vals|].
    iDestruct (big_sepL2_lookup with "Hpk_commit_reln") as "H";
      [exact Hlook_hist|exact Hlook_vals|].
    iNamed "H". opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup. eauto using Hlook_hist. }
    simpl in *. list_elem gs (uint.nat prior) as mprior.
    destruct mprior as [prior_ep prior_dig].
    iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
    iNamed "H". iFrame "#". iNamed "Hinv_gs".
    iPureIntro.
    apply (f_equal (fmap fst)) in Hmprior_lookup, Hm_lookup.
    rewrite -!list_lookup_fmap in Hmprior_lookup, Hm_lookup.
    simpl in *.
    opose proof (Hmono_maps _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    eapply lookup_weaken; [|done].
    clear -Henc_val.
    About enc_val.
    (* TODO: need map val encoding injectivity. *)

  (* bring None bound into curr epoch using maps_mono. *)
  - iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
    { iPureIntro. exact Hmbound_lookup. }
    iNamed "Hmap_transf". iPureIntro.
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
    by eapply lookup_weaken_None.

  (* bring Some bound into curr epoch using epochs_ok and then maps_mono. *)
  - iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
    { iPureIntro. exact Hmbound_lookup. }
    iNamed "Hmap_transf". iPureIntro.
    destruct (decide $ is_Some $ m !! label) as [[? Hlook_mkey]|]; last first.
    { by eapply eq_None_not_Some. }
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
    opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
    opose proof ((proj2 Hinv_adtr) _ _ _ _ _ Hm_lookup Hlook_mkey) as ?. word.
Admitted.

End proof.
