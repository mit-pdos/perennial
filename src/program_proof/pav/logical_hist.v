From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import
  client core msv serde.

(* this file presents a client's logical history of its own key
at every epoch. some details:
- since a client knows all its own plaintext keys,
  logical history can unify prior versions and the latest version,
  unlike the msv structure.
- the epochs (both history and bound epochs) are very relevant here,
  since clients combine epoch equalities with logical auditor
  invariants to derive msv map facts. *)

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_hist_ep cli_γ serv_vrf_pk (uid ep : w64)
    (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  let filt_hist := filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist in

  (* prior vers exist in prior epoch.
  use audit mono_maps to get curr epoch Some. *)
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior_ep, pk) ∈ filt_hist,
    ∃ commit enc,
    "#Hcommit" ∷ is_commit pk commit ∗
    "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk prior_ep commit) ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk prior_ep uid (W64 ver) (Some enc)) ∗

  "#Hbound" ∷ (∃ bound_ep : w64,
    "%Hlt_valid" ∷ ⌜ uint.Z bound_ep < uint.Z valid ⌝ ∗

    (* next ver doesn't exist in later epoch.
    use audit mono_maps to get curr epoch None. *)
    (("%Hlt_ep" ∷ ⌜ uint.Z ep ≤ uint.Z bound_ep ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk bound_ep uid
      (W64 $ length filt_hist) None)
    ∨

    (* next ver exists in strictly later epoch.
    use audit ok_epochs and mono_maps to get curr epoch None. *)
    (∃ commit enc,
    "%Hlt_ep" ∷ ⌜ uint.Z ep < uint.Z bound_ep ⌝ ∗
    "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk bound_ep commit) ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk bound_ep uid
      (W64 $ length filt_hist) (Some enc)))).

(* is_hist says a history is okay up to exclusive valid epoch. *)
Definition is_hist cli_γ serv_vrf_pk (uid : w64)
    (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  "%Hhist_valid" ∷ ([∗ list] x ∈ hist, ⌜ uint.Z x.1 < uint.Z valid ⌝) ∗
  "#Hknow_eps" ∷ (∀ ep : w64,
    ⌜ uint.Z ep < uint.Z valid ⌝ -∗
    is_hist_ep cli_γ serv_vrf_pk uid ep hist valid).

(* Logical history derived. *)

Lemma hist_extend_valid γ vrf_pk uid ep hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  is_hist_ep γ vrf_pk uid ep hist valid -∗
  is_hist_ep γ vrf_pk uid ep hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hbound".
  iFrame "#". word.
Qed.

Lemma hist_nil γ vrf_pk uid hist :
  is_hist γ vrf_pk uid hist (W64 0) -∗
  ⌜ hist = [] ⌝.
Proof.
  iNamed 1. destruct hist; [done|].
  ospecialize (Hhist_valid 0%nat _ _); [done|word].
Qed.

Lemma hist_extend_selfmon cli_γ vrf_pk uid hist valid selfmon_ep :
  let new_valid := word.add selfmon_ep (W64 1) in
  uint.Z valid ≤ uint.Z new_valid →
  uint.Z new_valid = uint.Z selfmon_ep + uint.Z 1 →
  ("#His_hist" ∷ is_hist cli_γ vrf_pk uid hist valid ∗
  "#His_selfmon_post" ∷ is_selfmon_post cli_γ vrf_pk uid (W64 $ length hist) selfmon_ep) -∗
  is_hist cli_γ vrf_pk uid hist new_valid.
Proof.
  simpl. intros ??. iNamed 1. iNamed "His_hist".
  iSplit.
  { iApply big_sepL_forall. iPureIntro. simpl. intros * Hlook.
    specialize (Hhist_valid _ _ Hlook). word. }
  iIntros (ep ?). destruct (decide (uint.Z ep < uint.Z valid)).
  (* case 1: ep < valid. *)
  { iSpecialize ("Hknow_eps" $! ep with "[]"); [word|].
    iApply (hist_extend_valid with "Hknow_eps"). word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
    iSplit; [naive_solver|].
    iExists selfmon_ep.
    iSplit; [word|]. iLeft. iFrame "#". word. }
  (* case 3: valid ≤ ep < selfmon_ep. *)
  iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
  iNamed "Hknow_eps". iSplit.
  - rewrite (list_filter_iff_strong
      (λ x, uint.Z x.1 ≤ uint.Z ep)
      (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
    intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
  - iClear "Hhist Hbound".
    rewrite list_filter_all; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook).
      simpl in *. word. }
    iExists selfmon_ep.
    iSplit; [word|]. iLeft. iFrame "#". word.
Qed.

Lemma hist_extend_put cli_γ vrf_pk uid hist valid put_ep pk :
  let new_valid := word.add put_ep (W64 1) in
  uint.Z valid < uint.Z new_valid →
  uint.Z new_valid = uint.Z put_ep + uint.Z 1 →
  ("#His_hist" ∷ is_hist cli_γ vrf_pk uid hist valid ∗
  "#His_put_post" ∷ is_put_post cli_γ vrf_pk uid (W64 $ length hist) put_ep pk) -∗
  is_hist cli_γ vrf_pk uid (hist ++ [(put_ep, pk)]) new_valid.
Proof.
  simpl. intros ??. iNamed 1. iNamed "His_hist". iSplit.
  { iApply big_sepL_forall. iPureIntro. simpl. intros * Hlook.
    apply lookup_app_Some in Hlook as [Hlook|[_ Hlook]].
    - specialize (Hhist_valid _ _ Hlook). word.
    - apply list_lookup_singleton_Some in Hlook as [_ ?]. simplify_eq/=. word. }
  iIntros (ep ?). destruct (decide (uint.Z ep < uint.Z put_ep)).
  (* case 1: ep < put_ep. *)
  { iEval (rewrite /is_hist_ep). rewrite filter_app.
    opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
      (put_ep, pk)) as [[->_]|[_?]]. 2: { exfalso. simpl in *. word. }
    list_simplifier. destruct (decide (uint.Z ep < uint.Z valid)).
    (* case 1.1: ep < valid. *)
    { iSpecialize ("Hknow_eps" $! ep with "[]"); [word|].
      iNamed "Hknow_eps". iNamed "Hbound". iFrame "#". word. }
    destruct (decide (valid = 0)) as [->|].
    (* case 1.2: valid = 0. *)
    { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
      iSplit; [naive_solver|].
      iNamed "His_put_post".
      iFrame "#%". word. }
    (* case 1.3: valid ≤ ep < put_ep. *)
    { iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
      iNamed "Hknow_eps". iFrame "#". iSplit.
      - rewrite (list_filter_iff_strong
          (λ x, uint.Z x.1 ≤ uint.Z ep)
          (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
        intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
      - iNamed "His_put_post". iFrame "#".
        rewrite list_filter_all; last first.
        { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook).
          simpl in *. word. }
        iFrame "#%". word. } }
  (* case 2: ep = put_ep. *)
  iEval (rewrite /is_hist_ep). rewrite filter_app.
  opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
    (put_ep, pk)) as [[_?]|[->_]]. { exfalso. simpl in *. word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2.1: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->. iNamed "His_put_post".
    simpl. iSplit.
    - by iFrame "#".
    - iFrame "%". iSplit; [word|]. iLeft. iFrame "#". word. }
  (* case 2.2: valid != 0. *)
  - iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
    iNamed "Hknow_eps". iNamed "His_put_post".
    rewrite list_filter_all; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    rewrite list_filter_all; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    iSplit.
    + iApply big_sepL_snoc. iFrame "#%".
    + rewrite length_app. simpl.
      replace (W64 (length hist + 1)%nat) with (word.add (W64 $ length hist) (W64 1)) by word.
      iFrame "#". iSplit; [word|]. iLeft. word.
Qed.

Lemma hist_to_msv (ep hist_ep aud_ep : w64) γcli vrf_pk uid pks γaudit :
  uint.Z ep < uint.Z hist_ep →
  (* need to transfer hist epochs (including bound) into auditor maps. *)
  uint.Z hist_ep <= uint.Z aud_ep →
  is_hist γcli vrf_pk uid pks hist_ep -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  msv γaudit vrf_pk ep uid (get_lat pks ep).
Proof.
  iIntros (??) "#Hhist". iNamed 1.
  list_elem gs (uint.nat ep) as m. destruct m as [m dig].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; [done|].
  iFrame "Hidx". iClear "Hidx".
  iNamed "Hhist". iSpecialize ("Hknow_eps" $! ep with "[//]").
  iNamed "Hknow_eps".

  (* both msv Some and None derive bound the same way. *)
  remember (filter _ _) as filt_hist.
  iAssert (
    ∃ label,
    "#Hlabel" ∷ is_map_label vrf_pk uid (W64 $ length filt_hist) label ∗
    "%Hlook_map" ∷ ⌜ m !! label = None ⌝)%I as "#Hmsv_bound".
  { iClear "Hhist". iNamed "Hbound".
    list_elem gs (uint.nat bound_ep) as mbound.
    destruct mbound as [mbound dbound].
    iDestruct "Hbound" as "[H|H]"; iNamed "H".

    (* bring None bound into curr epoch using mono_maps. *)
    - iDestruct ("Hmap_transf" with "[$Hcli_entry //]") as "H".
      iNamed "H". iFrame "#". iNamed "Hinv_gs". iPureIntro.
      apply (f_equal (fmap fst)) in Hmbound_lookup, Hm_lookup.
      rewrite -!list_lookup_fmap in Hmbound_lookup, Hm_lookup.
      simpl in *.
      opose proof (Hmono_maps _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      eapply lookup_weaken_None; [|done].
      inv Henc_val.
      destruct (mbound !! label); [naive_solver|done].

    (* bring Some bound into curr epoch. arg by contra:
    if had Some x at ep, by ok_epochs, x.ep <= ep.
    move x into bound_ep (with mono_maps) and use encoding inj
    to unify with existing bound entry.
    for that entry, already know that ep < x.ep. *)
    - iDestruct ("Hmap_transf" with "[$Hcli_entry //]") as "H".
      iNamed "H". iFrame "#". iNamed "Hinv_gs". iPureIntro.
      destruct (decide $ is_Some $ m !! label) as [[[??] Hlook_mkey]|].
      2: { by eapply eq_None_not_Some. }
      apply (f_equal (fmap fst)) in Hmbound_lookup, Hm_lookup.
      rewrite -!list_lookup_fmap in Hmbound_lookup, Hm_lookup.
      simpl in *.
      opose proof (Hok_epochs _ _ _ _ _ Hm_lookup Hlook_mkey) as ?.
      opose proof (Hmono_maps _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
      inv Henc_val.
      opose proof (MapValPre.inj _ _ _ _ [] [] _ Henc H6); [done|].
      intuition. simplify_eq/=.
      destruct (mbound !! label) as [[??]|]; [|done].
      simplify_eq/=. word. }
  iClear "Hbound".

  destruct (get_lat _ _) as [[lat_ep lat_pk]|] eqn:Heq_last.
  2: {
    rewrite /get_lat last_None in Heq_last.
    rewrite Heq_last in Heqfilt_hist.
    simplify_eq/=. iFrame "#". }

  rewrite /get_lat last_Some in Heq_last.
  destruct Heq_last as [hist Heq_last].
  rewrite Heq_last in Heqfilt_hist.
  iExists (W64 $ length filt_hist).
  simplify_eq/=.
  rewrite length_app. simpl.
  iRename "Hhist" into "H".
  iDestruct (big_sepL_snoc with "H") as "[Hhist Hlat]".
  iClear "H".

  iEval (rewrite /msv_Some sep_assoc).
  iSplit; [|iFrame "#"].
  iClear "Hmsv_bound".
  replace (word.sub _ _) with (W64 $ length hist) by word.
  iSplit.

  - iIntros (??) "{Hlat}".
    list_elem hist (uint.nat ver) as a_hist.
    destruct a_hist as [prior_ep pk].
    iDestruct (big_sepL_lookup with "Hhist") as "H"; [done|].
    rewrite w64_to_nat_id. iNamed "H".

    opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup.
      apply (f_equal (lookup (uint.nat ver))) in Heq_last.
      apply (lookup_app_l_Some _ [(lat_ep, lat_pk)]) in Ha_hist_lookup.
      rewrite Ha_hist_lookup in Heq_last.
      naive_solver. }
    simpl in *.
    list_elem gs (uint.nat prior_ep) as mprior.
    destruct mprior as [mprior prior_dig].

    iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
    iNamed "H". iFrame "#". iNamed "Hinv_gs". iPureIntro.
    apply (f_equal (fmap fst)) in Hmprior_lookup, Hm_lookup.
    rewrite -!list_lookup_fmap in Hmprior_lookup, Hm_lookup.
    simpl in *.
    opose proof (Hmono_maps _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    eexists. eapply lookup_weaken; [|done].
    (* is_hist_ep had encoding of relevant commit.
    map transfer lemma over bytes, but gives back an encoding.
    need to unify the encodings, to prove that the commit still there
    in latest ep. *)
    subst. clear -Henc Henc_val.
    inv Henc_val.
    opose proof (MapValPre.inj _ _ _ _ [] [] _ Henc H6); [done|].
    intuition. simplify_eq/=.
    destruct (mprior !! label) as [[??]|]; [|done].
    by simplify_eq/=.

  - iNamed "Hlat".
    opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup.
      apply (f_equal last) in Heq_last.
      rewrite last_snoc last_lookup in Heq_last.
      naive_solver. }
    simpl in *.
    list_elem gs (uint.nat lat_ep) as mprior.
    destruct mprior as [mprior prior_dig].

    iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
    iNamed "H". iFrame "#".
    iExists (_, _). iFrame "#". iSplit; [done|].
    iNamed "Hinv_gs". iPureIntro.
    apply (f_equal (fmap fst)) in Hmprior_lookup, Hm_lookup.
    rewrite -!list_lookup_fmap in Hmprior_lookup, Hm_lookup.
    simpl in *.
    opose proof (Hmono_maps _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    eapply lookup_weaken; [|done].
    (* is_hist_ep had encoding of relevant commit.
    map transfer lemma over bytes, but gives back an encoding.
    need to unify the encodings, to prove that the commit still there
    in latest ep. *)
    subst. clear -Henc Henc_val.
    inv Henc_val.
    opose proof (MapValPre.inj _ _ _ _ [] [] _ Henc H1); [done|].
    intuition. simplify_eq/=.
    destruct (mprior !! label) as [[??]|]; [|done].
    by simplify_eq/=.
Qed.

End proof.
