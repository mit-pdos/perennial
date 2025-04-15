From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor client core.

Section hist.
(* logical history. *)
Context `{!heapGS Σ, !pavG Σ}.

Definition is_hist_ep cli_γ serv_vrf_pk (uid ep : w64)
    (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  (* msv talks about opaque map vals, so expose those here. *)
  ∃ (vals : list opaque_map_val_ty),
  "#Hpk_commit_reln" ∷
    ([∗ list] pk_val;commit_val ∈ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist;vals,
    "%Heq_ep" ∷ ⌜ pk_val.1 = commit_val.1 ⌝ ∗
    "#Hcommit" ∷ is_commit pk_val.2 commit_val.2) ∗

  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior, commit) ∈ vals,
    is_cli_entry cli_γ serv_vrf_pk prior uid ver (Some $ enc_val prior commit)) ∗

  "#Hbound" ∷ (∃ bound : w64,
    "%Hlt_valid" ∷ ⌜ uint.Z bound < uint.Z valid ⌝ ∗
    (* next ver doesn't exist in this or later map. *)
    (("%Hlt_ep" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
    "#Hentry_bound" ∷ is_cli_entry cli_γ serv_vrf_pk bound uid (W64 $ length vals) None)
    ∨
    (* next ver exists in later map. *)
    (∃ commit,
    "%Hlt_ep" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
    "#Hentry_bound" ∷ is_cli_entry cli_γ serv_vrf_pk bound uid (W64 $ length vals) (Some $ enc_val bound commit)))).

(* is_hist says a history is okay up to valid. *)
Definition is_hist cli_γ serv_vrf_pk (uid : w64)
    (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  "%Hhist_valid" ∷ ([∗ list] x ∈ hist, ⌜ uint.Z x.1 < uint.Z valid ⌝) ∗
  "#Hknow_eps" ∷ (∀ ep : w64,
    ⌜ uint.Z ep < uint.Z valid ⌝ -∗
    is_hist_ep cli_γ serv_vrf_pk uid ep hist valid).

End hist.

Section hist_derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma hist_val_extend_valid γ vrf_pk uid ep hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  is_hist_ep γ vrf_pk uid ep hist valid -∗
  is_hist_ep γ vrf_pk uid ep hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hbound". iExists vals. iFrame "#".
  iDestruct "Hbound" as "[H|H]"; iNamed "H"; word.
Qed.

Lemma hist_nil γ vrf_pk uid hist :
  is_hist γ vrf_pk uid hist (W64 0) -∗
  ⌜ hist = [] ⌝.
Proof.
  iNamed 1. destruct hist; [done|].
  ospecialize (Hhist_valid 0%nat _ _); [done|word].
Qed.

(*
Lemma hist_extend_selfmon cli_γ uid hist valid new_valid :
  uint.Z valid ≤ uint.Z (word.add new_valid (W64 1)) →
  uint.Z (word.add new_valid (W64 1)) = uint.Z new_valid + uint.Z 1 →
  ("#His_hist" ∷ is_hist cli_γ uid hist valid ∗
  "#His_selfmon_post" ∷ is_selfmon_post cli_γ uid (W64 $ length hist) new_valid) -∗
  is_hist cli_γ uid hist (word.add new_valid (W64 1)).
Proof.
  intros ??. iNamed 1. iNamed "His_hist".
  (* FIXME: word should work without this. *)
  set (word.add new_valid (W64 1)) in *. iSplit.
  { iApply big_sepL_forall. iPureIntro. simpl. intros * Hlook.
    specialize (Hhist_valid _ _ Hlook). word. }
  iIntros (ep ?). destruct (decide (uint.Z ep < uint.Z valid)).
  (* case 1: ep < valid. *)
  { iSpecialize ("Hknow_eps" $! ep with "[]"); [word|].
    iApply (hist_val_extend_valid with "Hknow_eps"). word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
    iExists []. iSplit; [|iSplit]; [naive_solver..|].
    iNamed "His_selfmon_post". iFrame "#". iSplit; [word|]. iLeft. word. }
  (* case 3: valid ≤ ep < new_valid. *)
  iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
  iNamed "Hknow_eps". iExists vals. iSplit; [|iSplit].
  - rewrite (list_filter_iff_strong
      (λ x, uint.Z x.1 ≤ uint.Z ep)
      (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
    intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
  - iFrame "#".
  - iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
    rewrite list_filter_all in Hlen_vals; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    iNamed "His_selfmon_post". rewrite Hlen_vals. iFrame "#".
    iSplit; [word|]. iLeft. word.
Qed.
*)

(* in this lemma, new_valid is inclusive bound. *)
Lemma hist_extend_put cli_γ vrf_pk uid hist valid new_valid pk :
  uint.Z valid ≤ uint.Z (word.add new_valid (W64 1)) →
  uint.Z (word.add new_valid (W64 1)) = uint.Z new_valid + uint.Z 1 →
  ("#His_hist" ∷ is_hist cli_γ vrf_pk uid hist valid ∗
  "#His_put_post" ∷ is_put_post cli_γ vrf_pk uid (W64 $ length hist) new_valid pk) -∗
  is_hist cli_γ vrf_pk uid (hist ++ [(new_valid, pk)]) (word.add new_valid (W64 1)).
Proof.
  intros ??. iNamed 1. iNamed "His_hist". iSplit.
  { iApply big_sepL_forall. iPureIntro. simpl. intros * Hlook.
    apply lookup_app_Some in Hlook as [Hlook|[_ Hlook]].
    - specialize (Hhist_valid _ _ Hlook). word.
    - apply list_lookup_singleton_Some in Hlook as [_ ?]. simplify_eq/=. word. }
  iIntros (ep ?). destruct (decide (uint.Z ep < uint.Z new_valid)).
  (* case 1: ep < new_valid. *)
  { iEval (rewrite /is_hist_ep). rewrite filter_app.
    opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
      (new_valid, pk)) as [[->_]|[_?]]. 2: { exfalso. simpl in *. word. }
    list_simplifier. destruct (decide (uint.Z ep < uint.Z valid)).
    (* case 1.1: ep < valid. *)
    { iSpecialize ("Hknow_eps" $! ep with "[]"); [word|].
      iNamed "Hknow_eps". iExists (vals). iNamed "Hbound". iFrame "#".
      iDestruct "Hbound" as "[H|H]"; iNamed "H"; word. }
    destruct (decide (valid = 0)) as [->|].
    (* case 1.2: valid = 0. *)
    { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
      iExists []. iSplit; [|iSplit]; [naive_solver..|].
      iNamed "His_put_post". iFrame "#". iSplit; [word|]. iRight. word. }
    (* case 1.3: valid ≤ ep < new_valid. *)
    { iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
      iNamed "Hknow_eps". iExists (vals). iFrame "#". iSplit.
      - rewrite (list_filter_iff_strong
          (λ x, uint.Z x.1 ≤ uint.Z ep)
          (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
        intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
      - iNamed "His_put_post". iFrame "#".
        iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
        rewrite list_filter_all in Hlen_vals; last first.
        { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook).
          simpl in *. word. }
        rewrite Hlen_vals. iFrame "#". iSplit; [word|]. iRight. word. } }
  (* case 2: ep = new_valid. *)
  iEval (rewrite /is_hist_ep). rewrite filter_app.
  opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
    (new_valid, pk)) as [[_?]|[->_]]. { exfalso. simpl in *. word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2.1: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->. iNamed "His_put_post".
    iExists [(new_valid, commit)]. iSplit; [|iSplit].
    - simpl. by iFrame "#".
    - simpl. iFrame "#".
    - iFrame "#". iSplit; [word|]. iLeft. word. }
  (* case 2.2: valid != 0. *)
  - iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
    iNamed "Hknow_eps". iNamed "His_put_post".
    iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
    iExists (vals ++ [(new_valid, commit)]).
    rewrite list_filter_all in Hlen_vals; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    rewrite Hlen_vals. iSplit; [|iSplit].
    + iApply big_sepL2_snoc. iSplit.
      * rewrite (list_filter_iff_strong
          (λ x, uint.Z x.1 ≤ uint.Z ep)
          (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
        intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
      * simpl. by iFrame "#".
    + iApply big_sepL_snoc. iFrame "#".
    + rewrite length_app. simpl.
      replace (W64 (length vals + 1)%nat) with (word.add (W64 $ length vals) (W64 1)) by word.
      iFrame "#". iSplit; [word|]. iLeft. word.
Qed.

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

(*
Lemma hist_audit_msv (ep : w64) cli_γ uid hist valid adtr_γ aud_ep :
  uint.Z ep < uint.Z valid →
  uint.Z valid ≤ uint.Z aud_ep →
  ("#His_hist" ∷ is_hist cli_γ uid hist valid ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  msv adtr_γ ep uid (get_lat hist ep).
Proof.
  intros ??. iNamed 1.
  iNamed "His_hist". iSpecialize ("Hknow_eps" $! ep with "[//]").
  iNamed "His_audit". list_elem ms (uint.nat ep) as m.
  iDestruct (mono_list_idx_own_get _ _ Hm_lookup with "Hadtr_maps") as "Hadtr_map".
  iFrame "Hadtr_map". iNamed "Hknow_eps". iExists vals. iSplit.
  { iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
    destruct (get_lat hist ep) as [[??]|] eqn:Hlat_pk, (last vals) as [[??]|]
      eqn:Hlat_commit; [|exfalso..|done];
      rewrite /get_lat last_lookup in Hlat_pk; rewrite last_lookup in Hlat_commit.
    + rewrite Hlen_vals in Hlat_pk.
      iDestruct (big_sepL2_lookup with "Hpk_commit_reln") as "?"; [exact Hlat_pk|exact Hlat_commit|].
      iFrame "#".
    + apply lookup_lt_Some in Hlat_pk. apply lookup_ge_None in Hlat_commit. lia.
    + apply lookup_ge_None in Hlat_pk. apply lookup_lt_Some in Hlat_commit. lia. }
  iNamedSuffix "Hbound" "_bnd". iFrame "#".
  list_elem ms (uint.nat bound) as mbound.
  iSplit; [|iClear "Hhist"; iDestruct "Hbound" as "[H|H]"; iNamed "H"].
  - iClear "Hbound". iApply (big_sepL_impl with "Hhist").
    iIntros (?[prior ?]) "!> %Hlook_vals". iNamed 1. iFrame "#".
    (* tedious: need prior ep < adtr_bound to get prior adtr map for map transf.
    get that by tracing val back to filtered hist and using hist validity. *)
    iDestruct (big_sepL2_lookup_2_some with "Hpk_commit_reln") as %[[??] Hlook_hist]; [exact Hlook_vals|].
    iDestruct (big_sepL2_lookup with "Hpk_commit_reln") as "H"; [exact Hlook_hist|exact Hlook_vals|].
    iNamed "H". opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup. eauto using Hlook_hist. }
    simpl in *. list_elem ms (uint.nat prior) as mprior.
    iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_prior $His_label]") as "H".
    { iPureIntro. exact Hmprior_lookup. }
    iNamed "H". iPureIntro.
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    by eapply lookup_weaken.
  - iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
    { iPureIntro. exact Hmbound_lookup. }
    iNamed "Hmap_transf". iPureIntro.
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
    by eapply lookup_weaken_None.
  - iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
    { iPureIntro. exact Hmbound_lookup. }
    iNamed "Hmap_transf". iPureIntro.
    destruct (decide $ is_Some $ m !! label) as [[? Hlook_mkey]|]; last first.
    { by eapply eq_None_not_Some. }
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
    opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
    opose proof ((proj2 Hinv_adtr) _ _ _ _ _ Hm_lookup Hlook_mkey) as ?. word.
Qed.
*)

End hist_derived.

(*
Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "#Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"]□ #obj.1 ∗
  "#Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"]□ (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist cli_γ uid sl_hist hist valid : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "#Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, is_HistEntry p o) ∗
  "#His_hist" ∷ is_hist cli_γ uid hist valid.

Lemma mk_hist cli_γ uid :
  ⊢ own_hist cli_γ uid Slice.nil [] (W64 0).
Proof.
  iEval (rewrite /own_hist). iExists [].
  iSplit. { iApply own_slice_zero. } iSplit; [|iSplit]; [naive_solver..|].
  iIntros (??). word.
Qed.

Lemma wp_put_hist cli_γ uid sl_hist hist valid ptr_e ep pk  :
  uint.Z valid ≤ uint.Z (word.add ep (W64 1)) →
  uint.Z (word.add ep (W64 1)) = uint.Z ep + uint.Z 1 →
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist valid ∗
    "#His_entry" ∷ is_HistEntry ptr_e (ep, pk) ∗
    "#His_put_post" ∷ is_put_post cli_γ uid (W64 $ length hist) ep pk
  }}}
  SliceAppend ptrT (slice_val sl_hist) #ptr_e
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist' (hist ++ [(ep, pk)]) (word.add ep (W64 1))
  }}}.
Proof.
  intros ??. iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_hist".
  wp_apply (wp_SliceAppend with "Hsl_hist"). iIntros (?) "Hsl_hist".
  iDestruct (big_sepL2_snoc with "[$Hdim0_hist $His_entry]") as "Hnew_dim0_hist".
  iDestruct (hist_extend_put with "[$His_hist $His_put_post]") as "Hnew_is_hist"; [done..|].
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_GetHist cli_γ uid sl_hist hist valid (ep : w64) :
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist valid
  }}}
  GetHist (slice_val sl_hist) #ep
  {{{
    (is_reg : bool) sl_pk pk, RET (#is_reg, slice_val sl_pk);
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist valid ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match get_lat hist ep with
        | None => is_reg = false
        | Some lat => is_reg = true ∧ pk = lat.2
        end ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". rewrite /GetHist. iNamed "Hown_hist".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_isReg) "Hptr_isReg".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_val) "Hptr_val".
  iDestruct (own_slice_small_read with "Hsl_hist") as "[Hsl_hist Hsl_restore]".
  wp_apply (wp_forSlicePrefix
    (λ donel _,
    ∃ (is_reg : bool) sl_pk pk,
    "Hptr_isReg" ∷ ptr_isReg ↦[boolT] #is_reg ∗
    "Hptr_val" ∷ ptr_val ↦[slice.T byteT] (slice_val sl_pk) ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match get_lat (take (length donel) hist) ep with
        | None => is_reg = false
        | Some lat => is_reg = true ∧ pk = lat.2
        end ⌝)%I with "[] [$Hsl_hist Hptr_isReg Hptr_val]").
  2: { iExists _, Slice.nil, []. iFrame. iSplit; [|done].
    iDestruct (own_slice_zero byteT) as "H".
    by iDestruct (own_slice_to_small with "H") as "?". }
  { clear. iIntros "* %". iIntros (Φ) "!> H HΦ". iNamed "H".
    opose proof (list_lookup_middle done todo x _ _) as Hlook_x; [done|].
    subst dim0_hist.
    iDestruct (big_sepL2_lookup_1_some with "Hdim0_hist")
      as %[[new_ep new_pk] Hlook_hist]; [exact Hlook_x|].
    iDestruct (big_sepL2_lookup with "Hdim0_hist")
      as "His_entry"; [exact Hlook_x|exact Hlook_hist|].
    iNamed "His_entry". wp_loadField. wp_if_destruct.
    - wp_store. wp_loadField. wp_store. iApply "HΦ".
      iFrame "Hsl_HistVal". iFrame "∗#". rewrite app_length. simpl.
      replace (length done + 1)%nat with (S $ length done)%nat; [|lia].
      rewrite (take_S_r _ _ _ Hlook_hist). rewrite /get_lat filter_app.
      opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
        (new_ep, new_pk)) as [[_?]|[Htmp _]]. { exfalso. simpl in *. word. }
      rewrite Htmp. clear Htmp. rewrite last_snoc. naive_solver.
    - iApply "HΦ". iFrame "Hsl_pk". iFrame "∗#". rewrite app_length. simpl.
      replace (length done + 1)%nat with (S $ length done)%nat; [|lia].
      rewrite (take_S_r _ _ _ Hlook_hist). rewrite /get_lat filter_app.
      opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
        (new_ep, new_pk)) as [[Htmp _]|[_?]]. 2: { exfalso. simpl in *. word. }
      rewrite Htmp. clear Htmp. list_simplifier. by iFrame "%". }
  iIntros "[H0 H1]". iNamed "H1". iDestruct ("Hsl_restore" with "H0") as "Hsl_hist".
  do 2 wp_load. wp_pures. iApply "HΦ". iFrame "∗#".
  iDestruct (big_sepL2_length with "Hdim0_hist") as %Htmp.
  rewrite Htmp in Heq_lat. clear Htmp.
  rewrite firstn_all in Heq_lat. naive_solver.
Qed.

End wps.
*)
