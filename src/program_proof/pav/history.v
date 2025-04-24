From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor client core serde.

(* TODO: make history have just physical history lemmas.
there should be a separate file for client agreement. *)

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
    ∃ enc,
    "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk prior commit) ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk prior uid ver (Some enc)) ∗

  "#Hbound" ∷ (∃ bound : w64,
    "%Hlt_valid" ∷ ⌜ uint.Z bound < uint.Z valid ⌝ ∗
    (* next ver doesn't exist in this or later map. *)
    (("%Hlt_ep" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk bound uid (W64 $ length vals) None)
    ∨
    (* next ver exists in later map. *)
    (∃ commit enc,
    "%Hlt_ep" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
    (* bound epoch needs to be visible to apply epochs_ok from audit. *)
    "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk bound commit) ⌝ ∗
    "#Hcli_entry" ∷ is_cli_entry cli_γ serv_vrf_pk bound uid (W64 $ length vals) (Some enc)))).

(* is_hist says a history is okay up to exclusive valid. *)
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
    iApply (hist_val_extend_valid with "Hknow_eps"). word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
    iExists []. iSplit; [|iSplit]; [naive_solver..|].
    iNamed "His_selfmon_post". iFrame "#". iSplit; [word|]. iLeft. word. }
  (* case 3: valid ≤ ep < selfmon_ep. *)
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
    iNamed "His_selfmon_post". rewrite Hlen_vals. iFrame "#%".
    iSplit; [word|]. iLeft. word.
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
      iNamed "Hknow_eps". iExists (vals). iNamed "Hbound". iFrame "#".
      iDestruct "Hbound" as "[H|H]"; iNamed "H"; word. }
    destruct (decide (valid = 0)) as [->|].
    (* case 1.2: valid = 0. *)
    { iDestruct (hist_nil with "[$Hknow_eps //]") as %->.
      iExists []. iSplit; [|iSplit]; [naive_solver..|].
      iNamed "His_put_post". iFrame "#%". word. }
    (* case 1.3: valid ≤ ep < put_ep. *)
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
        rewrite Hlen_vals. iFrame "#%". word. } }
  (* case 2: ep = put_ep. *)
  iEval (rewrite /is_hist_ep). rewrite filter_app.
  opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
    (put_ep, pk)) as [[_?]|[->_]]. { exfalso. simpl in *. word. }
  destruct (decide (valid = 0)) as [->|].
  (* case 2.1: valid = 0. *)
  { iDestruct (hist_nil with "[$Hknow_eps //]") as %->. iNamed "His_put_post".
    iExists [(put_ep, commit)]. iSplit; [|iSplit].
    - simpl. by iFrame "#".
    - simpl. iFrame "#%".
    - iFrame "#". iSplit; [word|]. iLeft. word. }
  (* case 2.2: valid != 0. *)
  - iSpecialize ("Hknow_eps" $! (word.sub valid (W64 1)) with "[]"); [word|].
    iNamed "Hknow_eps". iNamed "His_put_post".
    iDestruct (big_sepL2_length with "Hpk_commit_reln") as %Hlen_vals.
    iExists (vals ++ [(put_ep, commit)]).
    rewrite list_filter_all in Hlen_vals; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    rewrite Hlen_vals. iSplit; [|iSplit].
    + iApply big_sepL2_snoc. iSplit.
      * rewrite (list_filter_iff_strong
          (λ x, uint.Z x.1 ≤ uint.Z ep)
          (λ x, uint.Z x.1 ≤ uint.Z (word.sub valid (W64 1))) hist); [iFrame "#"|].
        intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). naive_solver word.
      * simpl. by iFrame "#".
    + iApply big_sepL_snoc. iFrame "#%".
    + rewrite length_app. simpl.
      replace (W64 (length vals + 1)%nat) with (word.add (W64 $ length vals) (W64 1)) by word.
      iFrame "#". iSplit; [word|]. iLeft. word.
Qed.

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

End hist_derived.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "#Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"]□ #obj.1 ∗
  "#Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"]□ (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist sl_hist hist : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "#Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, is_HistEntry p o).

Lemma wp_put_hist sl_hist hist ptr_e ep pk  :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist ∗
    "#His_entry" ∷ is_HistEntry ptr_e (ep, pk)
  }}}
  SliceAppend ptrT (slice_val sl_hist) #ptr_e
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist sl_hist' (hist ++ [(ep, pk)])
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_hist".
  wp_apply (wp_SliceAppend with "Hsl_hist"). iIntros (?) "Hsl_hist".
  iDestruct (big_sepL2_snoc with "[$Hdim0_hist $His_entry]") as "Hnew_dim0_hist".
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_GetHist sl_hist hist (ep : w64) :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist
  }}}
  GetHist (slice_val sl_hist) #ep
  {{{
    (is_reg : bool) sl_pk pk, RET (#is_reg, slice_val sl_pk);
    "Hown_hist" ∷ own_hist sl_hist hist ∗
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
