From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import client core serde.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

(* Logical history defs. *)

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

(* Logical history derived. *)

Lemma hist_extend_valid γ vrf_pk uid ep hist valid new_valid :
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
    iApply (hist_extend_valid with "Hknow_eps"). word. }
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

Lemma hist_to_msv (ep hist_ep aud_ep : w64) γcli vrf_pk uid pks γaudit :
  uint.Z ep < uint.Z hist_ep →
  uint.Z ep < uint.Z aud_ep →
  is_hist γcli vrf_pk uid pks hist_ep -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  msv γaudit vrf_pk ep uid (get_lat pks ep).
Proof.
  iIntros (Hlt_valid). iNamed 1. iClear "Hcli". iNamed 1.
  list_elem gs (uint.nat ep) as m. destruct m as [m dig].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; [done|].
  iFrame "Hidx". iClear "Hidx".
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
  destruct mbound as [mbound dbound].
  iSplit; [|iClear "Hhist"; iDestruct "Hbound" as "[H|H]"; iNamed "H"].

  (* bring history into curr epoch using mono_maps. *)
  - iClear "Hbound". iApply (big_sepL_impl with "Hhist").
    iIntros (?[prior ?]) "!> %Hlook_vals". iNamed 1.
    (* tedious: need prior ep < adtr_bound to get prior adtr map for map transf.
    get that by tracing val back to filtered hist and using hist validity. *)
    iDestruct (big_sepL2_lookup_2_some with "Hpk_commit_reln") as %[[??] Hlook_hist];
      [exact Hlook_vals|].
    iDestruct (big_sepL2_lookup with "Hpk_commit_reln") as "H";
      [exact Hlook_hist|exact Hlook_vals|].
    iNamed "H". opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup. eauto using Hlook_hist. }
    simpl in *.
    list_elem gs (uint.nat prior) as mprior.
    destruct mprior as [prior_ep prior_dig].
    iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
    iNamed "H". iFrame "#". iNamed "Hinv_gs". iPureIntro.
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
    destruct (prior_ep !! label) as [[??]|]; [|done].
    by simplify_eq/=.

  (* bring None bound into curr epoch using mono_maps. *)
  - iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
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
  - iDestruct ("Hmap_transf" with "[$Hcli_entry]") as "H"; [done|].
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
    opose proof (MapValPre.inj _ _ _ _ [] [] _ Henc H4); [done|].
    intuition. simplify_eq/=.
    destruct (mbound !! label) as [[??]|]; [|done].
    simplify_eq/=. word.
Qed.

(* Get calls. *)

Lemma get_None_to_msv ep aud_ep γcli vrf_pk uid γaudit :
  uint.Z ep < uint.Z aud_ep →
  is_get_post_None γcli vrf_pk uid ep -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  msv γaudit vrf_pk ep uid None.
Proof.
  iIntros (?) "#Hpost #Haudit". iNamed "Haudit".
  iPoseProof "Hpost" as "Hentry". iNamed "Hpost".
  list_elem gs (uint.nat ep) as m. destruct m as [m ?].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; try done.
  iFrame "#".
  iDestruct ("Hmap_transf" with "[$Hentry //]") as "H".
  iNamedSuffix "H" "0".
  iDestruct (is_vrf_out_det with "Hvrf_out Hvrf_out0") as %->.
  inv Henc_val0.
  by simplify_option_eq.
Qed.

Lemma get_Some_to_msv ep aud_ep γcli vrf_pk uid pk γaudit :
  uint.Z ep < uint.Z aud_ep →
  is_get_post_Some γcli vrf_pk uid ep pk -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  ∃ ep', msv γaudit vrf_pk ep uid (Some (ep', pk)).
Proof.
  iIntros (?) "#Hpost #Haudit". iNamed "Hpost". iNamed "Haudit".
  list_elem gs (uint.nat ep) as m. destruct m as [m ?].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; try done.
  iFrame "#".
  iExists ep', (word.add (W64 $ length hist) (W64 1)).
  repeat iSplit.
  - iIntros (??).
    list_elem hist (uint.nat ver) as a_hist.
    iDestruct (big_sepL_lookup with "Hhist") as "Hentry"; try done.
    replace (W64 (uint.nat _)) with ver by word.
    iDestruct ("Hmap_transf" with "[$Hentry //]") as "H".
    iNamed "H". iFrame "#".
    inv Henc_val. simplify_option_eq. naive_solver.
  - iDestruct ("Hmap_transf" with "[$His_lat //]") as "H".
    iNamed "H".
    replace (word.sub _ _) with (W64 $ length hist) by word.
    iFrame "#".
    iExists (_, _). iFrame "#". iSplit; try done.
    inv Henc_val. simplify_option_eq.
    destruct H0 as [??]. simpl in *.
    opose proof (MapValPre.inj _ _ _ _ [] [] _ Henc H2) as ?; try done.
    intuition. by simplify_eq/=.
  - iDestruct ("Hmap_transf" with "[$His_bound //]") as "H".
    iNamed "H". iFrame "#".
    inv Henc_val. by simplify_option_eq.
Qed.

End proof.
