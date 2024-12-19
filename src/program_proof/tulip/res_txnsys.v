From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.base_logic Require Import ghost_map mono_nat saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import vslice fin_maps.
From Perennial.program_proof.tulip Require Import base.

(* TODO: Needed to get the ID values for actions *)
From Perennial.goose_lang.trusted.github_com.mit_pdos.tulip Require trusted_proph.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Section cmtd_hist.

    (** History generated by committed transactions for a certain key. *)

    Definition own_cmtd_hist γ (k : dbkey) (h : dbhist) : iProp Σ :=
      own γ.(cmtd_hist) {[ k := ●ML{#1} h ]}.

    Definition is_cmtd_hist_lb γ (k : dbkey) (h : dbhist) : iProp Σ :=
      own γ.(cmtd_hist) {[ k := ◯ML h ]}.

    #[global]
    Instance is_cmtd_hist_lb_persistent α key hist :
      Persistent (is_cmtd_hist_lb α key hist).
    Proof. apply _. Defined.

    Definition is_cmtd_hist_length_lb γ key n : iProp Σ :=
      ∃ lb, is_cmtd_hist_lb γ key lb ∗ ⌜(n ≤ length lb)%nat⌝.

    Lemma cmtd_hist_update {γ k h1} h2 :
      prefix h1 h2 ->
      own_cmtd_hist γ k h1 ==∗
      own_cmtd_hist γ k h2.
    Proof.
      intros Hprefix.
      iApply own_update.
      apply singleton_update.
      by apply mono_list_update.
    Qed.

    Lemma cmtd_hist_witness {γ k h} :
      own_cmtd_hist γ k h -∗
      is_cmtd_hist_lb γ k h.
    Proof.
      iApply own_mono.
      apply singleton_included_mono.
      apply mono_list_included.
    Qed.

    Lemma cmtd_hist_prefix {γ k h hlb} :
      own_cmtd_hist γ k h -∗
      is_cmtd_hist_lb γ k hlb -∗
      ⌜prefix hlb h⌝.
    Proof.
      iIntros "Hh Hlb".
      iDestruct (own_valid_2 with "Hh Hlb") as %Hvalid.
      iPureIntro. revert Hvalid.
      rewrite singleton_op singleton_valid.
      rewrite mono_list_both_dfrac_valid_L.
      by intros [_ ?].
    Qed.

  End cmtd_hist.

  Section lnrz_hist.

    (** History generated by linearized transactions for a certain key. *)

    Definition own_lnrz_hist γ (k : dbkey) (h : dbhist) : iProp Σ :=
      own γ.(lnrz_hist) {[ k := ●ML{#1} h ]}.

    Definition is_lnrz_hist_lb γ (k : dbkey) (h : dbhist) : iProp Σ :=
      own γ.(lnrz_hist) {[ k := ◯ML h ]}.

    #[global]
    Instance is_lnrz_hist_lb_persistent α key hist :
      Persistent (is_lnrz_hist_lb α key hist).
    Proof. apply _. Defined.

    Lemma lnrz_hist_update {γ k l} l' :
      prefix l l' ->
      own_lnrz_hist γ k l ==∗
      own_lnrz_hist γ k l'.
    Proof.
      intros Hprefix.
      iApply own_update.
      apply singleton_update.
      by apply mono_list_update.
    Qed.

    Lemma lnrz_hist_witness γ k l :
      own_lnrz_hist γ k l -∗
      is_lnrz_hist_lb γ k l.
    Proof.
      iApply own_mono.
      apply singleton_included_mono.
      apply mono_list_included.
    Qed.

    Lemma lnrz_hist_prefix {γ k h hlb} :
      own_lnrz_hist γ k h -∗
      is_lnrz_hist_lb γ k hlb -∗
      ⌜prefix hlb h⌝.
    Proof.
      iIntros "Hh Hlb".
      iDestruct (own_valid_2 with "Hh Hlb") as %Hvalid.
      iPureIntro. revert Hvalid.
      rewrite singleton_op singleton_valid.
      rewrite mono_list_both_dfrac_valid_L.
      by intros [_ ?].
    Qed.

    Definition is_lnrz_hist_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ :=
      ∃ lb, is_lnrz_hist_lb γ k lb ∗ ⌜lb !! ts = Some v⌝.

    Lemma lnrz_hist_lookup γ k h ts v :
      own_lnrz_hist γ k h -∗
      is_lnrz_hist_at γ k ts v -∗
      ⌜h !! ts = Some v⌝.
    Proof.
      iIntros "Hauth (%lb & #Hlb & %Hv)".
      iDestruct (lnrz_hist_prefix with "Hauth Hlb") as %Hprefix.
      iPureIntro.
      by eapply prefix_lookup_Some.
    Qed.

  End lnrz_hist.

  Section txn_res.

    (** Mapping from transaction IDs to results (i.e., committed or aborted) of
    the transactions. *)

    Definition own_txn_resm γ (resm : gmap nat txnres) : iProp Σ :=
      ghost_map_auth γ.(txn_res) 1 resm ∗
      ([∗ map] ts ↦ res ∈ resm, ghost_map_elem γ.(txn_res) ts DfracDiscarded res).

    Definition is_txn_res γ (ts : nat) (res : txnres) : iProp Σ :=
      ghost_map_elem γ.(txn_res) ts DfracDiscarded res.

    #[global]
    Instance is_txn_res_persistent γ ts res :
      Persistent (is_txn_res γ ts res).
    Proof. apply _. Defined.

    Definition is_txn_committed γ ts wrs :=
      is_txn_res γ ts (ResCommitted wrs).

    Definition is_txn_aborted γ ts :=
      is_txn_res γ ts ResAborted.

    Lemma txn_res_insert {γ resm} ts res :
      resm !! ts = None ->
      own_txn_resm γ resm ==∗
      own_txn_resm γ (<[ts := res]> resm).
    Proof.
      iIntros (Hnotin) "[Hauth Hfrags]".
      iMod (ghost_map_insert ts res with "Hauth") as "[Hauth Hfrag]".
      { apply Hnotin. }
      iMod (ghost_map_elem_persist with "Hfrag") as "#Hfrag".
      iFrame.
      iModIntro.
      by iApply (big_sepM_insert_2 with "[Hfrag] Hfrags").
    Qed.

    Lemma txn_res_witness {γ resm} ts res :
      resm !! ts = Some res ->
      own_txn_resm γ resm -∗
      is_txn_res γ ts res.
    Proof.
      iIntros (Hres) "[Hauth Hfrags]".
      by iDestruct (big_sepM_lookup with "Hfrags") as "Hfrag".
    Qed.

    Lemma txn_res_lookup γ resm ts res :
      own_txn_resm γ resm -∗
      is_txn_res γ ts res -∗
      ⌜resm !! ts = Some res⌝.
    Proof.
      iIntros "[Hauth _] Hfrag".
      iApply (ghost_map_lookup with "Hauth Hfrag").
    Qed.

  End txn_res.

  Section txn_oneshot_wrs.

    (** Transaction write-sets. This resource allows us to specify that
    [CmdPrep] is submitted to only the participant group, as encoded in
    [safe_submit]. Without which we won't be able to prove that learning a
    commit under an aborted state is impossible, as a non-participant group
    could have received [CmdPrep] and aborted. *)

    Definition own_txn_oneshot_wrsm γ (wrsm : gmap nat (option dbmap)) : iProp Σ :=
      ghost_map_auth γ.(txn_oneshot_wrs) 1 wrsm.

    Definition own_txn_oneshot_wrs γ (ts : nat) (dq : dfrac) (owrs : option dbmap) : iProp Σ :=
      ghost_map_elem γ.(txn_oneshot_wrs) ts dq owrs.

    Definition own_txn_reserved_wrs γ (ts : nat) :=
      own_txn_oneshot_wrs γ ts (DfracOwn 1) None.

    Definition is_txn_canceled_wrs γ (ts : nat) :=
      own_txn_oneshot_wrs γ ts DfracDiscarded None.

    Definition is_txn_wrs γ (ts : nat) (wrs : dbmap) :=
      own_txn_oneshot_wrs γ ts DfracDiscarded (Some wrs).

    #[global]
    Instance txn_wrs_cancel_persistent γ ts :
      Persistent (is_txn_canceled_wrs γ ts).
    Proof. apply _. Defined.

    #[global]
    Instance is_txn_wrs_persistent γ ts wrs :
      Persistent (is_txn_wrs γ ts wrs).
    Proof. apply _. Defined.

    Lemma txn_oneshot_wrs_allocate γ wrsm ts :
      wrsm !! ts = None ->
      own_txn_oneshot_wrsm γ wrsm ==∗
      own_txn_oneshot_wrsm γ (<[ts := None]> wrsm) ∗ own_txn_reserved_wrs γ ts.
    Proof.
      iIntros (Hnone) "Hauth".
      by iApply (ghost_map_insert with "Hauth").
    Qed.

    Lemma txn_oneshot_wrs_cancel γ ts :
      own_txn_reserved_wrs γ ts ==∗ is_txn_canceled_wrs γ ts.
    Proof.
      iIntros "Hfrag".
      iApply (ghost_map_elem_persist with "Hfrag").
    Qed.

    Lemma txn_oneshot_wrs_update γ wrsm ts wrs :
      own_txn_reserved_wrs γ ts -∗
      own_txn_oneshot_wrsm γ wrsm ==∗
      own_txn_oneshot_wrsm γ (<[ts := Some wrs]> wrsm) ∗ is_txn_wrs γ ts wrs.
    Proof.
      iIntros "Hfrag Hauth".
      iMod (ghost_map_update (Some wrs) with "Hauth Hfrag") as "[Hauth Hfrag]".
      iMod (ghost_map_elem_persist with "Hfrag") as "#Hfrag".
      by iFrame "∗ #".
    Qed.

    Lemma txn_oneshot_wrs_lookup γ wrsm ts dq owrs :
      own_txn_oneshot_wrs γ ts dq owrs -∗
      own_txn_oneshot_wrsm γ wrsm -∗
      ⌜wrsm !! ts = Some owrs⌝.
    Proof.
      iIntros "Hfrag Hauth".
      iApply (ghost_map_lookup with "Hauth Hfrag").
    Qed.

    Lemma txn_oneshot_wrs_agree γ ts dq1 dq2 owrs1 owrs2 :
      own_txn_oneshot_wrs γ ts dq1 owrs1 -∗
      own_txn_oneshot_wrs γ ts dq2 owrs2 -∗
      ⌜owrs2 = owrs1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      by iDestruct (ghost_map_elem_agree with "Hfrag1 Hfrag2") as %?.
    Qed.

    Lemma txn_wrs_lookup γ wrsm ts wrs :
      is_txn_wrs γ ts wrs -∗
      own_txn_oneshot_wrsm γ wrsm -∗
      ⌜wrsm !! ts = Some (Some wrs)⌝.
    Proof. iIntros "#Hwrs Hwrsm". by iApply txn_oneshot_wrs_lookup. Qed.

    Lemma txn_oneshot_wrs_elem_of γ wrsm ts :
      own_txn_reserved_wrs γ ts -∗
      own_txn_oneshot_wrsm γ wrsm -∗
      ⌜ts ∈ dom wrsm⌝.
    Proof.
      iIntros "Hwrs Hwrsm".
      iDestruct (txn_oneshot_wrs_lookup with "Hwrs Hwrsm") as %Hlookup.
      by apply elem_of_dom_2 in Hlookup.
    Qed.

    Lemma txn_wrs_agree γ ts wrs1 wrs2 :
      is_txn_wrs γ ts wrs1 -∗
      is_txn_wrs γ ts wrs2 -∗
      ⌜wrs2 = wrs1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      iDestruct (ghost_map_elem_agree with "Hfrag1 Hfrag2") as %Heq.
      by inv Heq.
    Qed.

  End txn_oneshot_wrs.

  Section lnrz_tid.

    (** Timestamps of transactions that have linearized. *)

    Definition own_lnrz_tids γ (tids : gset nat) : iProp Σ :=
      ghost_map_auth γ.(lnrz_tid) 1 (gset_to_gmap tt tids).

    Definition is_lnrz_tid γ (tid : nat) : iProp Σ :=
      ghost_map_elem γ.(lnrz_tid) tid DfracDiscarded tt.

    #[global]
    Instance is_lnrz_tid_persistent γ tid :
      Persistent (is_lnrz_tid γ tid).
    Proof. apply _. Defined.

    Lemma lnrz_tid_insert γ tids tid :
      tid ∉ tids ->
      own_lnrz_tids γ tids ==∗
      own_lnrz_tids γ ({[ tid ]} ∪ tids) ∗ is_lnrz_tid γ tid.
    Proof.
      iIntros (Hnotin) "Hauth".
      iMod (ghost_map_insert tid tt with "Hauth") as "[Hauth Hfrag]".
      { by rewrite lookup_gset_to_gmap_None. }
      rewrite -gset_to_gmap_union_singleton.
      iMod (ghost_map_elem_persist with "Hfrag") as "Hfrag".
      by iFrame.
    Qed.

    Lemma lnrz_tid_elem_of γ tids tid :
      own_lnrz_tids γ tids -∗
      is_lnrz_tid γ tid -∗
      ⌜tid ∈ tids⌝.
    Proof.
      iIntros "Hauth Hfrag".
      iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
      by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
    Qed.

  End lnrz_tid.

  Section wabt_tid.

    (** Timestamps of transactions predicted to abort. *)

    Definition own_wabt_tids γ (tids : gset nat) : iProp Σ :=
      ghost_map_auth γ.(wabt_tid) 1 (gset_to_gmap tt tids).

    Definition own_wabt_tid γ (tid : nat) : iProp Σ :=
      ghost_map_elem γ.(wabt_tid) tid (DfracOwn 1) tt.

    Lemma wabt_tid_insert {γ tids} tid :
      tid ∉ tids ->
      own_wabt_tids γ tids ==∗
      own_wabt_tids γ ({[ tid ]} ∪ tids) ∗ own_wabt_tid γ tid.
    Proof.
      iIntros (Hnotin) "Hauth".
      iMod (ghost_map_insert tid tt with "Hauth") as "[Hauth Hfrag]".
      { by rewrite lookup_gset_to_gmap_None. }
      rewrite -gset_to_gmap_union_singleton.
      by iFrame.
    Qed.

    Lemma wabt_tid_delete {γ tids} tid :
      own_wabt_tid γ tid -∗
      own_wabt_tids γ tids ==∗
      own_wabt_tids γ (tids ∖ {[ tid ]}).
    Proof.
      iIntros "Hfrag Hauth".
      iMod (ghost_map_delete with "Hauth Hfrag") as "Hauth".
      by rewrite -gset_to_gmap_difference_singleton.
    Qed.

    Lemma wabt_tid_elem_of γ tids tid :
      own_wabt_tids γ tids -∗
      own_wabt_tid γ tid -∗
      ⌜tid ∈ tids⌝.
    Proof.
      iIntros "Hauth Hfrag".
      iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
      by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
    Qed.

  End wabt_tid.

  Section cmt_tmod.

    (** Pairs of timestamp and write-set of transactions predicted to commit or
    has committed. *)

    Definition own_cmt_tmods γ (tmods : gmap nat dbmap) : iProp Σ :=
      ghost_map_auth γ.(cmt_tmod) 1 tmods.

    Definition own_cmt_tmod γ (tid : nat) (wrs : dbmap) : iProp Σ :=
       ghost_map_elem γ.(cmt_tmod) tid (DfracOwn 1) wrs.

    Lemma cmt_tmod_insert {γ tmods} tid wrs :
      tmods !! tid = None ->
      own_cmt_tmods γ tmods ==∗
      own_cmt_tmods γ (<[tid := wrs]> tmods) ∗ own_cmt_tmod γ tid wrs.
    Proof.
      iIntros (Hnotin) "Hauth".
      by iApply (ghost_map_insert with "Hauth").
    Qed.

    Lemma cmt_tmod_lookup γ tmods tid wrs :
      own_cmt_tmods γ tmods -∗
      own_cmt_tmod γ tid wrs -∗
      ⌜tmods !! tid = Some wrs⌝.
    Proof.
      iIntros "Hauth Hfrag".
      by iApply (ghost_map_lookup with "Hauth Hfrag").
    Qed.

  End cmt_tmod.

  Section excl_tid.

    (** Exclusive tokens of transaction IDs. *)

    Definition own_excl_tids γ (tids : gset nat) : iProp Σ :=
      ghost_map_auth γ.(excl_tid) 1 (gset_to_gmap tt tids).

    Definition own_excl_tid γ (tid : nat) : iProp Σ :=
      ghost_map_elem γ.(excl_tid) tid (DfracOwn 1) tt.

    Lemma excl_tid_insert γ tids tid :
      tid ∉ tids ->
      own_excl_tids γ tids ==∗
      own_excl_tids γ ({[ tid ]} ∪ tids) ∗ own_excl_tid γ tid.
    Proof.
      iIntros (Hnotin) "Hauth".
      iMod (ghost_map_insert tid tt with "Hauth") as "[Hauth Hfrag]".
      { by rewrite lookup_gset_to_gmap_None. }
      rewrite -gset_to_gmap_union_singleton.
      by iFrame.
    Qed.

    Lemma excl_tid_ne γ tid1 tid2 :
      own_excl_tid γ tid1 -∗
      own_excl_tid γ tid2 -∗
      ⌜tid2 ≠ tid1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      iApply (ghost_map_elem_ne with "Hfrag2 Hfrag1").
    Qed.

    Lemma excl_tid_not_elem_of γ tids tid :
      ([∗ set] t ∈ tids, own_excl_tid γ t) -∗
      own_excl_tid γ tid -∗
      ⌜tid ∉ tids⌝.
    Proof.
      iIntros "Htids Htid".
      destruct (decide (tid ∈ tids)) as [Hin | ?]; last done.
      iDestruct (big_sepS_elem_of with "Htids") as "Htid'"; first apply Hin.
      by iDestruct (excl_tid_ne with "Htid Htid'") as %?.
    Qed.

  End excl_tid.

  Section txn_client_token.

    (** Exclusive tokens of transaction clients used in proving freshness of
    slow-path prepare decision proposal. *)

    Definition own_txn_client_tokens γ (ctm : gmap nat (gset u64)) : iProp Σ :=
      ∃ tgs : gset (nat * u64),
        ghost_map_auth γ.(txn_client_token) 1 (gset_to_gmap tt tgs) ∧
        ⌜(∀ t g, (t, g) ∈ tgs -> ∃ gs, ctm !! t = Some gs ∧ g ∈ gs)⌝.

    Definition own_txn_client_token γ (tid : nat) (gid : u64) : iProp Σ :=
      ghost_map_elem γ.(txn_client_token) (tid, gid) (DfracOwn 1) tt.

    Lemma txn_client_token_insert {γ ctm} ts gids :
      ctm !! ts = None ->
      own_txn_client_tokens γ ctm ==∗
      own_txn_client_tokens γ (<[ts := gids]> ctm) ∗
      ([∗ set] gid ∈ gids, own_txn_client_token γ ts gid).
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (tgs) "[Hauth %Hincl]".
      set tgsx : gset (nat * u64) := set_map (λ g, (ts, g)) gids.
      iMod (ghost_map_insert_big (gset_to_gmap tt tgsx) with "Hauth") as "[Hauth Hfrags]".
      { rewrite map_disjoint_dom 2!dom_gset_to_gmap.
        intros [t g] Hin1 Hin2.
        specialize (Hincl _ _ Hin2).
        destruct Hincl as (gs & Hin & Hg).
        apply elem_of_map in Hin1 as (g' & Heq & _).
        inv Heq.
      }
      iModIntro.
      iSplitL "Hauth".
      { iExists (tgsx ∪ tgs).
        iSplit.
        { replace (_ ∪ _) with (gset_to_gmap () (tgsx ∪ tgs)); first done.
          apply map_eq.
          intros tg.
          rewrite lookup_union.
          rewrite 3!lookup_gset_to_gmap.
          destruct (decide (tg ∈ tgsx)) as [Htgin | Htgnotin].
          { rewrite option_guard_True.
            { rewrite option_guard_True; last done.
              by rewrite union_Some_l.
            }
            set_solver.
          }
          rewrite (option_guard_False (tg ∈ tgsx)); last done.
          rewrite option_union_left_id.
          destruct (decide (tg ∈ tgs)) as [Htgin' | Htgnotin'].
          { rewrite option_guard_True.
            { by rewrite option_guard_True. }
            set_solver.
          }
          { rewrite option_guard_False.
            { by rewrite option_guard_False. }
            set_solver.
          }
        }
        iPureIntro.
        intros t g Htg.
        apply elem_of_union in Htg.
        destruct Htg as [Hintgsx | Hintgs]; last first.
        { specialize (Hincl _ _ Hintgs).
          destruct Hincl as (gs & Ht & Hin).
          destruct (decide (t = ts)) as [-> | Hne]; first congruence.
          exists gs.
          by rewrite lookup_insert_ne.
        }
        subst tgsx.
        apply elem_of_map in Hintgsx as (g' & Heq & Hin).
        inv Heq.
        exists gids.
        by rewrite lookup_insert.
      }
      { by rewrite big_sepM_gset_to_gmap big_opS_set_map. }
    Qed.

    Lemma txn_client_token_excl γ ts gid :
      own_txn_client_token γ ts gid -∗
      own_txn_client_token γ ts gid -∗
      False.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      by iDestruct (ghost_map_elem_ne with "Hfrag1 Hfrag2") as %?.
    Qed.

  End txn_client_token.

  Section txn_postcond.

    (** Transaction post-conditions. Might need a [ghost_map nat gname] and a [saved_prop]? *)

    Definition own_txn_postconds γ (posts : gmap nat (dbmap -> Prop)) : iProp Σ :=
      ghost_map_auth γ.(txn_postcond) 1 posts.

    Definition is_txn_postcond γ (tid : nat) (post : dbmap -> Prop) : iProp Σ :=
      ghost_map_elem γ.(txn_postcond) tid DfracDiscarded post.

    #[global]
    Instance is_txn_postcond_persistent γ tid post :
      Persistent (is_txn_postcond γ tid post).
    Proof. apply _. Defined.

    Lemma txn_postcond_insert γ posts tid post :
      posts !! tid = None ->
      own_txn_postconds γ posts ==∗
      own_txn_postconds γ (<[tid := post]> posts) ∗ is_txn_postcond γ tid post.
    Proof.
      iIntros (Hnotin) "Hauth".
      iMod (ghost_map_insert tid post with "Hauth") as "[Hauth Hfrag]".
      { apply Hnotin. }
      iMod (ghost_map_elem_persist with "Hfrag") as "Hfrag".
      by iFrame.
    Qed.

    Lemma txn_postcond_elem_of γ posts tid post :
      own_txn_postconds γ posts -∗
      is_txn_postcond γ tid post -∗
      ⌜posts !! tid = Some post⌝.
    Proof.
      iIntros "Hauth Hfrag".
      by iApply (ghost_map_lookup with "Hauth Hfrag").
    Qed.

    Lemma txn_postcond_agree γ tid post1 post2 :
      is_txn_postcond γ tid post1 -∗
      is_txn_postcond γ tid post2 -∗
      ⌜post2 = post1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      iApply (ghost_map_elem_agree with "Hfrag2 Hfrag1").
    Qed.

  End txn_postcond.

  Section largest_ts.

    (** Largest timestamp assigned. *)

    Definition own_largest_ts γ (ts : nat) : iProp Σ :=
      mono_nat_auth_own γ.(largest_ts) (1/2) ts.

    Definition is_largest_ts_lb γ (ts : nat) : iProp Σ :=
      mono_nat_lb_own γ.(largest_ts) ts.

    #[global]
    Instance is_largest_ts_lb_persistent γ ts :
      Persistent (is_largest_ts_lb γ ts).
    Proof. apply _. Defined.

    Lemma largest_ts_le γ tslb ts :
      is_largest_ts_lb γ tslb -∗
      own_largest_ts γ ts -∗
      ⌜(tslb ≤ ts)%nat⌝.
    Proof.
      iIntros "Hlb Hauth".
      by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
    Qed.

    Lemma largest_ts_witness γ ts :
      own_largest_ts γ ts -∗
      is_largest_ts_lb γ ts.
    Proof. iApply mono_nat_lb_own_get. Qed.

    Lemma largest_ts_lb_weaken {γ ts} ts' :
      (ts' ≤ ts)%nat ->
      is_largest_ts_lb γ ts -∗
      is_largest_ts_lb γ ts'.
    Proof. iIntros (Hle) "Hlb". by iApply mono_nat_lb_own_le. Qed.

  End largest_ts.

  Section txn_proph.

    (* Needed to be able to refer to prophecies *)
    Context `{!heapGS Σ}.

    (** Prophecy variable predicting a global trace of transaction commands. *)
    (** Computes a dbmap from its representation as a GooseLang value.
        If decoding fails, returns some arbitrary nonsense value. *)

    Definition to_dbval (b : bool) (v : byte_string) :=
      if b then Some v else None.

    Definition to_dbstring (v : val) : option byte_string :=
      match v with
      | (#true, (#(LitString key), _))%V => Some key
      | (#false, (#(LitString key), _))%V => None
      | _ => None
      end.

    Definition decode_dbmap (v: val) : dbmap :=
      match map.map_val v with
      | None => ∅
      | Some (mv, _) => to_dbstring <$> mv
      end.

    (*
    Fixpoint decode_dbmap (v : val) : dbmap :=
      match v with
      | (#(LitString key), #(LitBool present), #(LitString str'), tail)%V =>
          <[key:=to_dbval present str']> (decode_dbmap tail)
      | _ => ∅
      end.
     *)

    Local Definition decode_ev_read (v : val) : option action :=
      match v with
      | (#(LitInt tid), #(LitString key))%V => Some (ActRead (uint.nat tid) key)
      | _ => None
      end.

    Local Definition decode_ev_abort (v : val) : option action :=
      match v with
      | #(LitInt tid) => Some (ActAbort (uint.nat tid))
      | _ => None
      end.

    Local Definition decode_ev_commit (v : val) : option action :=
      match v with
      | (#(LitInt tid), m)%V => Some (ActCommit (uint.nat tid) (decode_dbmap m))
      | _ => None
      end.

    Local Definition decode_action (v : val) : option action :=
     match v with
     | (#(LitInt id), data)%V =>
         if bool_decide (id = trusted_proph.ActReadId) then
           decode_ev_read data
         else if bool_decide (id = trusted_proph.ActAbortId) then
           decode_ev_abort data
         else if bool_decide (id = trusted_proph.ActCommitId) then
           decode_ev_commit data
         else
           None
     | _ => None
     end.

   Fixpoint decode_actions (pvs : list val) : list action :=
     match pvs with
     | [] => []
     | v :: pvs => option_list (decode_action v) ++ decode_actions pvs
     end.

   Definition own_txn_proph  (p : proph_id) (acs : list action) : iProp Σ :=
     ∃ (pvs : list val), ⌜decode_actions pvs = acs⌝ ∗ proph p pvs.

  End txn_proph.

  Definition own_sid (γ : tulip_names) (sid : u64) : iProp Σ :=
    own γ.(sids) ({[ sid := Excl () ]}).

  Definition gentid_init γ : iProp Σ :=
    own_largest_ts γ 0%nat ∗ ghost_map_auth γ.(gentid_reserved) 1 (∅ : gmap u64 gname).

End res.
