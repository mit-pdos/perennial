From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.Helpers Require Import gmap_algebra.
From Perennial.base_logic Require Import ghost_map mono_nat saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import misc.
From Perennial.program_proof.tulip.paxos Require Import base recovery.
From Perennial.program_proof.tulip.paxos Require Export res_network.

Section res.
  Context `{!paxos_ghostG Σ}.

  Section consensus.

    (** Elements. *)

    Definition own_log_half γ (l : ledger) : iProp Σ :=
      own γ.(consensus_log) (mono_list_auth (A:=byte_stringO) (DfracOwn (1 / 2)) l).

    Definition is_log_lb γ (l : ledger) : iProp Σ :=
      own γ.(consensus_log) (mono_list_lb (A:=byte_stringO)  l).

    Definition is_cmd_receipt γ (c : byte_string) : iProp Σ :=
      ghost_map_elem γ.(consensus_cpool) c DfracDiscarded tt.

    Definition own_cpool_half γ (vs : gset byte_string) : iProp Σ :=
      ghost_map_auth γ.(consensus_cpool) (1 / 2) (gset_to_gmap tt vs) ∗
      ([∗ set] v ∈ vs, is_cmd_receipt γ v).

    Definition own_consensus_half γ (l : ledger) (vs : gset byte_string) : iProp Σ :=
      own_log_half γ l ∗ own_cpool_half γ vs.

    Definition cpool_subsume_log (l : ledger) (vs : gset byte_string) :=
      Forall (λ v, v ∈ vs) l.

    (** Type class instances. *)

    #[global]
    Instance is_log_lb_persistent γ l :
      Persistent (is_log_lb γ l).
    Proof. apply _. Defined.

    #[global]
    Instance is_cmd_receipt_persistent γ v :
      Persistent (is_cmd_receipt γ v).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma log_update {γ} l1 l2 :
      prefix l1 l2 ->
      own_log_half γ l1 -∗
      own_log_half γ l1 ==∗
      own_log_half γ l2 ∗ own_log_half γ l2.
    Proof.
      iIntros (Hprefix) "Hlx Hly".
      iCombine "Hlx Hly" as "Hl".
      iMod (own_update with "Hl") as "Hl".
      { by apply mono_list_update. }
      iDestruct "Hl" as "[Hlx Hly]".
      by iFrame.
    Qed.

    Lemma log_agree {γ} l1 l2 :
      own_log_half γ l1 -∗
      own_log_half γ l2 -∗
      ⌜l2 = l1⌝.
    Proof.
      iIntros "Hlx Hly".
      iDestruct (own_valid_2 with "Hlx Hly") as %Hvalid.
      by apply mono_list_auth_dfrac_op_valid_L in Hvalid as [_ ->].
    Qed.

    Lemma log_witness {γ l} :
      own_log_half γ l -∗
      is_log_lb γ l.
    Proof. iApply own_mono. apply mono_list_included. Qed.

    Lemma log_prefix {γ l lb} :
      own_log_half γ l -∗
      is_log_lb γ lb -∗
      ⌜prefix lb l⌝.
    Proof.
      iIntros "Hl Hlb".
      iDestruct (own_valid_2 with "Hl Hlb") as %Hvalid.
      by apply mono_list_both_dfrac_valid_L in Hvalid as [_ ?].
    Qed.

    Lemma log_lb_prefix {γ lb1 lb2} :
      is_log_lb γ lb1 -∗
      is_log_lb γ lb2 -∗
      ⌜prefix lb1 lb2 ∨ prefix lb2 lb1⌝.
    Proof.
      iIntros "Hlb1 Hlb2".
      iDestruct (own_valid_2 with "Hlb1 Hlb2") as %Hvalid.
      by apply mono_list_lb_op_valid_1_L in Hvalid.
    Qed.

    Lemma cpool_update {γ vs1} vs2 :
      vs1 ⊆ vs2 ->
      own_cpool_half γ vs1 -∗
      own_cpool_half γ vs1 ==∗
      own_cpool_half γ vs2 ∗ own_cpool_half γ vs2.
    Proof.
      iIntros (Hincl) "[Hvsx #Hfrags] [Hvsy _]".
      set vsnew := vs2 ∖ vs1.
      iCombine "Hvsx Hvsy" as "Hvs".
      iMod (ghost_map_insert_persist_big (gset_to_gmap tt vsnew) with "Hvs") as "[Hvs #Hfragsnew]".
      { rewrite map_disjoint_dom 2!dom_gset_to_gmap. set_solver. }
      iDestruct "Hvs" as "[Hvsx Hvsy]".
      rewrite -gset_to_gmap_same_union.
      rewrite big_sepM_gset_to_gmap.
      iDestruct (big_sepS_union_2 with "Hfragsnew Hfrags") as "Hfrags'".
      rewrite difference_union_L.
      replace (vs2 ∪ vs1) with vs2 by set_solver.
      by iFrame "∗ #".
    Qed.

    Lemma cpool_agree {γ vs1} vs2 :
      own_cpool_half γ vs1 -∗
      own_cpool_half γ vs2 -∗
      ⌜vs2 = vs1⌝.
    Proof.
      iIntros "[Hvsx _] [Hvsy _]".
      iDestruct (ghost_map_auth_agree with "Hvsx Hvsy") as %Heq.
      iPureIntro.
      replace vs1 with (dom (gset_to_gmap () vs1)); last by rewrite dom_gset_to_gmap.
      replace vs2 with (dom (gset_to_gmap () vs2)); last by rewrite dom_gset_to_gmap.
      by rewrite Heq.
    Qed.

    Lemma cpool_witness {γ vs} v :
      v ∈ vs ->
      own_cpool_half γ vs -∗
      is_cmd_receipt γ v.
    Proof.
      iIntros (Hin) "[_ Hfrags]".
      by iApply (big_sepS_elem_of with "Hfrags").
    Qed.

    Lemma cpool_lookup {γ vs} v :
      is_cmd_receipt γ v -∗
      own_cpool_half γ vs -∗
      ⌜v ∈ vs⌝.
    Proof.
      iIntros "Hfrag [Hauth _]".
      iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
      by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
    Qed.

  End consensus.

  Section proposal.

    (** Elements. *)

    Definition own_proposals_name γ (names : gmap nat gname) : iProp Σ :=
      ghost_map_auth γ.(proposal) 1 names.

    Definition is_proposal_name γ (t : nat) (name : gname) : iProp Σ :=
      ghost_map_elem γ.(proposal) t DfracDiscarded name.

    Definition own_proposals γ (ps : proposals) : iProp Σ :=
      ∃ names,
        own_proposals_name γ names ∗
        ([∗ map] t ↦ name; l ∈ names; ps, own name (mono_list_auth (DfracOwn (1 / 2)) l)).

    Definition own_proposal γ (t : nat) (v : ledger) : iProp Σ :=
      ∃ name,
        is_proposal_name γ t name ∗
        own name (mono_list_auth (A:=byte_stringO) (DfracOwn (1 / 2)) v).

    Definition is_proposal_lb γ (t : nat) (v : ledger) : iProp Σ :=
      ∃ name,
        is_proposal_name γ t name ∗
        own name (mono_list_lb (A:=byte_stringO) v).

    (** Type class instances. *)

    #[global]
    Instance is_proposal_lb_persistent γ t v :
      Persistent (is_proposal_lb γ t v).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma proposal_insert {γ ps} t v :
      ps !! t = None ->
      own_proposals γ ps ==∗
      own_proposals γ (<[t := v]> ps) ∗ own_proposal γ t v.
    Proof.
      intros Hnotin.
      iIntros "Hauth".
      iDestruct "Hauth" as (names) "[Hauth Hpslm]".
      iDestruct (big_sepM2_dom with "Hpslm") as %Hdom.
      assert (Hnamest : names !! t = None).
      { by rewrite -not_elem_of_dom Hdom not_elem_of_dom. }
      iMod (own_alloc (mono_list_auth (A:=byte_stringO) (DfracOwn 1) v)) as (name) "Hl".
      { apply mono_list_auth_valid. }
      iMod (ghost_map_insert _ name with "Hauth") as "[Hauth Hfrag]".
      { apply Hnamest. }
      iMod (ghost_map_elem_persist with "Hfrag") as "Hfrag".
      iDestruct "Hl" as "[Hlx Hly]".
      iFrame.
      iModIntro.
      by iApply (big_sepM2_insert_2 with "[Hlx] Hpslm").
    Qed.

    Lemma proposal_lookup {γ ps t v} :
      own_proposal γ t v -∗
      own_proposals γ ps -∗
      ⌜ps !! t = Some v⌝.
    Proof.
      iIntros "Hfrag Hauth".
      iDestruct "Hfrag" as (name) "[Hfrag Hpsl]".
      iDestruct "Hauth" as (names) "[Hauth Hpslm]".
      iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hname.
      iDestruct (big_sepM2_dom with "Hpslm") as %Hdom.
      assert (is_Some (ps !! t)) as [v' Hv'].
      { by rewrite -elem_of_dom -Hdom elem_of_dom. }
      iDestruct (big_sepM2_lookup with "Hpslm") as "Hpsl'".
      { apply Hname. }
      { apply Hv'. }
      iDestruct (own_valid_2 with "Hpsl Hpsl'") as %Hvalid.
      by apply mono_list_auth_dfrac_op_valid_L in Hvalid as [_ <-].
    Qed.

    Lemma proposal_update {γ ps t v1} v2 :
      prefix v1 v2 ->
      own_proposal γ t v1 -∗
      own_proposals γ ps ==∗
      own_proposal γ t v2 ∗ own_proposals γ (<[t := v2]> ps).
    Proof.
      iIntros (Hprefix) "Hfrag Hauth".
      iDestruct "Hfrag" as (name) "[Hfrag Hpsl]".
      iDestruct "Hauth" as (names) "[Hauth Hpslm]".
      iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hname.
      iDestruct (big_sepM2_dom with "Hpslm") as %Hdom.
      assert (is_Some (ps !! t)) as [v' Hv'].
      { by rewrite -elem_of_dom -Hdom elem_of_dom. }
      iDestruct (big_sepM2_delete with "Hpslm") as "[Hpsl' Hpslm]".
      { apply Hname. }
      { apply Hv'. }
      iDestruct (own_valid_2 with "Hpsl Hpsl'") as %Hvalid.
      apply mono_list_auth_dfrac_op_valid_L in Hvalid as [_ <-].
      iCombine "Hpsl Hpsl'" as "Hpsl".
      iMod (own_update with "Hpsl") as "Hpsl".
      { apply mono_list_update, Hprefix. }
      iDestruct "Hpsl" as "[Hpsl Hpsl']".
      iDestruct (big_sepM2_insert_2 _ _ _ t with "[Hpsl] Hpslm") as "Hpslm".
      { iFrame "Hpsl". }
      rewrite 2!insert_delete_eq.
      iFrame.
      by rewrite insert_id.
    Qed.

    Lemma proposal_witness {γ t v} :
      own_proposal γ t v -∗
      is_proposal_lb γ t v.
    Proof.
      iIntros "Hfrag".
      iDestruct "Hfrag" as (name) "[Hfrag Hpsl]".
      iFrame.
      iApply (own_mono with "Hpsl").
      apply mono_list_included.
    Qed.

    Lemma proposals_prefix {γ ps t vlb} :
      is_proposal_lb γ t vlb -∗
      own_proposals γ ps -∗
      ∃ v, ⌜ps !! t = Some v ∧ prefix vlb v⌝.
    Proof.
      iIntros "#Hlb Hauth".
      iDestruct "Hlb" as (name) "[Hname Hpsl]".
      iDestruct "Hauth" as (names) "[Hauth Hpslm]".
      iDestruct (ghost_map_lookup with "Hauth Hname") as %Hname.
      iDestruct (big_sepM2_dom with "Hpslm") as %Hdom.
      assert (is_Some (ps !! t)) as [v' Hv'].
      { by rewrite -elem_of_dom -Hdom elem_of_dom. }
      iDestruct (big_sepM2_lookup with "Hpslm") as "Hpsl'".
      { apply Hname. }
      { apply Hv'. }
      iDestruct (own_valid_2 with "Hpsl Hpsl'") as %Hvalid.
      iPureIntro.
      rewrite cmra_comm mono_list_both_dfrac_valid_L in Hvalid.
      destruct Hvalid as [_ Hprefix].
      by eauto.
    Qed.

    Lemma proposal_prefix {γ t v vlb} :
      is_proposal_lb γ t vlb -∗
      own_proposal γ t v -∗
      ⌜prefix vlb v⌝.
    Proof.
      iIntros "#Hlb Hfrag".
      iDestruct "Hlb" as (name) "[Hname Hpsl]".
      iDestruct "Hfrag" as (name') "[Hfrag Hpsl']".
      iDestruct (ghost_map_elem_agree with "Hfrag Hname") as %->.
      iDestruct (own_valid_2 with "Hpsl Hpsl'") as %Hvalid.
      iPureIntro.
      rewrite cmra_comm mono_list_both_dfrac_valid_L in Hvalid.
      by destruct Hvalid as [_ Hprefix].
    Qed.

    Lemma proposal_lb_prefix {γ t v1 v2} :
      is_proposal_lb γ t v1 -∗
      is_proposal_lb γ t v2 -∗
      ⌜prefix v1 v2 ∨ prefix v2 v1⌝.
    Proof.
      iIntros "#Hlb Hfrag".
      iDestruct "Hlb" as (name) "[Hname Hpsl]".
      iDestruct "Hfrag" as (name') "[Hfrag Hpsl']".
      iDestruct (ghost_map_elem_agree with "Hfrag Hname") as %->.
      iDestruct (own_valid_2 with "Hpsl Hpsl'") as %Hvalid.
      iPureIntro.
      by rewrite mono_list_lb_op_valid_L in Hvalid.
    Qed.

  End proposal.

  Section base_proposal.

    (** Elements. *)

    Definition own_base_proposals γ (ps : proposals) : iProp Σ :=
      ghost_map_auth γ.(base_proposal) 1 ps.

    Definition is_base_proposal_receipt γ (t : nat) (v : ledger) : iProp Σ :=
      ghost_map_elem γ.(base_proposal) t DfracDiscarded v.

    (** Type class instances. *)

    #[global]
    Instance is_base_proposal_receipt_persistent γ t v :
      Persistent (is_base_proposal_receipt γ t v).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma base_proposal_insert {γ ps} t v :
      ps !! t = None ->
      own_base_proposals γ ps ==∗
      own_base_proposals γ (<[t := v]> ps) ∗ is_base_proposal_receipt γ t v.
    Proof.
      intros Hnotin.
      iIntros "Hauth".
      iMod (ghost_map_insert with "Hauth") as "[Hauth Hfrag]".
      { apply Hnotin. }
      iMod (ghost_map_elem_persist with "Hfrag") as "Hfrag".
      by iFrame.
    Qed.

    Lemma base_proposal_lookup {γ ps t v} :
      is_base_proposal_receipt γ t v -∗
      own_base_proposals γ ps -∗
      ⌜ps !! t = Some v⌝.
    Proof.
      iIntros "Hfrag Hauth".
      iApply (ghost_map_lookup with "Hauth Hfrag").
    Qed.

  End base_proposal.

  Section prepare_lsn.

    (** Elements. *)

    Definition own_free_prepare_lsn γ (t : nat) : iProp Σ :=
      own γ.(prepare_lsn) {[ t := (to_dfrac_agree (DfracOwn 1) O) ]}.

    Definition is_prepare_lsn γ (t : nat) (n : nat) : iProp Σ :=
      own γ.(prepare_lsn) {[ t := (to_dfrac_agree DfracDiscarded n) ]}.

    (** Type class instances. *)

    #[global]
    Instance is_prepare_lsn_persistent γ t n :
      Persistent (is_prepare_lsn γ t n).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma prepare_lsn_update {γ t} n :
      own_free_prepare_lsn γ t ==∗
      is_prepare_lsn γ t n.
    Proof.
      iApply own_update.
      apply singleton_update.
      trans (to_dfrac_agree (DfracOwn 1) n).
      { by apply cmra_update_exclusive. }
      apply dfrac_agree_persist.
    Qed.

    Lemma prepare_lsn_eq {γ t n1 n2} :
      is_prepare_lsn γ t n1 -∗
      is_prepare_lsn γ t n2 -∗
      ⌜n2 = n1⌝.
    Proof.
      iIntros "Hn1 Hn2".
      iDestruct (own_valid_2 with "Hn1 Hn2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End prepare_lsn.

  Section past_nodedecs.

    (** Elements. *)

    Definition own_past_nodedecs γ (nid : u64) (d : list nodedec) : iProp Σ :=
      own γ.(node_declist) {[ nid := ●ML d ]}.

    Definition is_past_nodedecs_lb γ (nid : u64) (d : list nodedec) : iProp Σ :=
      own γ.(node_declist) {[ nid := ◯ML d ]}.

    (** Type class instances. *)

    #[global]
    Instance is_past_nodedecs_lb_persistent γ nid d :
      Persistent (is_past_nodedecs_lb γ nid d).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma past_nodedecs_update {γ nid d1} d2 :
      prefix d1 d2 ->
      own_past_nodedecs γ nid d1 ==∗
      own_past_nodedecs γ nid d2.
    Proof.
      intros Hprefix.
      iApply own_update.
      apply singleton_update.
      by apply mono_list_update.
    Qed.

    Lemma past_nodedecs_witness γ nid d :
      own_past_nodedecs γ nid d -∗
      is_past_nodedecs_lb γ nid d.
    Proof.
      iApply own_mono.
      apply singleton_included_mono.
      apply mono_list_included.
    Qed.

    Lemma past_nodedecs_prefix γ nid dlb d :
      is_past_nodedecs_lb γ nid dlb -∗
      own_past_nodedecs γ nid d -∗
      ⌜prefix dlb d⌝.
    Proof.
      iIntros "Hlb Hh".
      iDestruct (own_valid_2 with "Hh Hlb") as %Hvalid.
      iPureIntro. revert Hvalid.
      rewrite singleton_op singleton_valid.
      rewrite mono_list_both_dfrac_valid_L.
      by intros [_ ?].
    Qed.

  End past_nodedecs.

  Section accepted_proposal.

    (** Elements. *)

    Definition own_accepted_proposals_name γ (nid : u64) (names : gmap nat gname) : iProp Σ :=
      own γ.(node_proposal) {[ nid := gmap_view_auth (DfracOwn 1) (to_agree <$> names) ]}.

    Definition is_accepted_proposal_name γ (nid : u64) (t : nat) (name : gname) : iProp Σ :=
      own γ.(node_proposal) {[ nid := gmap_view_frag t DfracDiscarded (to_agree name) ]}.

    Definition own_accepted_proposals γ (nid : u64) (ps : proposals) : iProp Σ :=
      ∃ names,
        own_accepted_proposals_name γ nid names ∗
        ([∗ map] t ↦ α; l ∈ names; ps, own α (mono_list_auth (DfracOwn (1 / 2)) l)).

    Definition own_accepted_proposal γ (nid : u64) (t : nat) (v : ledger) : iProp Σ :=
      ∃ name,
        is_accepted_proposal_name γ nid t name ∗
        own name (mono_list_auth (A:=byte_stringO) (DfracOwn (1 / 2)) v).

    Definition is_accepted_proposal_lb γ (nid : u64) (t : nat) (v : ledger) : iProp Σ :=
      ∃ name,
        is_accepted_proposal_name γ nid t name ∗ own name (mono_list_lb (A:=byte_stringO) v).

    Definition is_accepted_proposal_length_lb γ (nid : u64) (t n : nat) : iProp Σ :=
      ∃ v, is_accepted_proposal_lb γ nid t v ∗ ⌜(n ≤ length v)%nat⌝.

    (** Type class instances. *)

    #[global]
    Instance is_accepted_proposal_lb_persistent γ nid t v :
      Persistent (is_accepted_proposal_lb γ nid t v).
    Proof. apply _. Defined.

    (** Rules. *)

    Lemma accepted_proposal_insert {γ nid ps} t v :
      ps !! t = None ->
      own_accepted_proposals γ nid ps ==∗
      own_accepted_proposals γ nid (<[t := v]> ps) ∗ own_accepted_proposal γ nid t v.
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts)".
      iMod (own_alloc (mono_list_auth (A:=byte_stringO) (DfracOwn 1) v)) as (α) "Hblt".
      { apply mono_list_auth_valid. }
      iDestruct (big_sepM2_dom with "Hblts") as %Hdom.
      assert (Hgnotin : gnames !! t = None).
      { by rewrite -not_elem_of_dom Hdom not_elem_of_dom. }
      iAssert (own_accepted_proposals_name γ nid (<[t := α]> gnames) ∗
               is_accepted_proposal_name γ nid t α)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert.
        apply: gmap_view_alloc; [|done..].
        by rewrite lookup_fmap Hgnotin.
      }
      iDestruct "Hblt" as "[Hblt Hblt']".
      iFrame "∗ #".
      iModIntro.
      by iApply (big_sepM2_insert_2 with "[Hblt] Hblts").
    Qed.

    Lemma accepted_proposal_update {γ nid ps t v1} v2 :
      prefix v1 v2 ->
      own_accepted_proposal γ nid t v1 -∗
      own_accepted_proposals γ nid ps ==∗
      own_accepted_proposal γ nid t v2 ∗ own_accepted_proposals γ nid (<[t := v2]> ps).
    Proof.
      iIntros (Hprefix) "Hfrag Hauth".
      iDestruct "Hauth" as (names) "[Hauth Hls]".
      iDestruct "Hfrag" as (name) "[Hfrag Hl]".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_dom with "Hls") as %Hdom.
      assert (is_Some (ps !! t)) as [l Hl].
      { by rewrite -elem_of_dom -Hdom elem_of_dom. }
      iDestruct (big_sepM2_delete with "Hls") as "[Hlx Hls]".
      { apply Hb. }
      { apply Hl. }
      iDestruct (own_valid_2 with "Hl Hlx") as %Hvalid.
      apply mono_list_auth_dfrac_op_valid_L in Hvalid as [_ <-].
      iCombine "Hl Hlx" as "Hl".
      iMod (own_update with "Hl") as "Hl".
      { apply mono_list_update, Hprefix. }
      iDestruct "Hl" as "[Hl Hl']".
      iDestruct (big_sepM2_insert_2 _ _ _ t with "[Hl] Hls") as "Hls".
      { iFrame "Hl". }
      rewrite 2!insert_delete_eq.
      iFrame.
      by rewrite insert_id.
    Qed.

    Lemma accepted_proposal_lookup {γ nid ps t v} :
      own_accepted_proposal γ nid t v -∗
      own_accepted_proposals γ nid ps -∗
      ⌜ps !! t = Some v⌝.
    Proof.
      iIntros "Hfrag Hauth".
      iDestruct "Hauth" as (names) "[Hauth Hls]".
      iDestruct "Hfrag" as (name) "[Hfrag Hl]".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_lookup_l with "Hls") as (x) "[%Hx Hx]".
      { apply Hb. }
      iDestruct (own_valid_2 with "Hl Hx") as %Hvalid.
      by apply mono_list_auth_dfrac_op_valid_L in Hvalid as [_ <-].
    Qed.

    Lemma accepted_proposal_lb_lookup {γ nid ps t vlb} :
      is_accepted_proposal_lb γ nid t vlb -∗
      own_accepted_proposals γ nid ps -∗
      ⌜∃ v, ps !! t = Some v ∧ prefix vlb v⌝.
    Proof.
      iIntros "Hlb Hauth".
      iDestruct "Hauth" as (names) "[Hauth Hls]".
      iDestruct "Hlb" as (name) "[Hlb Hl]".
      iDestruct (own_valid_2 with "Hauth Hlb") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_lookup_l with "Hls") as (x) "[%Hx Hx]".
      { apply Hb. }
      iDestruct (own_valid_2 with "Hl Hx") as %Hvalid.
      rewrite cmra_comm in Hvalid.
      apply mono_list_both_dfrac_valid_L in Hvalid as [_ Hprefix].
      by eauto.
    Qed.

    Lemma accepted_proposal_witness {γ nid t v} :
      own_accepted_proposal γ nid t v -∗
      is_accepted_proposal_lb γ nid t v.
    Proof.
      iIntros "Hfrag".
      iDestruct "Hfrag" as (name) "[Hfrag Hl]".
      iFrame.
      iApply (own_mono with "Hl").
      apply mono_list_included.
    Qed.

    Lemma accepted_proposal_prefix {γ nid ps t vlb} :
      is_accepted_proposal_lb γ nid t vlb -∗
      own_accepted_proposals γ nid ps -∗
      ∃ v, ⌜ps !! t = Some v ∧ prefix vlb v⌝.
    Proof.
      iIntros "Hlb Hauth".
      iDestruct "Hlb" as (name) "[Hname Hlb]".
      iDestruct "Hauth" as (names) "[Hnames Hls]".
      iDestruct (own_valid_2 with "Hnames Hname") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_lookup_l with "Hls") as (x) "[%Hx Hx]".
      { apply Hb. }
      iDestruct (own_valid_2 with "Hlb Hx") as %Hvalid.
      rewrite cmra_comm in Hvalid.
      apply mono_list_both_dfrac_valid_L in Hvalid as [_ Hprefix].
      by eauto.
    Qed.

    Lemma accepted_proposal_lb_prefix {γ nid t v1 v2} :
      is_accepted_proposal_lb γ nid t v1 -∗
      is_accepted_proposal_lb γ nid t v2 -∗
      ⌜prefix v1 v2 ∨ prefix v2 v1⌝.
    Proof.
      iIntros "Hlb1 Hlb2".
      iDestruct "Hlb1" as (name1) "[Hname1 Hlb1]".
      iDestruct "Hlb2" as (name2) "[Hname2 Hlb2]".
      iDestruct (own_valid_2 with "Hname1 Hname2") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_frag_op_valid in Hvalid as [_ Hvalid].
      apply to_agree_op_inv_L in Hvalid as <-.
      iDestruct (own_valid_2 with "Hlb1 Hlb2") as %Hvalid.
      by apply mono_list_lb_op_valid_L in Hvalid.
    Qed.

    Lemma accepted_proposal_lb_weaken {γ nid t v1} v2 :
      prefix v2 v1 ->
      is_accepted_proposal_lb γ nid t v1 -∗
      is_accepted_proposal_lb γ nid t v2.
    Proof.
      iIntros (Hprefix) "Hlb".
      iDestruct "Hlb" as (name) "[Hname Hlb]".
      iFrame.
      iApply (own_mono with "Hlb").
      by apply mono_list_lb_mono.
    Qed.

    Lemma accepted_proposal_length_lb_weaken {γ nid t n1} n2 :
      (n2 ≤ n1)%nat ->
      is_accepted_proposal_length_lb γ nid t n1 -∗
      is_accepted_proposal_length_lb γ nid t n2.
    Proof. iIntros (Hlt) "(%v & Hlb & %Hlen)". iFrame. iPureIntro. lia. Qed.

    Lemma accepted_proposals_init γ nids:
      ([∗ set] nid ∈ nids, own_accepted_proposals γ nid ∅) ==∗
      ([∗ set] nid ∈ nids, own_accepted_proposals γ nid {[0%nat := []]}) ∗
      ([∗ set] nid ∈ nids, own_accepted_proposal γ nid 0 []).
    Proof.
      iIntros "Hempty".
      rewrite -big_sepS_sep.
      iApply big_sepS_bupd.
      iApply (big_sepS_mono with "Hempty").
      iIntros (nid Hin) "Hown".
      by iMod (accepted_proposal_insert 0 [] with "[$]").
    Qed.

  End accepted_proposal.

  Section current_term.

    (** Elements. *)

    Definition own_current_term_half γ (nid : u64) (t : nat) : iProp Σ :=
      own γ.(current_term) {[ nid := (to_dfrac_agree (DfracOwn (1 / 2)) t) ]}.

    (** Type class instances. *)

    (** Rules. *)

    Lemma current_term_update {γ nid t1} t2 :
      own_current_term_half γ nid t1 -∗
      own_current_term_half γ nid t1 ==∗
      own_current_term_half γ nid t2 ∗ own_current_term_half γ nid t2.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma current_term_agree {γ nid t1 t2} :
      own_current_term_half γ nid t1 -∗
      own_current_term_half γ nid t2 -∗
      ⌜t2 = t1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End current_term.

  Section ledger_term.

    (** Elements. *)

    Definition own_ledger_term_half γ (nid : u64) (t : nat) : iProp Σ :=
      own γ.(ledger_term) {[ nid := (to_dfrac_agree (DfracOwn (1 / 2)) t) ]}.

    (** Type class instances. *)

    (** Rules. *)

    Lemma ledger_term_update {γ nid t1} t2 :
      own_ledger_term_half γ nid t1 -∗
      own_ledger_term_half γ nid t1 ==∗
      own_ledger_term_half γ nid t2 ∗ own_ledger_term_half γ nid t2.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma ledger_term_agree {γ nid t1 t2} :
      own_ledger_term_half γ nid t1 -∗
      own_ledger_term_half γ nid t2 -∗
      ⌜t2 = t1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End ledger_term.

  Section committed_lsn.

    (** Elements. *)

    Definition own_committed_lsn_half γ (nid : u64) (t : nat) : iProp Σ :=
      own γ.(committed_lsn) {[ nid := (to_dfrac_agree (DfracOwn (1 / 2)) t) ]}.

    (** Type class instances. *)

    (** Rules. *)

    Lemma committed_lsn_update {γ nid t1} t2 :
      own_committed_lsn_half γ nid t1 -∗
      own_committed_lsn_half γ nid t1 ==∗
      own_committed_lsn_half γ nid t2 ∗ own_committed_lsn_half γ nid t2.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma committed_lsn_agree {γ nid t1 t2} :
      own_committed_lsn_half γ nid t1 -∗
      own_committed_lsn_half γ nid t2 -∗
      ⌜t2 = t1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End committed_lsn.

  Section node_ledger.

    (** Elements. *)

    Definition own_node_ledger_half γ (nid : u64) (v : ledger) : iProp Σ :=
      own γ.(node_ledger) {[ nid := (to_dfrac_agree (A:=ledgerO) (DfracOwn (1 / 2)) v) ]}.

    (** Type class instances. *)

    (** Rules. *)

    Lemma node_ledger_update {γ nid v1 v1'} v2 :
      own_node_ledger_half γ nid v1 -∗
      own_node_ledger_half γ nid v1' ==∗
      own_node_ledger_half γ nid v2 ∗ own_node_ledger_half γ nid v2.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma node_ledger_agree {γ nid v1 v2} :
      own_node_ledger_half γ nid v1 -∗
      own_node_ledger_half γ nid v2 -∗
      ⌜v2 = v1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End node_ledger.

End res.

Section wal.
  Context `{!paxos_ghostG Σ}.

  Definition own_node_wal_half γ (nid : u64) (wal : list pxcmd) : iProp Σ :=
      own γ.(node_wal) {[ nid := (to_dfrac_agree (A:=pxcmdlO) (DfracOwn (1 / 2)) wal) ]}.

  Lemma node_wal_update {γ nid l1 l1'} l2 :
    own_node_wal_half γ nid l1 -∗
    own_node_wal_half γ nid l1' ==∗
    own_node_wal_half γ nid l2 ∗ own_node_wal_half γ nid l2.
  Proof.
    iIntros "Hv1 Hv2".
    iCombine "Hv1 Hv2" as "Hv".
    rewrite -own_op singleton_op.
    iApply (own_update with "Hv").
    apply singleton_update.
    apply dfrac_agree_update_2.
    by rewrite dfrac_op_own Qp.half_half.
  Qed.

  Lemma node_wal_agree {γ nid l1 l2} :
    own_node_wal_half γ nid l1 -∗
    own_node_wal_half γ nid l2 -∗
    ⌜l2 = l1⌝.
  Proof.
    iIntros "Hv1 Hv2".
    iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
    rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
    by destruct Hvalid as [_ ?].
  Qed.

  Definition is_node_wal_fname γ (nid : u64) (fname : byte_string) : iProp Σ :=
      own γ.(node_wal_fname) {[ nid := (to_agree (A:=byte_stringO) fname) ]}.

  #[global]
  Instance is_node_wal_fname_persistent γ nid fname :
    Persistent (is_node_wal_fname γ nid fname).
  Proof. apply _. Defined.

  Lemma node_wal_fname_agree {γ nid fname1 fname2} :
    is_node_wal_fname γ nid fname1 -∗
    is_node_wal_fname γ nid fname2 -∗
    ⌜fname2 = fname1⌝.
  Proof.
    iIntros "Hv1 Hv2".
    iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
    rewrite singleton_op singleton_valid in Hvalid.
    by apply to_agree_op_inv_L in Hvalid.
  Qed.

End wal.

Section alloc.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_res_alloc nids fnames :
    ⊢ |==> ∃ γ, (own_log_half γ [] ∗ own_log_half γ [] ∗ own_cpool_half γ ∅ ∗ own_cpool_half γ ∅) ∗
                own_proposals γ ∅ ∗
                own_base_proposals γ ∅ ∗
                ([∗ set] t ∈ terms_all, own_free_prepare_lsn γ t) ∗
                ([∗ set] nid ∈ nids, own_past_nodedecs γ nid []) ∗
                ([∗ set] nid ∈ nids, own_accepted_proposals γ nid {[O := []]}) ∗
                ([∗ set] nid ∈ nids, own_accepted_proposal γ nid O []) ∗
                ([∗ set] nid ∈ nids, own_current_term_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_current_term_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_ledger_term_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_ledger_term_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_committed_lsn_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_committed_lsn_half γ nid O) ∗
                ([∗ set] nid ∈ nids, own_node_ledger_half γ nid []) ∗
                ([∗ set] nid ∈ nids, own_node_ledger_half γ nid []) ∗
                (* file resources *)
                ([∗ set] nid ∈ nids, own_node_wal_half γ nid []) ∗
                ([∗ set] nid ∈ nids, own_node_wal_half γ nid []) ∗
                ([∗ map] nid ↦ fname ∈ fnames, is_node_wal_fname γ nid fname) ∗
                (* network resources *)
                own_terminals γ ∅.
  Proof.
    iMod (own_alloc (mono_list_auth (DfracOwn 1) [])) as
      (γconsensus_log) "(Hconsensus_log1&Hconsensus_log2)".
    { econstructor; try econstructor; rewrite //=. }
    iMod (ghost_map_alloc_empty (K := byte_string) (V := unit)) as
      (γconsensus_cpool) "(Hconsensus_cpool1&Hconsensus_cpool2)".
    iMod (ghost_map_alloc_empty (K := nat) (V := gname)) as
      (γproposal) "Hproposals".
    iMod (ghost_map_alloc_empty (K := nat) (V := ledger)) as
      (γbase_proposal) "Hbase_proposals".

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) O) terms_all)) as
           (γprepare_lsn) "Hfree_prepare".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc (gset_to_gmap (●ML []) nids)) as
           (γnode_declist) "Hnode_declist".
    { apply gset_to_gmap_valid; apply mono_list_auth_valid. }

    iMod (own_alloc (gset_to_gmap (gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)) nids)) as
           (γnode_proposal) "Hnode_proposal".
    { apply gset_to_gmap_valid; apply gmap_view_auth_valid. }

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) O) nids)) as
           (γcurrent_term) "Hcurrent_term".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) O) nids)) as
           (γledger_term) "Hledger_term".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) O) nids)) as
           (γcommitted_lsn) "Hcommitted_lsn".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) ([] : ledgerO)) nids)) as
           (γnode_ledger) "Hnode_ledger".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc (gset_to_gmap (to_dfrac_agree (DfracOwn 1) ([] : pxcmdlO)) nids)) as
           (γnode_wal) "Hnode_wal".
    { apply gset_to_gmap_valid. rewrite //=. }

    iMod (own_alloc ((to_agree <$> fnames) : gmapR u64 (agreeR byte_stringO))) as
           (γnode_wal_fname) "Hnode_wal_fname".
    { intros k. rewrite lookup_fmap; destruct (fnames !! k) eqn:Heq; rewrite Heq //=. }

    iMod (ghost_map_alloc_empty (K := chan) (V := unit)) as
      (γtrmlm) "Htrmlm".


    set γ :=
      {| consensus_log := γconsensus_log;
         consensus_cpool := γconsensus_cpool;
         proposal := γproposal;
         base_proposal := γbase_proposal;
         prepare_lsn := γprepare_lsn;
         node_declist := γnode_declist;
         node_proposal := γnode_proposal;
         current_term := γcurrent_term;
         ledger_term := γledger_term;
         committed_lsn := γcommitted_lsn;
         node_ledger := γnode_ledger;
         node_wal := γnode_wal;
         node_wal_fname := γnode_wal_fname;
         trmlm := γtrmlm |}.

    iAssert ([∗ set] nid ∈ nids, own_accepted_proposals γ nid ∅)%I
      with "[Hnode_proposal]" as "Hnode_proposal".
    { rewrite /own_accepted_proposals.
      rewrite -big_opS_gset_to_gmap big_opS_own_1.
      iApply (big_sepS_mono with "Hnode_proposal").
      iIntros (? Hin) "H". iExists _. iFrame.
      rewrite big_sepM2_empty //.
    }

    iMod (accepted_proposals_init with "Hnode_proposal") as "(Hnode_proposal1&Hnode_proposal2)".
    iModIntro.
    iExists γ.

    iSplitL "Hconsensus_log1 Hconsensus_log2 Hconsensus_cpool1 Hconsensus_cpool2".
    { iFrame. rewrite big_sepS_empty //=. }
    iFrame "Hproposals".
    iFrame "Hbase_proposals".
    iSplitL "".
    { rewrite big_sepM2_empty //=. }
    iSplitL "Hfree_prepare".
    { rewrite -big_opS_gset_to_gmap big_opS_own_1. iExact "Hfree_prepare". }
    iSplitL "Hnode_declist".
    { rewrite -big_opS_gset_to_gmap big_opS_own_1. iExact "Hnode_declist". }
    iSplitL "Hnode_proposal1".
    { iFrame. }
    iSplitL "Hnode_proposal2".
    { iFrame. }

    iDestruct (own_gset_to_gmap_singleton_sep_half with "Hcurrent_term") as "($&$)".
    iDestruct (own_gset_to_gmap_singleton_sep_half with "Hledger_term") as "($&$)".
    iDestruct (own_gset_to_gmap_singleton_sep_half with "Hcommitted_lsn") as "($&$)".
    iDestruct (own_gset_to_gmap_singleton_sep_half with "Hnode_ledger") as "($&$)".
    iDestruct (own_gset_to_gmap_singleton_sep_half with "Hnode_wal") as "($&$)".

    iSplitL "Hnode_wal_fname".
    { rewrite -big_opM_own_1 -big_opM_fmap big_opM_singletons //. }

    rewrite /own_terminals.
    iFrame "Htrmlm". rewrite big_sepS_empty //.
  Qed.

End alloc.
