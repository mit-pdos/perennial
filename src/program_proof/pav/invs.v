From Perennial.program_proof Require Import grove_prelude.

From Perennial.program_proof.pav Require Import common cryptoffi merkle rpc.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.base_logic.lib Require Import ghost_map.

Section shared.
Class pavG Σ :=
  {
    mono_trees :> mono_listG gname Σ;
    tree_maps :> ghost_mapG Σ (list w8) (list w8);
  }.
End shared.

Section chain.
Context `{!heapGS Σ, !pavG Σ}.

(* is_link_conn removes the need to think about records or encoding when
reasoning about links. *)
Definition is_link_conn epoch prevLink dig link : iProp Σ :=
  is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink dig)) link.

Lemma is_link_conn_agree_l epoch prevLink dig link0 link1 :
  is_link_conn epoch prevLink dig link0 -∗
  is_link_conn epoch prevLink dig link1 -∗
  ⌜ link0 = link1 ⌝.
Proof.
  iIntros "Hlink0 Hlink1".
  by iDestruct (is_hash_deterministic with "Hlink0 Hlink1") as %->.
Qed.

Lemma is_link_conn_agree_r epoch0 prevLink0 dig0 epoch1 prevLink1 dig1 link :
  is_link_conn epoch0 prevLink0 dig0 link -∗
  is_link_conn epoch1 prevLink1 dig1 link -∗
  ⌜ epoch0 = epoch1 ∧ prevLink0 = prevLink1 ∧ dig0 = dig1 ⌝.
Proof.
  iIntros "Hlink0 Hlink1".
  iDestruct (is_hash_inj with "Hlink0 Hlink1") as %Heq.
  by pose proof (chainSepSome.inj _ _ Heq) as [=->].
Qed.

(* this version zips the data directly to the links,
by currying the nextLink.
not sure how hard it is to work with. *)
Fixpoint alt_binds_aux (nextLink : list w8) (data links : list (list w8)) : iProp Σ :=
  match data, links with
  | [], [] => is_hash [(W8 0)] nextLink
  | d :: data', l :: links' =>
    is_link_conn (length data') l d nextLink ∗
    alt_binds_aux l data' links'
  | _, _ => False
  end.

Definition alt_binds data links : iProp Σ :=
  match reverse links with
  | [] => False
  | l :: links' => alt_binds_aux l (reverse data) links'
  end.

(* this version just talks about the latest link.
it takes more effort to talk about all links,
but the resulting object might be easier to reason about
since it's more "local".
all digs are on one side and a link is on the other side. *)
Fixpoint is_link_aux (data : list (list w8)) (link : list w8) : iProp Σ :=
  match data with
  | [] => is_hash [(W8 0)] link
  | d :: data' =>
    ∃ prevLink,
    is_link_conn (length data') prevLink d link ∗
    is_link_aux data' prevLink
  end.

Definition is_link data link := is_link_aux (reverse data) link.

#[global]
Instance is_link_pers data link : Persistent (is_link data link).
Proof. Admitted.

Lemma is_link_agree_l data link0 link1 :
  is_link data link0 -∗ is_link data link1 -∗ ⌜ link0 = link1 ⌝.
Proof. Admitted.

Fixpoint suffixes {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l' => suffixes l' ++ [l]
  end.

Definition prefixes {A : Type} (l : list A) := reverse <$> suffixes (reverse l).

Lemma prefix_of_prefixes {A : Type} (l1 l2 : list A) :
  l1 `prefix_of` l2 →
  prefixes l1 `prefix_of` prefixes l2.
Proof. Admitted.

Definition binds (data links : list (list w8)) : iProp Σ :=
  ([∗ list] pref;link ∈ (prefixes data);links,
    is_link pref link).

End chain.

Section global_inv.
Context `{!heapGS Σ, !pavG Σ}.
Definition global_inv γ : iProp Σ :=
  ∃ γtrees trees,
  (* γ commits to all the tree γs, including the next tr. *)
  "HmonoTrees" ∷ mono_list_auth_own γ (1/2) γtrees ∗
  "Htree_views" ∷ ([∗ list] γtr; tr ∈ γtrees; trees,
    ghost_map_auth γtr (1/2) tr).
End global_inv.

Section serv_sigpreds.
Context `{!heapGS Σ, !pavG Σ}.

Record committed_state_ty :=
  mk_committed_state {
    γkey_maps: list gname;
    key_maps: list (gmap (list w8) (list w8));
    digs : list (list w8);
    links : list (list w8);
  }.

Definition is_committed_state γ s : iProp Σ :=
  mono_list_lb_own γ s.(γkey_maps) ∗
  ([∗ list] γ;m ∈ s.(γkey_maps);s.(key_maps), ghost_map_auth_pers γ m) ∗
  ([∗ list] m;d ∈ s.(key_maps);s.(digs), is_tree_dig m d) ∗
  binds s.(digs) s.(links).

(* link exists at a particular epoch of committed state. *)
Definition serv_sigpred_link γ link : iProp Σ :=
  ∃ epoch prevLink dig comm_st,
  is_committed_state γ comm_st ∗
  is_link_conn epoch prevLink dig link.(servSepLink.link) ∗
  ⌜ comm_st.(links) !! (uint.nat epoch) = Some link.(servSepLink.link) ⌝.

(* entry exists at a specific (potentially uncommitted) epoch. *)
Definition serv_sigpred_put γ (put_sep : servSepPut.t) : iProp Σ :=
  ∃ γtr,
  "#Htr_idx" ∷ mono_list_idx_own γ (uint.nat put_sep.(servSepPut.epoch)) γtr ∗
  "#Hentry" ∷ put_sep.(servSepPut.id) ↪[γtr]□ put_sep.(servSepPut.val).

Definition serv_sigpred γ : (list w8 → iProp Σ) :=
  λ data,
    (inv nroot (global_inv γ) ∗
    ((
      ∃ dataSepLink,
      ⌜servSepLink.encodes data dataSepLink⌝ ∗
      serv_sigpred_link γ dataSepLink
    )%I
    ∨
    (
      ∃ dataSepPut,
      ⌜servSepPut.encodes data dataSepPut⌝ ∗
      serv_sigpred_put γ dataSepPut
    )%I))%I.

Lemma get_serv_sigpred_link γ o :
  serv_sigpred γ (servSepLink.encodesF o) -∗
  serv_sigpred_link γ o.
Proof.
  iIntros "[_ [[% [%Henc HP]] | [% [%Henc _]]]]"; last first.
  { by opose proof (servSep_disj _ Henc). }
  by apply servSepLink.inj in Henc as ->.
Qed.

Lemma get_serv_sigpred_put γ o :
  serv_sigpred γ (servSepPut.encodesF o) -∗
  serv_sigpred_put γ o.
Proof.
  iIntros "[_ [[% [%Henc _]] | [% [%Henc HP]]]]".
  { by opose proof* (servSep_disj Henc). }
  by apply servSepPut.inj in Henc as ->.
Qed.

Lemma big_sepL2_lookup_prefix_l `{!BiAffine PROP} {A B : Type}
    (Φ : A → B → PROP) l1 l2 l1' :
  l1' `prefix_of` l1 →
  ([∗ list] x1;x2 ∈ l1;l2, Φ x1 x2) -∗
  ⌜ ∃ l2', l2' `prefix_of` l2 ∧ length l1' = length l2' ⌝.
Proof. Admitted.

Lemma big_sepL2_agree_l `{PROP : bi} {A B : Type}
    (Φ : nat → A → B → PROP) l1 l2 l3 :
  (∀ k x1 x2 x2', Φ k x1 x2 -∗ Φ k x1 x2' -∗ ⌜ x2 = x2' ⌝) -∗
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) -∗
  ([∗ list] k↦x1;x2 ∈ l1;l3, Φ k x1 x2) -∗
  ⌜ l2 = l3 ⌝.
Proof. Admitted.

(*
Lemma sep_auth_agree_l γtrees trees0 trees1 :
  ([∗ list] γtr;tr ∈ γtrees;trees0, ghost_map_auth_pers γtr tr) -∗
  ([∗ list] γtr;tr ∈ γtrees;trees1, ghost_map_auth_pers γtr tr) -∗
  ⌜trees0 = trees1⌝.
Proof.
  iIntros "Hsep0 Hsep1".
  unfold_leibniz; setoid_rewrite list_equiv_lookup; fold_leibniz.
  iDestruct (big_sepL2_length with "Hsep0") as %Hlen0.
  iDestruct (big_sepL2_length with "Hsep1") as %Hlen1.
  iIntros (i).
  destruct (decide (i < length γtrees)) as [Hbound | Hbound].
  {
    apply lookup_lt_is_Some in Hbound as [x0 Hlook0].
    iDestruct (big_sepL2_lookup_1_some with "Hsep0") as %[x1 Hlook1]; [done|].
    iDestruct (big_sepL2_lookup_1_some with "Hsep1") as %[x2 Hlook2]; [done|].
    iDestruct (big_sepL2_lookup with "Hsep0") as "Hauth0"; [done..|].
    iDestruct (big_sepL2_lookup with "Hsep1") as "Hauth1"; [done..|].
    iDestruct (ghost_map_auth_pers_pers_agree with "Hauth0 Hauth1") as %->.
    rewrite Hlook1 Hlook2.
    done.
  }
  {
    assert (trees0 !! i = None) as ->.
    { apply lookup_ge_None; lia. }
    assert (trees1 !! i = None) as ->.
    { apply lookup_ge_None; lia. }
    done.
  }
Qed.
*)

Lemma big_sepL2_prefix_carry `{PROP : bi} {A B : Type}
    (Φ : nat → A → B → PROP) l1 l2 l3 l4 :
  l1 `prefix_of` l3 ∨ l3 `prefix_of` l1 →
  (∀ k x1 x2 x2', Φ k x1 x2 -∗ Φ k x1 x2' -∗ ⌜ x2 = x2' ⌝) -∗
  ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) -∗
  ([∗ list] k↦x1;x2 ∈ l3;l4, Φ k x1 x2) -∗
  ⌜ l2 `prefix_of` l4 ∨ l4 `prefix_of` l2 ⌝.
Proof. Admitted.
(*
why is this true?
start:
l1;l2
l3;l4
l1 prefix_of l3.

prefix lookup lemma:
exists l4',
l1;l4'
l4' prefix_of l4.

agreement lemma:
l2 = l4'.

so l2 prefix_of l4.
*)
(*
  apply exists_common_prefix in Hpref as (γtrees2 & Hpref0 & Hpref1).
  iDestruct (big_sepL2_lookup_prefix_l with "Hmap_auth0") as %(trees0' & Hpref2 & Hlen0); [exact Hpref0|].
  iDestruct (big_sepL2_prefix with "Hmap_auth0") as "Hmap_auth0'"; [done..|].
  iDestruct (big_sepL2_lookup_prefix_l with "Hmap_auth1") as %(trees1' & Hpref3 & Hlen1); [exact Hpref1|].
  iDestruct (big_sepL2_prefix with "Hmap_auth1") as "Hmap_auth1'"; [done..|].
  iDestruct (big_sepL2_agree_r with "[] Hmap_auth0' Hmap_auth1'") as %<-.
  { iIntros "**". by iApply ghost_map_auth_pers_pers_agree. }
*)

(* extending the prefix_of property of γkey_maps all the way down to links. *)
Lemma serv_sigpred_link_def_prefix γ comm_st0 comm_st1 :
  is_committed_state γ comm_st0 -∗
  is_committed_state γ comm_st1 -∗
  ⌜ comm_st0.(links) `prefix_of` comm_st1.(links) ∨
    comm_st1.(links) `prefix_of` comm_st0.(links) ⌝.
Proof.
  iIntros "#HP0 #HP1".
  iDestruct "HP0" as "(Hmono_map0 & Hmap_views0 & Hmap_digs0 & Hdig_links0)".
  iDestruct "HP1" as "(Hmono_map1 & Hmap_views1 & Hmap_digs1 & Hdig_links1)".
  iDestruct (mono_list_lb_valid with "Hmono_map0 Hmono_map1") as %Hpref0.
  iClear "Hmono_map0 Hmono_map1".

  iDestruct (big_sepL2_prefix_carry with "[] Hmap_views0 Hmap_views1") as %Hpref1.
  { done. }
  { iIntros "**". by iApply ghost_map_auth_pers_pers_agree. }
  iClear "Hmap_views0 Hmap_views1".
  iDestruct (big_sepL2_prefix_carry with "[] Hmap_digs0 Hmap_digs1") as %Hpref2.
  { done. }
  { iIntros "**". by iApply is_tree_dig_agree. }
  iClear "Hmap_digs0 Hmap_digs1".

  assert (prefixes comm_st0.(digs) `prefix_of` prefixes comm_st1.(digs) ∨
    prefixes comm_st1.(digs) `prefix_of` prefixes comm_st0.(digs)) as Hpref3.
  { intuition (eauto using prefix_of_prefixes). }
  iDestruct (big_sepL2_prefix_carry with "[] Hdig_links0 Hdig_links1") as %Hpref4.
  { done. }
  { iIntros "**". by iApply is_link_agree_l. }
  done.
Qed.

End serv_sigpreds.
