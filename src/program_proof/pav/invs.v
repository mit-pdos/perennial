From Perennial.program_proof Require Import grove_prelude.

From Perennial.program_proof.pav Require Import classes cryptoffi merkle rpc chain.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.base_logic.lib Require Import ghost_map.

Section shared.
Class pavG Σ :=
  {
    #[global] pavG_mono_key_maps :: mono_listG gname Σ;
    #[global] pavG_key_map_views :: ghost_mapG Σ (list w8) (list w8);
  }.
End shared.

Section global_inv.
Context `{!heapGS Σ, !pavG Σ}.
Definition global_inv γ : iProp Σ :=
  ∃ γkey_maps key_maps,
  (* γ commits to all the key_map γs, including the next key_map. *)
  "Hγmaps" ∷ mono_list_auth_own γ (1/2) γkey_maps ∗
  (* TODO: maybe change to ghost_map_auth_pers for all but last.
  this more closely matches server protocol. *)
  "Hmaps" ∷ ([∗ list] γ;m ∈ γkey_maps;key_maps, ghost_map_auth γ (1/2) m).
End global_inv.

Section serv_sigpreds.
Context `{!heapGS Σ, !pavG Σ}.

(* com_st_ty holds committed state across all epochs. *)
Record com_st_ty :=
  mk_com_st {
    γkey_maps: list gname;
    key_maps: list (gmap (list w8) (list w8));
    digs : list (list w8);
    links : list (list w8);
  }.

Definition is_com_st γ com_st : iProp Σ :=
  "#Hγmaps" ∷ mono_list_lb_own γ com_st.(γkey_maps) ∗
  "#Hmaps" ∷ ([∗ list] γ;m ∈ com_st.(γkey_maps);com_st.(key_maps),
    ghost_map_auth_pers γ m) ∗
  "#Hdigs" ∷ ([∗ list] m;d ∈ com_st.(key_maps);com_st.(digs),
    is_dig m d) ∗
  "%Hlen_links" ∷ ⌜ length com_st.(digs) = length com_st.(links) ⌝ ∗
  "#Hlinks" ∷ ([∗ list] e↦l ∈ com_st.(links),
    is_chain (take e com_st.(digs)) l).

Definition serv_sigpred_link_aux γ link_sep epoch prevLink dig com_st : iProp Σ :=
  "#His_com" ∷ is_com_st γ com_st ∗
  "#His_ln" ∷ is_link epoch prevLink dig link_sep.(servSepLink.link) ∗
  "%Hlook_ln" ∷ ⌜ com_st.(links) !! (uint.nat epoch) = Some link_sep.(servSepLink.link) ⌝.

(* serv_sigpred_link_get_all_state just fetches the state at epoch from all
the upper layers, paying special attention to the dig that's
in the link opening. *)
Lemma serv_sigpred_link_get_all_state γ link_sep epoch prevLink dig com_st :
  serv_sigpred_link_aux γ link_sep epoch prevLink dig com_st -∗
  ∃ γkey_map key_map,
  "Hγmap" ∷ mono_list_idx_own γ (uint.nat epoch) γkey_map ∗
  "Hmap" ∷ ghost_map_auth_pers γkey_map key_map ∗
  "Hdig" ∷ is_dig key_map dig.
Proof. Admitted.

(* serv_sigpred_link says that a link exists at a particular epoch of
committed state. *)
Definition serv_sigpred_link γ link_sep : iProp Σ :=
  ∃ epoch prevLink dig com_st,
  serv_sigpred_link_aux γ link_sep epoch prevLink dig com_st.

(* serv_sigpred_put says that an entry exists at a certain
(potentially uncommitted) epoch. *)
Definition serv_sigpred_put γ (put_sep : servSepPut.t) : iProp Σ :=
  ∃ γmap,
  "#Hidx_γmap" ∷ mono_list_idx_own γ (uint.nat put_sep.(servSepPut.epoch)) γmap ∗
  "#Hentry" ∷ put_sep.(servSepPut.id) ↪[γmap]□ put_sep.(servSepPut.val).

Definition serv_sigpred γ : (list w8 → iProp Σ) :=
  λ data,
    (inv nroot (global_inv γ) ∗
    ((
      ∃ link_sep,
      ⌜servSepLink.encodes data link_sep⌝ ∗
      serv_sigpred_link γ link_sep
    )%I
    ∨
    (
      ∃ put_sep,
      ⌜servSepPut.encodes data put_sep⌝ ∗
      serv_sigpred_put γ put_sep
    )%I))%I.

(* serv_sigpred_know_link says that when you know the underlying
signed data is a link, you can directly extract the link sigpred. *)
Lemma serv_sigpred_know_link γ link_sep :
  serv_sigpred γ (servSepLink.encodesF link_sep) -∗
  serv_sigpred_link γ link_sep.
Proof.
  iIntros "[_ [[% [%Henc HP]] | [% [%Henc _]]]]"; last first.
  { by opose proof (servSep_disj _ Henc). }
  by apply servSepLink.inj in Henc as ->.
Qed.

Lemma serv_sigpred_know_put γ put_sep :
  serv_sigpred γ (servSepPut.encodesF put_sep) -∗
  serv_sigpred_put γ put_sep.
Proof.
  iIntros "[_ [[% [%Henc _]] | [% [%Henc HP]]]]".
  { by opose proof* (servSep_disj Henc). }
  by apply servSepPut.inj in Henc as ->.
Qed.

Lemma prefix_take_transport {A B} {start0 start1 : list A} {end0 end1 : list B} :
  start0 `prefix_of` start1 →
  length start0 = length end0 →
  length start1 = length end1 →
  take (length start0) end0 = take (length start0) end1 →
  end0 `prefix_of` end1.
Proof.
  intros ??? Htake.
  rewrite take_ge in Htake; [|lia].
  pose proof (prefix_take end1 (length start0)) as Hpref1.
  set_solver.
Qed.

Lemma links_prefix_carry digs0 digs1 links0 links1 :
  digs0 `prefix_of` digs1 →
  length digs0 = length links0 →
  length digs1 = length links1 →
  ([∗ list] e↦l ∈ links0, is_chain (Σ:=Σ) (take e digs0) l) -∗
  ([∗ list] e↦l ∈ links1, is_chain (Σ:=Σ) (take e digs1) l) -∗
  ⌜ links0 `prefix_of` links1 ⌝.
Proof.
  iIntros (Hpref ??) "Hlinks0 Hlinks1".
  iDestruct (big_sepL_func_prefix (length digs0) with "Hlinks0 Hlinks1") as %Htake.
  { unfold Func in *. pose proof (is_chain_func (Σ:=Σ)). naive_solver eauto. }
  { lia. }
  { apply prefix_length in Hpref. lia. }
  { intros ??. destruct Hpref as [?->].
    rewrite take_app_le; [done|lia]. }
  eauto using prefix_take_transport.
Qed.

(* is_com_st_links_prefix extends the prefix_of property of γkey_maps
all the way down to the links. *)
Lemma is_com_st_links_prefix γ com_st0 com_st1 :
  is_com_st γ com_st0 -∗
  is_com_st γ com_st1 -∗
  ⌜ com_st0.(links) `prefix_of` com_st1.(links) ∨
    com_st1.(links) `prefix_of` com_st0.(links) ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (mono_list_lb_valid with "Hγmaps0 Hγmaps1") as %Hpref0.
  unshelve (iDestruct (big_sepL2_func_prefix with "Hmaps0 Hmaps1") as %Hpref1; [done|]).
  { iIntros ([??]??) "H1 H2".
    (* TODO: play around with instances for uncurry / Func to automate this. *)
    iApply (ghost_map_auth_pers_pers_agree with "[$H1] [$H2]"). }
  unshelve (iDestruct (big_sepL2_func_prefix with "Hdigs0 Hdigs1") as %Hpref2; [done|]).
  { iIntros ([??]??) "H1 H2".
    iApply (is_dig_func with "[$H1] [$H2]"). }
  destruct Hpref2 as [?|?].
  - iLeft. by iApply (links_prefix_carry with "[$Hlinks0] [$Hlinks1]").
  - iRight. by iApply (links_prefix_carry with "[$Hlinks1] [$Hlinks0]").
Qed.

End serv_sigpreds.
