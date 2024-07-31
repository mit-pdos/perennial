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

Section epochChain.
Context `{!heapGS Σ, !pavG Σ}.

Definition chainSepNone_hashes_to h : iProp Σ :=
  is_hash [(W8 0)] h.

Definition binds (data links : list (list w8)) : iProp Σ :=
  ∃ init,
  "%Hinit" ∷ ⌜ links !! 0 = Some init ⌝ ∗
  "#Hinit_hash" ∷ chainSepNone_hashes_to init ∗
  (* every link except init was formed by the previous link. *)
  "#Hbinds" ∷ ([∗ list] epoch ↦ d; l ∈ data; (drop 1 links),
    ∃ prevLink,
    ⌜ links !! epoch = Some prevLink ⌝ ∗
    is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink d)) l).

(* Can't state this thru stdpp Inj bc data, links related thru iProp, not pure func.
Maybe if we had a pure hash func, things would be diff. *)
Lemma binds_inj data0 data1 links0 links1 :
  binds data0 links0 -∗
  binds data1 links1 -∗
  ⌜ data0 = data1 ↔ links0 = links1 ⌝.
Proof. Admitted.
End epochChain.

Section global_inv.
Context `{!heapGS Σ, !pavG Σ}.
(* state is tied together as follows, all from one γ:
γ →[mono_list]
γtrees →[ghost_map_auth]
trees →[is_tree_dig]
digs →[binds]
links. *)
Definition global_inv γ : iProp Σ :=
  ∃ γtrees trees,
  (* γ commits to all the tree γs, including the next tr. *)
  "HmonoTrees" ∷ mono_list_auth_own γ (1/2) γtrees ∗
  "Htree_views" ∷ ([∗ list] γtr; tr ∈ γtrees; trees,
    ghost_map_auth γtr (1/2) tr).
(*
Definition global_inv γ : iProp Σ :=
  ∃ γtrees trees updates digs links,
  "HmonoTrees" ∷ mono_list_auth_own γ (1/2) γtrees ∗
  "Htree_views" ∷ ([∗ list] γtr; tr ∈ γtrees; (trees ++ [updates]),
    ghost_map_auth γtr (1/2) tr) ∗
  "#Hdigs" ∷ ([∗ list] tr; dig ∈ trees; digs, is_tree_dig tr dig) ∗
  "#Hdigs_links" ∷ binds digs links.
*)
End global_inv.

Section serv_sigpreds.
Context `{!heapGS Σ, !pavG Σ}.

Definition serv_sigpred_link γ (data : servSepLink.t) : iProp Σ :=
  ∃ (epoch : w64) (prevLink dig : list w8) γtrees trees digs links,
  "#Hbind" ∷ is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink dig)) data.(servSepLink.link) ∗
  "#HmonoIdx" ∷ mono_list_lb_own γ γtrees ∗
  "#Htree_views" ∷ ([∗ list] γtr; tr ∈ γtrees; trees,
    ghost_map_auth_pers γtr tr) ∗
  "#Hdigs" ∷ ([∗ list] tr; dig ∈ trees; digs, is_tree_dig tr dig) ∗
  "#Hdigs_links" ∷ binds digs links ∗
  "%Hlink_look" ∷ ⌜ links !! (uint.nat epoch) = Some data.(servSepLink.link) ⌝.

Definition serv_sigpred_put γ (data : servSepPut.t) : iProp Σ :=
  ∃ γtr,
  "#Htr_idx" ∷ mono_list_idx_own γ (uint.nat data.(servSepPut.epoch)) γtr ∗
  "#Hentry" ∷ data.(servSepPut.id) ↪[γtr]□ data.(servSepPut.val).

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
End serv_sigpreds.
