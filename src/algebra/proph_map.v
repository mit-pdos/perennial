From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl list gmap.
From iris.base_logic.lib Require Export own proph_map.
Set Default Proof Using "Type".
Import uPred.

Lemma proph_map_name_init `{Countable P} `(pG: proph_mapPreG P V PVS) pvs ps :
  ⊢ |==> ∃ γ : gname, proph_map_ctx (pG := {| proph_map_inG := _; proph_map_name := γ|}) pvs ps.
Proof.
  iMod (own_alloc (● to_proph_map ∅)) as (γ) "Hh".
  { rewrite auth_auth_valid. exact: to_proph_map_valid. }
  iModIntro. iExists γ, ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.

Lemma proph_map_reinit `{Countable P} `(pG: proph_mapG P V PVS) pvs ps :
  ⊢ |==> ∃ γ : gname, proph_map_ctx (pG := {| proph_map_inG := _; proph_map_name := γ|}) pvs ps.
Proof.
  iMod (own_alloc (● to_proph_map ∅)) as (γ) "Hh".
  { rewrite auth_auth_valid. exact: to_proph_map_valid. }
  iModIntro. iExists γ, ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.
