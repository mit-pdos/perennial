From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl gmap_view.
From Perennial.base_logic.lib Require Import ghost_map.
From Perennial.base_logic.lib Require Export own proph_map.
Set Default Proof Using "Type".
Import uPred.

Lemma proph_map_name_init `{Countable P} `(pG: proph_mapPreG P V PVS) pvs ps :
  ⊢ |==> ∃ γ : gname, proph_map_interp (pG := {| proph_map_inG := _; proph_map_name := γ|}) pvs ps.
Proof.
  iMod ghost_map_alloc_empty as (γ) "Hh".
  iModIntro. iExists γ, ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.

Lemma proph_map_reinit `{Countable P} `(pG: proph_mapG P V PVS) pvs ps :
  ⊢ |==> ∃ γ : gname, proph_map_interp (pG := {| proph_map_inG := _; proph_map_name := γ|}) pvs ps.
Proof.
  iMod ghost_map_alloc_empty as (γ) "Hh".
  iModIntro. iExists γ, ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.
