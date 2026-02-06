From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From Perennial.algebra Require Import auth_set.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.algebra Require Export ghost_var.

Class chan_idiomG Σ V := ChanIdiomG {
    chan_idiom_chanG :: chanG Σ V;
    chan_idiom_ghost_mapG :: ghost_mapG Σ nat gname;
    (* already in chanG *)
    chan_idiom_savedPropG :: savedPropG Σ;
    chan_idiom_ghost_boolG :: ghost_varG Σ bool;
    chan_idiom_ghost_listG :: ghost_varG Σ (list V);
    chan_idiom_setG :: auth_setG Σ gname;
    chan_idiom_ghost_natG :: ghost_varG Σ nat;
    chan_idiom_ghost_unitG :: ghost_varG Σ ();
}.

Definition chan_idiomΣ V : gFunctors :=
  #[ chanΣ V; ghost_mapΣ nat gname;
     ghost_varΣ bool; ghost_varΣ (list V); ghost_varΣ nat; ghost_varΣ ();
     auth_setΣ gname
    ].

#[global] Instance subG_chan_idiomG Σ V :
  subG (chan_idiomΣ V) Σ → chan_idiomG Σ V.
Proof. solve_inG. Qed.
