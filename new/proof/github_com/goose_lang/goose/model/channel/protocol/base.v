From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From Perennial.algebra Require Import auth_set.
From iris.base_logic Require Import ghost_var ghost_map.
From iris.base_logic.lib Require Import saved_prop.

Class chan_protocolG Σ V := ChanProtocolG {
    chan_protocol_chanG :: chanG Σ V;
    chan_protocol_ghost_mapG :: ghost_mapG Σ nat gname;
    (* already in chanG *)
    (* chan_protocol_savedPropG :: savedPropG Σ; *)
    chan_protocol_ghost_boolG :: ghost_varG Σ bool;
    chan_protocol_ghost_listG :: ghost_varG Σ (list V);
    chan_protocol_setG :: auth_setG Σ gname;
    chan_protocol_ghost_natG :: ghost_varG Σ nat;
}.

Definition chan_protocolΣ V : gFunctors :=
  #[ chanΣ V; ghost_mapΣ nat gname;
     ghost_varΣ bool; ghost_varΣ (list V); ghost_varΣ nat;
     auth_setΣ gname
    ].

#[global] Instance subG_chan_protocolG Σ V :
  subG (chan_protocolΣ V) Σ → chan_protocolG Σ V.
Proof. solve_inG. Qed.
