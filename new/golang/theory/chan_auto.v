From New.golang.defn Require Import typing.
From New.golang.theory Require Import auto chan.

Tactic Notation "wp_for_chan" :=
  chan.wp_for_chan_core; _wp_for_cleanup.
Tactic Notation "wp_for_chan" constr(hyp) :=
  chan.wp_for_chan_core; iNamed hyp; wp_for_cleanup.
Ltac wp_for_chan_post :=
  chan.wp_for_chan_post_core; try wp_auto.
