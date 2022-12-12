From Perennial.program_proof.simplepb Require Import config_proof admin_proof.
From Perennial.program_proof.simplepb.apps Require Import kv_proof.

(* FIXME this list is probably incomplete *)
Definition lemmas :=
  (@config_proof.wp_MakeServer, @config_proof.wp_Server__Serve,
  @admin_proof.wp_Reconfig,
  @kv_proof.wp_Start).
Print Assumptions lemmas.
