From Perennial.program_proof.simplepb Require config_proof admin_proof.
From Perennial.program_proof.simplepb.apps Require kv_proof closed_proof.

(* FIXME this list is probably incomplete *)
Definition lemmas :=
  (@config_proof.wp_MakeServer, @config_proof.wp_Server__Serve,
  @admin_proof.wp_Reconfig,
  @kv_proof.wp_Start,
  @kv_proof.wp_MakeClerk,
  @kv_proof.wp_Clerk__Put,
  @kv_proof.wp_Clerk__Get).

Print Assumptions lemmas.

Print Assumptions closed_proof.closed.kv_pb_boot.
