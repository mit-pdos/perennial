From Perennial.program_proof.vrsm Require kv_proof closed_proof config_proof reconfig.proof.
From Perennial.program_proof.cachekv Require proof.

Definition lemmas :=
  (@config_proof.wp_StartServer,
   @reconfig.proof.wp_Reconfig,
   @kv_proof.wp_Start,
   @kv_proof.wp_MakeClerk,
   @kv_proof.wp_Clerk__Put,
   @kv_proof.wp_Clerk__Get,
   @kv_proof.wp_Clerk__CondPut,
   @cachekv.proof.wp_CacheKv__Get,
   @cachekv.proof.wp_CacheKv__GetAndCache,
   @cachekv.proof.wp_CacheKv__Put
  ).

Print Assumptions lemmas.

Print Assumptions closed_proof.closed.closed_bank.
