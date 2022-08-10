From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.

Section config_proof.

Class configG Σ := {
    config_epochG :> mono_natG Σ ;
    config_configG :> inG Σ (gmapR u64 (dfrac_agreeR (leibnizO (option (list u64))))) ;
}.

Context

End config_proof.
