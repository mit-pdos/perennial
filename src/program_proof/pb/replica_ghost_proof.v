From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.
From Perennial.program_proof.pb Require Export ghost_proof.

Section replica_ghost_proof.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Implicit Type γ:pb_names.

Lemma append_new_ghost γ r (newCn:u64) newLog :
  "Hown" ∷ own_Replica_ghost γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog ∗
  "%Hnew" ∷ ⌜int.Z r.(cn) < int.Z newCn ∨ r.(opLog )⪯ newLog⌝
  ={⊤}=∗
  accepted_lb γ newCn r.(rid) newLog.
Proof.
  iNamed 1.
  iNamed "Hown".
Admitted.

Lemma append_dup_ghost γ r (newCn:u64) newLog :
  "Hown" ∷ own_Replica_ghost γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog ∗
  "%Hdup" ∷ ⌜int.Z r.(cn) = int.Z newCn ∧ newLog ⪯ r.(opLog )⌝
  ={⊤}=∗
  accepted_lb γ newCn r.(rid) newLog.
Proof.
  iNamed 1.
  iNamed "Hown".
Admitted.

End replica_ghost_proof.
