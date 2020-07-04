(** Test which admits are needed by some top-level theorems *)
(* importing the prelude ensures notations are in scope for these lemma
statements *)
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import
     replicated_block_proof single_inode_proof dir_proof.

Print Assumptions replicated_block_proof.init_zero_cinv. (* not used by [OpenRead] *)
Print Assumptions replicated_block_proof.OpenRead_adequate.

(* FIXME: also prove and check zero_init lemma. *)
Print Assumptions single_inode_proof.wpc_Open.
Print Assumptions single_inode_proof.is_single_inode_alloc.
Print Assumptions single_inode_proof.wpc_Read.
Print Assumptions single_inode_proof.wpc_Append.

(* FIXME: also prove and check zero_init lemma. *)
Print Assumptions dir_proof.wpc_Open.
Print Assumptions dir_proof.is_dir_alloc.
Print Assumptions dir_proof.wpc_Read.
Print Assumptions dir_proof.wpc_Append.
