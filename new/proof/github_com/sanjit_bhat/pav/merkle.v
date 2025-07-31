(* NOTE: "merkle_proof" files themselves don't explicitly define Modules.
this allows merkle files to not have to write "merkle".
however, when they're exposed to the outside, they're within this merkle module. *)
From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base merkle serde theory.

Module merkle.
  Export base merkle serde theory.
  (* tentative strategy:
  - inside sub-files, don't mark opaque / local.
  those objects need to be visible inside the "pkg".
  - at export time, only export external objects.
  - ideally, mark external objects as opaque.
  if haven't proved all helper lemmas for external obj,
  then might need to leave as transp and mark lower-level obj as opaque. *)
  #[global] Opaque is_full_tree is_merkle_map is_merkle_entry.
End merkle.
