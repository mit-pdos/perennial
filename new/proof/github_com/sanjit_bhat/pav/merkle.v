(* use iris.bi Module structure to enforce strict "merkle" namespace. *)
(* NOTE: with multi-file "pkg", i don't think it's possible to make
"internal" things invisible to the outside.
marking them "Local" would make them hard to use from other inside-pkg files.
splitting into "internal" / "external" modules is tedious. *)
From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Export
  base code serde theory.

Module Import merkle.
  Export base.merkle code.merkle serde.merkle theory.merkle.
End merkle.

(* external defs. *)
#[global] Opaque is_initialized own_Map is_map
  wish_NonMemb wish_Memb wish_Update.
