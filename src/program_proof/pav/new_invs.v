From Perennial.program_proof Require Import grove_prelude.

From stdpp Require Import gmap.

Section invs.

Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_ty := (gmap (uid_ty * ver_ty) pk_ty) (only parsing).
(* sub-maps are useful for helping us state non-existence of
certain keys in a way that they carry across map subsets. *)
Notation submap_ty := (gmap (uid_ty * ver_ty) (option pk_ty)) (only parsing).

(* key map monotonic. *)
Definition km_mono (maps : list map_ty) i j map_i map_j :=
  maps !! i = Some map_i →
  maps !! j = Some map_j →
  i ≤ j →
  map_i ⊆ map_j.

(* key map only has consecutive version sequence,
and nothing else outside. *)
Definition km_only_cons_ver (map : map_ty) uid pks :=
  (∀ i, i < length pks → map !! (uid, (W64 i)) = pks !! i) ∧
  (∀ i, i ≥ length pks → map !! (uid, (W64 i)) = None).

Definition serv_inv maps :=
  (∀ i j map_i map_j, km_mono maps i j map_i map_j) ∧
  (∀ i map_i uid, maps !! i = Some map_i → ∃ pks, km_only_cons_ver map_i uid pks).

Definition auditor_inv maps :=
  (∀ i j map_i map_j, km_mono maps i j map_i map_j).

(* key map has consecutive version sequence. *)
Definition km_pk_seq (map : map_ty) uid pks :=
  (∀ i, i < length pks → map !! (uid, (W64 i)) = pks !! i) ∧
  map !! (uid, (W64 (length pks))) = None.

Definition skm_pk_seq (map : submap_ty) uid pks := 
  (∀ i, i < length pks → map !! (uid, (W64 i)) = Some (pks !! i)) ∧
  map !! (uid, (W64 (length pks))) = Some None.

(* subset of submap with full map. *)
Definition submap_subset (submap : submap_ty) (map : map_ty) :=
  ∀ k opt_v, submap !! k = Some opt_v → map !! k = opt_v.

Lemma seq_agree map uid pks0 pks1 :
  km_pk_seq map uid pks0 →
  km_pk_seq map uid pks1 →
  pks0 = pks1.
Proof. Admitted.

Lemma seq_sub smap uid pks map :
  skm_pk_seq smap uid pks →
  submap_subset smap map →
  km_pk_seq map uid pks.
Proof. Admitted.

Lemma agree_same_epoch smap0 smap1 uid pks0 pks1 map :
  (* from two client's Get calls at the same epoch. *)
  skm_pk_seq smap0 uid pks0 →
  skm_pk_seq smap1 uid pks1 →
  (* [map] from Audit bulletin board. *)
  submap_subset smap0 map →
  submap_subset smap1 map →
  pks0 = pks1.
(* apply [seq_agree] and [seq_sub]. *)
Proof. Admitted.

Lemma agree_interp_epoch smap0 smap1 smap2 uid pks0 pks1 map0 map1 map2 i j k maps :
  (* client 0's Put @ i. *)
  skm_pk_seq smap0 uid pks0 →
  (* client 1's later Get @ j. *)
  skm_pk_seq smap1 uid pks1 →
  (* client 0's even later SelfMon @ k. *)
  skm_pk_seq smap2 uid pks0 →

  (* client 0's Audit @ i. *)
  submap_subset smap0 map0 →
  (* client 1's Audit @ j. *)
  submap_subset smap1 map1 →
  (* client 0's Audit @ k. *)
  submap_subset smap2 map2 →

  i ≤ j →
  j ≤ k →
  maps !! i = Some map0 →
  maps !! j = Some map1 →
  maps !! k = Some map2 →

  auditor_inv maps →

  pks0 = pks1.
(* actually use auditor mono inv. *)
Proof. Admitted.

End invs.

(* auditor sig pred:
  - auditor has app-only list of maps
  - they commit to a set of digs.
  - digs indexed at specific epoch gives us the signed dig.
  - additionally, pure [auditor_inv] holds on maps.
*)

(* client Get fn:
  - check dig and hist proof from server.
  - get ghost submap for this epoch, or make if needed.
  - add hist proof pks to submap.
  - return [skm_pk_seq].
*)

(* client Audit fn:
  - check dig against auditor.
  - all things in our prior submap had merkle proofs,
  and therefore are in the auditor map as well.
  - this allows us to provide [submap_subset].
*)
