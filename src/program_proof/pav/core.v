From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.pav Require Import classes cryptoffi serde.

(* TODO: split out joint imports (if needed) from msv theory. *)
From RecordUpdate Require Export RecordSet.
From iris.base_logic.lib Require Export mono_nat ghost_map.
From iris.unstable.base_logic Require Export mono_list.
From Perennial.Helpers Require Export Integers.

(* TODO: for same reason not using alias's in go code,
prob shouldn't define all these notations. *)
Notation commit_ty := (list w8) (only parsing).
Notation dig_ty := (list w8) (only parsing).
Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
Notation epoch_ty := w64 (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation opaque_label_ty := (list w8) (only parsing).
Notation map_val_ty := (epoch_ty * pk_ty)%type (only parsing).
Notation map_ty := (gmap map_label_ty map_val_ty) (only parsing).
Notation merkle_map_ty := (gmap (list w8) (list w8)) (only parsing).
Notation opaque_map_val_ty := (epoch_ty * commit_ty)%type (only parsing).
Notation adtr_map_ty := (gmap opaque_label_ty opaque_map_val_ty) (only parsing).
Notation cli_map_val_ty := (option (epoch_ty * commit_ty)) (only parsing).
Notation cli_map_ty := (gmap map_label_ty cli_map_val_ty) (only parsing).
Notation lat_val_ty := (option map_val_ty) (only parsing).
Notation lat_opaque_val_ty := (option opaque_map_val_ty) (only parsing).

Section misc.
Class pavG Σ :=
  {
    #[global] pavG_serv_ep :: mono_natG Σ;
    #[global] pavG_serv_digs ::
      mono_listG ((gmap (list w8) (w64 * list w8)) * list w8) Σ;
    #[global] pavG_serv_map :: ghost_mapG Σ w64 w64;
    #[global] pavG_adtr ::
      mono_listG ((gmap opaque_label_ty (epoch_ty * commit_ty)) * dig_ty) Σ;
    #[global] pavG_cli :: mono_listG (option dig_ty) Σ;
  }.

Context `{!heapGS Σ}.

Definition is_map_label pk uid ver label : iProp Σ :=
  is_vrf_out pk (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) label.

Definition is_commit (val : pk_ty) (commit : commit_ty) : iProp Σ :=
  ∃ rand, is_hash (CommitOpen.encodesF $ CommitOpen.mk val rand) commit.

Lemma is_commit_inj val0 val1 commit :
  is_commit val0 commit -∗ is_commit val1 commit -∗ ⌜ val0 = val1 ⌝.
Proof.
  iIntros "[% Hhash0] [% Hhash1]".
  iDestruct (is_hash_inj with "Hhash0 Hhash1") as %Heq_hash.
  by opose proof (CommitOpen.inj _ _ Heq_hash) as [=].
Qed.

End misc.

Section msv_core.
(* maximum sequence of versions. *)
Context `{!heapGS Σ, !pavG Σ}.

Definition msv_core (m : adtr_map_ty) uid vals pk : iProp Σ :=
  ∃ label,
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#His_label" ∷ is_map_label pk uid (W64 ver) label ∗
    "%Hin_prev" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#His_label" ∷ is_map_label pk uid (W64 $ length vals) label ∗
  "%Hnin_next" ∷ ⌜ m !! label = None ⌝.

Lemma msv_core_len_agree_aux m uid vals0 vals1 pk :
  ("#Hmsv0" ∷ msv_core m uid vals0 pk ∗
  "#Hmsv1" ∷ msv_core m uid vals1 pk ∗
  "%Hlt_len" ∷ ⌜ length vals0 < length vals1 ⌝) -∗
  False.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  list_elem vals1 (length vals0) as val.
  iDestruct (big_sepL_lookup with "Hhist1") as "H"; [exact Hval_lookup|].
  iNamed "H".
  iDestruct (is_vrf_out_det with "His_label0 His_label") as %->. naive_solver.
Qed.

Lemma msv_core_len_agree m uid vals0 vals1 pk :
  ("#Hmsv0" ∷ msv_core m uid vals0 pk ∗
  "#Hmsv1" ∷ msv_core m uid vals1 pk) -∗
  ⌜ length vals0 = length vals1 ⌝.
Proof.
  iNamed 1. destruct (decide (length vals0 = length vals1)) as [?|?]; [done|iExFalso].
  destruct (decide (length vals0 < length vals1)) as [?|?].
  - iApply (msv_core_len_agree_aux _ _ vals0 vals1 with "[]").
    iFrame "Hmsv0 Hmsv1". iPureIntro. lia.
  - iApply (msv_core_len_agree_aux _ _ vals1 vals0 with "[]").
    iFrame "Hmsv1 Hmsv0". iPureIntro. lia.
Qed.

Lemma msv_core_agree m uid vals0 vals1 pk :
  ("#Hmsv0" ∷ msv_core m uid vals0 pk ∗
  "#Hmsv1" ∷ msv_core m uid vals1 pk) -∗
  ⌜ vals0 = vals1 ⌝.
Proof.
  iNamed 1.
  iDestruct (msv_core_len_agree _ _ vals0 vals1 with "[$Hmsv0 $Hmsv1]") as %?.
  iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iApply (big_sepL_func_eq with "Hhist0 Hhist1"); [|done].
  rewrite /Func. iIntros "*". iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->. naive_solver.
Qed.

End msv_core.

Section msv.
Context `{!heapGS Σ, !pavG Σ}.

Definition lat_pk_commit (lat_pk : lat_val_ty) (lat_commit : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_commit with
  | Some (ep0, pk), Some (ep1, commit) =>
    "%Heq_ep" ∷ ⌜ ep0 = ep1 ⌝ ∗
    "#His_commit" ∷ is_commit pk commit
  | None, None => True
  | _, _ => False
  end.

Definition msv (adtr_γ : gname) pk (ep uid : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ m dig (vals : list opaque_map_val_ty),
  "#Hlat_pk_commit" ∷ lat_pk_commit lat (last vals) ∗
  "#Hmap" ∷ mono_list_idx_own adtr_γ (uint.nat ep) (m, dig) ∗
  "#Hmsv_core" ∷ msv_core m uid vals pk.

Lemma msv_agree γ pk ep uid lat0 lat1 :
  ("#Hmsv0" ∷ msv γ pk ep uid lat0 ∗
  "#Hmsv1" ∷ msv γ pk ep uid lat1) -∗
  ⌜ lat0 = lat1 ⌝.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iDestruct (mono_list_idx_agree with "Hmap0 Hmap1") as %H. inversion_clear H. iClear "Hmap0 Hmap1".
  iDestruct (msv_core_agree _ _ vals vals0 with "[$Hmsv_core0 $Hmsv_core1]") as %->.
  destruct lat0 as [[??]|], lat1 as [[??]|], (last vals0) as [[??]|]; [|done..].
  iNamedSuffix "Hlat_pk_commit0" "0". iNamedSuffix "Hlat_pk_commit1" "1".
  iDestruct (is_commit_inj with "His_commit0 His_commit1") as %->. naive_solver.
Qed.

End msv.
