From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.pav Require Import classes serde.

From RecordUpdate Require Export RecordSet.
From iris.unstable.base_logic Require Export mono_list.
From Perennial.base_logic.lib Require Export ghost_map.
From Perennial.Helpers Require Export Integers.

(* TODO: for same reason not using alias's in go code,
prob shouldn't define all these notations. *)
Notation comm_ty := (list w8) (only parsing).
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
Notation opaque_map_val_ty := (epoch_ty * comm_ty)%type (only parsing).
Notation adtr_map_ty := (gmap opaque_label_ty opaque_map_val_ty) (only parsing).
Notation cli_map_val_ty := (option (epoch_ty * comm_ty)) (only parsing).
Notation cli_map_ty := (gmap map_label_ty cli_map_val_ty) (only parsing).
Notation lat_val_ty := (option map_val_ty) (only parsing).
Notation lat_opaque_val_ty := (option opaque_map_val_ty) (only parsing).

Section misc.
Class pavG Σ :=
  {
    #[global] pavG_adtr :: mono_listG (gmap opaque_label_ty (epoch_ty * comm_ty)) Σ;
    #[global] pavG_client_seen_maps :: mono_listG (option (dig_ty * gname)) Σ;
    #[global] pavG_client_submaps :: ghost_mapG Σ map_label_ty cli_map_val_ty;
  }.

Context `{!heapGS Σ}.

(* an opening exists that binds pk to comm. *)
Definition is_comm (pk : pk_ty) (comm : comm_ty) : iProp Σ. Admitted.
Global Instance is_comm_persis pk comm :
  Persistent (is_comm pk comm).
Proof. Admitted.
(* Func doesn't hold. there's mult comms for a single pk. *)
Global Instance is_comm_inj : InjRel is_comm.
Proof. Admitted.

Definition is_vrf (uid ver : w64) (hash : opaque_label_ty) : iProp Σ. Admitted.
Global Instance is_vrf_persis uid ver hash : Persistent (is_vrf uid ver hash).
Proof. Admitted.
Global Instance is_vrf_func : Func (uncurry is_vrf).
Proof. Admitted.
Global Instance is_vrf_inj : InjRel (uncurry is_vrf).
Proof. Admitted.

End misc.

Section msv_core.
(* maximum sequence of versions. *)
Context `{!heapGS Σ, !pavG Σ}.

Definition msv_core (m : adtr_map_ty) uid vals : iProp Σ :=
  ∃ label,
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#His_label" ∷ is_vrf uid (W64 ver) label ∗
    "%Hin_prev" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
  "%Hnin_next" ∷ ⌜ m !! label = None ⌝.

Lemma msv_core_len_agree_aux m uid vals0 vals1 :
  ("#Hmsv0" ∷ msv_core m uid vals0 ∗
  "#Hmsv1" ∷ msv_core m uid vals1 ∗
  "%Hlt_len" ∷ ⌜ length vals0 < length vals1 ⌝) -∗
  False.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  list_elem vals1 (length vals0) as val.
  iDestruct (big_sepL_lookup with "Hhist1") as "H"; [exact Hval_lookup|].
  iNamed "H".
  iDestruct (is_vrf_func (_, _) with "His_label0 His_label") as %->.
  naive_solver.
Qed.

Lemma msv_core_len_agree m uid vals0 vals1 :
  ("#Hmsv0" ∷ msv_core m uid vals0 ∗
  "#Hmsv1" ∷ msv_core m uid vals1) -∗
  ⌜ length vals0 = length vals1 ⌝.
Proof.
  iNamed 1. destruct (decide (length vals0 = length vals1)) as [?|?]; [done|iExFalso].
  destruct (decide (length vals0 < length vals1)) as [?|?].
  - iApply (msv_core_len_agree_aux _ _ vals0 vals1 with "[]").
    iFrame "Hmsv0 Hmsv1". iPureIntro. lia.
  - iApply (msv_core_len_agree_aux _ _ vals1 vals0 with "[]").
    iFrame "Hmsv1 Hmsv0". iPureIntro. lia.
Qed.

Lemma msv_core_agree m uid vals0 vals1 :
  ("#Hmsv0" ∷ msv_core m uid vals0 ∗
  "#Hmsv1" ∷ msv_core m uid vals1) -∗
  ⌜ vals0 = vals1 ⌝.
Proof.
  iNamed 1.
  iDestruct (msv_core_len_agree _ _ vals0 vals1 with "[$Hmsv0 $Hmsv1]") as %?.
  iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iApply (big_sepL_func_eq with "Hhist0 Hhist1"); [|done].
  rewrite /Func. iIntros "*". iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_vrf_func (_,_) with "His_label0 His_label1") as %->. naive_solver.
Qed.

End msv_core.

Section msv.
Context `{!heapGS Σ, !pavG Σ}.

Definition pk_comm_reln (lat_pk : lat_val_ty) (lat_comm : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_comm with
  | Some (ep0, pk), Some (ep1, comm) =>
    "%Heq_ep" ∷ ⌜ ep0 = ep1 ⌝ ∗
    "#His_comm" ∷ is_comm pk comm
  | None, None => True
  | _, _ => False
  end.

Definition msv (adtr_γ : gname) (ep uid : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (m : adtr_map_ty) (vals : list opaque_map_val_ty),
  "#Hpk_comm_reln" ∷ pk_comm_reln lat (last vals) ∗
  "#Hmap" ∷ mono_list_idx_own adtr_γ (uint.nat ep) m ∗
  "#Hmsv_core" ∷ msv_core m uid vals.

Lemma msv_agree γ ep uid lat0 lat1 :
  ("#Hmsv0" ∷ msv γ ep uid lat0 ∗
  "#Hmsv1" ∷ msv γ ep uid lat1) -∗
  ⌜ lat0 = lat1 ⌝.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iDestruct (mono_list_idx_agree with "Hmap0 Hmap1") as %->. iClear "Hmap0 Hmap1".
  iDestruct (msv_core_agree _ _ vals vals0 with "[$Hmsv_core0 $Hmsv_core1]") as %->.
  destruct lat0 as [[??]|], lat1 as [[??]|], (last vals0) as [[??]|]; [|done..].
  iNamedSuffix "Hpk_comm_reln0" "0". iNamedSuffix "Hpk_comm_reln1" "1".
  iDestruct (is_comm_inj with "His_comm0 His_comm1") as %->. naive_solver.
Qed.

End msv.
