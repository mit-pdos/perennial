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

Definition lat_pk_comm_reln (lat_pk : lat_val_ty) (lat_comm : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_comm with
  | Some (ep0, pk), Some (ep1, comm) =>
    "%Heq_ep" ∷ ⌜ ep0 = ep1 ⌝ ∗
    "#His_comm" ∷ is_comm pk comm
  | None, None => True
  | _, _ => False
  end.

Definition msv_core_aux (m : adtr_map_ty) uid (vals : list opaque_map_val_ty) : iProp Σ :=
  "%Hlt_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  (∀ (ver : w64) val,
    "%Hlook_ver" ∷ ⌜ vals !! (uint.nat ver) = Some val ⌝ -∗
    ∃ label,
    ("#His_label" ∷ is_vrf uid ver label ∗
    "%Hin_map" ∷ ⌜ m !! label = Some val ⌝)).

Definition msv_core m uid vals : iProp Σ :=
  ∃ label,
  "#Hmsv_aux" ∷ msv_core_aux m uid vals ∗
  "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
  "%Hnin_next" ∷ ⌜ m !! label = None ⌝.

(* TODO: upstream. *)
Lemma lookup_snoc {A} (l : list A) (x : A) :
  (l ++ [x]) !! (length l) = Some x.
Proof. by opose proof (proj2 (lookup_snoc_Some x l (length l) x) _) as H; [naive_solver|]. Qed.

Lemma msv_core_aux_snoc m uid l x :
  "#Hmsv_aux" ∷ msv_core_aux m uid (l ++ [x]) -∗
  (∃ label,
  "#Hmsv_aux" ∷ msv_core_aux m uid l ∗
  "#His_label" ∷ is_vrf uid (W64 $ length l) label ∗
  "%Hin_lat" ∷ ⌜ m !! label = Some x ⌝).
Proof.
  iNamed 1. iNamed "Hmsv_aux". rewrite app_length in Hlt_vals. list_simplifier.
  iDestruct ("Hmsv_aux" $! (W64 $ length l) with "[]") as "Hlat".
  { rewrite nat_thru_w64_id; [|lia]. iPureIntro. apply lookup_snoc. }
  iNamed "Hlat". iFrame "#%". iSplit. { iPureIntro. lia. }
  iIntros "*". iNamed 1. iSpecialize ("Hmsv_aux" with "[]").
  { iPureIntro. rewrite lookup_app_l; [exact Hlook_ver|by eapply lookup_lt_Some]. }
  iFrame "#".
Qed.

Lemma msv_core_aux_agree m uid vals0 vals1 :
  ("#Hmsv_aux0" ∷ msv_core_aux m uid vals0 ∗
  "#Hmsv_aux1" ∷ msv_core_aux m uid vals1 ∗
  "%Heq_len" ∷ ⌜ length vals0 = length vals1 ⌝) -∗
  ⌜ vals0 = vals1 ⌝.
Proof.
  revert vals1. induction vals0 as [|x0 l0 IH] using rev_ind;
    destruct vals1 as [|x1 l1 _] using rev_ind; iNamed 1.
  - done.
  - rewrite length_app/= in Heq_len. lia.
  - rewrite length_app/= in Heq_len. lia.
  - rewrite !length_app/= in Heq_len.
    iRename "Hmsv_aux0" into "HM0". iRename "Hmsv_aux1" into "HM1".
    iDestruct (msv_core_aux_snoc with "HM0") as "H". iNamedSuffix "H" "0".
    iDestruct (msv_core_aux_snoc with "HM1") as "H". iNamedSuffix "H" "1".
    assert (length l0 = length l1) as HT by lia.
    iEval (rewrite HT) in "His_label0". clear HT.
    iDestruct (is_vrf_func (_, _) with "His_label0 His_label1") as %->.
    simplify_map_eq/=. specialize (IH l1).
    iDestruct (IH with "[$Hmsv_aux0 $Hmsv_aux1]") as %->. { iPureIntro. lia. }
    naive_solver.
Qed.

Lemma msv_core_len_agree_aux m uid vals0 vals1 :
  ("#Hmsv0" ∷ msv_core m uid vals0 ∗
  "#Hmsv1" ∷ msv_core m uid vals1 ∗
  "%Hlt_len" ∷ ⌜ length vals0 < length vals1 ⌝) -∗
  False.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1". iNamed "Hmsv_aux1".
  list_elem vals1 (uint.nat (length vals0)) as val.
  iSpecialize ("Hmsv_aux1" with "[]"). { iPureIntro. exact Hval_lookup. }
  iNamed "Hmsv_aux1".
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
  iNamed 1. iApply msv_core_aux_agree.
  iPoseProof "Hmsv0" as "Hmsv0'". iPoseProof "Hmsv1" as "Hmsv1'".
  iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1". iFrame "#".
  iApply msv_core_len_agree. iFrame "Hmsv0' Hmsv1'".
Qed.

End msv_core.

Section msv.
Context `{!heapGS Σ, !pavG Σ}.

Definition msv (adtr_γ : gname) (ep uid : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (m : adtr_map_ty) (vals : list opaque_map_val_ty),
  "%Hlen_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  "#Hcomm_reln" ∷ lat_pk_comm_reln lat (last vals) ∗
  "#Hmap" ∷ mono_list_idx_own adtr_γ (uint.nat ep) m ∗
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#His_label" ∷ is_vrf uid (W64 ver) label ∗
    "%Hin_map" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#Hbound" ∷
    (∃ label,
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
    "%Hnin_map" ∷ ⌜ m !! label = None ⌝).

Lemma msv_agree γ ep uid lat0 lat1 :
  ("#Hmsv0" ∷ msv γ ep uid lat0 ∗
  "#Hmsv1" ∷ msv γ ep uid lat1) -∗
  ⌜ lat0 = lat1 ⌝.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iDestruct (mono_list_idx_agree with "Hmap0 Hmap1") as %->.
  iClear "Hmap0 Hmap1".
  iDestruct (msv_core_agree with "[]") as %->; [iSplit|].
  { iNamed "Hbound0". iFrame "#%". iClear "His_label". iIntros "*". iNamed 1.
    iDestruct (big_sepL_lookup with "Hhist0") as "H"; [exact Hlook_ver|].
    iNamed "H". iEval (rewrite w64_to_nat_id) in "His_label". iFrame "#%". }
  { iNamed "Hbound1". iFrame "#%". iClear "His_label". iIntros "*". iNamed 1.
    iDestruct (big_sepL_lookup with "Hhist1") as "H"; [exact Hlook_ver|].
    iNamed "H". iEval (rewrite w64_to_nat_id) in "His_label". iFrame "#%". }
  destruct lat0 as [[??]|], lat1 as [[??]|], (last vals0) as [[??]|]; [|done..].
  iNamedSuffix "Hcomm_reln0" "0". iNamedSuffix "Hcomm_reln1" "1".
  iDestruct (is_comm_inj with "His_comm0 His_comm1") as %->. naive_solver.
Qed.

End msv.

Section adtr_inv.

Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : nat) mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

Definition maps_epoch_ok (ms : list adtr_map_ty) :=
  ∀ (ep : nat) m_ep k ep' comm,
  ms !! ep = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.nat ep' ≤ ep.

Definition adtr_inv ms := maps_mono ms ∧ maps_epoch_ok ms.

End adtr_inv.
