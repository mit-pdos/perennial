From Perennial.program_proof.pav Require Import prelude.
From Perennial.program_proof.pav Require Import classes cryptoffi serde.

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

Notation enc_label_pre uid ver := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver).
Notation enc_val ep commit := (MapValPre.encodesF $ MapValPre.mk ep commit).

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

Section msv.
(* maximum sequence of versions. *)
Context `{!heapGS Σ, !pavG Σ}.

Definition msv_Some (m : adtr_map_ty) vrf_pk uid lat n_vers : iProp Σ :=
  "#Hhist" ∷
    (∀ ver,
    ⌜ uint.Z ver < uint.Z (word.sub n_vers (W64 1)) ⌝ -∗
    ∃ label val,
    "#His_label" ∷ is_map_label vrf_pk uid ver label ∗
    "%Hlook_map" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#Hlatest" ∷
    (∃ label,
    "#His_label" ∷ is_map_label vrf_pk uid (word.sub n_vers (W64 1)) label ∗
    "%Hlook_map" ∷ ⌜ m !! label = Some lat ⌝) ∗
  "#Hbound" ∷
    (∃ label,
    "#His_label" ∷ is_map_label vrf_pk uid n_vers label ∗
    "%Hlook_map" ∷ ⌜ m !! label = None ⌝).

Lemma msv_Some_vers_agree_aux m vrf_pk uid lat0 n_vers0 lat1 n_vers1 :
  uint.Z n_vers0 < uint.Z n_vers1 →
  msv_Some m vrf_pk uid lat0 n_vers0 -∗
  msv_Some m vrf_pk uid lat1 n_vers1 -∗
  False.
Proof.
  iIntros (?).
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iClear "Hhist0 Hlatest0 Hbound1".
  iNamedSuffix "Hbound0" "0".
  destruct (decide (n_vers0 = word.sub n_vers1 (W64 1))).
  - subst. iNamedSuffix "Hlatest1" "1".
    iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
    naive_solver.
  - iSpecialize ("Hhist1" $! n_vers0 with "[]"); [word|].
    iNamedSuffix "Hhist1" "1".
    iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
    naive_solver.
Qed.

Lemma msv_Some_vers_agree m vrf_pk uid lat0 n_vers0 lat1 n_vers1 :
  msv_Some m vrf_pk uid lat0 n_vers0 -∗
  msv_Some m vrf_pk uid lat1 n_vers1 -∗
  ⌜ n_vers0 = n_vers1 ⌝.
Proof.
  iIntros "Hmsv0 Hmsv1".
  destruct (decide (uint.Z n_vers0 < uint.Z n_vers1)).
  { by iDestruct (msv_Some_vers_agree_aux with "Hmsv0 Hmsv1") as "[]". }
  destruct (decide (uint.Z n_vers1 < uint.Z n_vers0)).
  { by iDestruct (msv_Some_vers_agree_aux with "Hmsv1 Hmsv0") as "[]". }
  word.
Qed.

Lemma msv_Some_nonzero_ver m vrf_pk uid lat n_vers :
  msv_Some m vrf_pk uid lat n_vers -∗
  ⌜ 0 < uint.Z n_vers ⌝.
Proof.
  iNamed 1.
  destruct (decide (n_vers = W64 0)); [|word].
  subst.
  iSpecialize ("Hhist" $! (W64 0) with "[]"); [word|].
  iNamedSuffix "Hhist" "0". iNamedSuffix "Hbound" "1".
  iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
  naive_solver.
Qed.

Definition msv_None (m : adtr_map_ty) vrf_pk uid : iProp Σ :=
  ∃ label,
  "#His_label" ∷ is_map_label vrf_pk uid (W64 0) label ∗
  "%Hlook_map" ∷ ⌜ m !! label = None ⌝.

Lemma msv_Some_None_excl m vrf_pk uid lat n_vers :
  msv_Some m vrf_pk uid lat n_vers -∗
  msv_None m vrf_pk uid -∗
  False.
Proof.
  iIntros "Hmsv0".
  iDestruct (msv_Some_nonzero_ver with "Hmsv0") as %?.
  iNamedSuffix "Hmsv0" "0". iNamedSuffix 1 "1".
  destruct (decide (n_vers = W64 1)).
  + subst. iNamedSuffix "Hlatest0" "0".
    replace (word.sub _ _) with (W64 0) by word.
    iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
    naive_solver.
  + iSpecialize ("Hhist0" $! (W64 0) with "[]"); [word|].
    iNamedSuffix "Hhist0" "0".
    iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
    naive_solver.
Qed.

Definition option_is_commit (lat_pk : lat_val_ty) (lat_commit : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_commit with
  | Some (ep0, pk), Some (ep1, commit) =>
    "%Heq_ep" ∷ ⌜ ep0 = ep1 ⌝ ∗
    "#His_commit" ∷ is_commit pk commit
  | None, None => True
  | _, _ => False
  end.

Definition msv γaudit vrf_pk (ep : w64) uid (lat : lat_val_ty) : iProp Σ :=
  ∃ m dig lat_commit,
  "#Hlook_gs" ∷ mono_list_idx_own γaudit (uint.nat ep) (m, dig) ∗
  "#Hcommit" ∷ option_is_commit lat lat_commit ∗
  "#Hmsv" ∷ match lat_commit with
    | None => "#Hmsv" ∷ msv_None m vrf_pk uid
    | Some lat' => ∃ n_vers, "#Hmsv" ∷ msv_Some m vrf_pk uid lat' n_vers
    end.

Lemma msv_agree γ vrf_pk ep uid lat0 lat1 :
  msv γ vrf_pk ep uid lat0 -∗
  msv γ vrf_pk ep uid lat1 -∗
  ⌜ lat0 = lat1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (mono_list_idx_agree with "Hlook_gs0 Hlook_gs1") as %?.
  simplify_eq/=.
  destruct lat_commit as [[??]|], lat_commit0 as [[??]|];
    iNamedSuffix "Hmsv0" "0"; iNamedSuffix "Hmsv1" "1".
  - iDestruct (msv_Some_vers_agree with "Hmsv0 Hmsv1") as %->.
    iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
    iClear "Hhist0 Hbound0 Hhist1 Hbound1".
    iNamedSuffix "Hlatest0" "0". iNamedSuffix "Hlatest1" "1".
    iDestruct (is_vrf_out_det with "His_label0 His_label1") as %->.
    simplify_eq/=.
    destruct lat0 as [[??]|], lat1 as [[??]|]; try done.
    iNamedSuffix "Hcommit0" "0". iNamedSuffix "Hcommit1" "1".
    iDestruct (is_commit_inj with "His_commit0 His_commit1") as %?.
    by simplify_eq/=.
  - iDestruct (msv_Some_None_excl with "Hmsv0 Hmsv1") as "[]".
  - iDestruct (msv_Some_None_excl with "Hmsv1 Hmsv0") as "[]".
  - by destruct lat0 as [[??]|], lat1 as [[??]|].
Qed.

End msv.
