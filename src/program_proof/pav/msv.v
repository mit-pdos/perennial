From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import core cryptoffi.

(* Maximum Sequence of Versions (MSV).
sequence: contiguous versions starting from 0.
maximum: the longest sequence s.t. the next version is not present.

MSV is on a plaintext latest pk.
we have a commitment for that pk, and the commitment is in the map.
we need not have plaintexts for all prior versions,
like in the Client Get calls.
we just need to know their opaque commitments are in the map.
this difference is why we separated the "history" and "latest" resources. *)

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition msv_Some (m : adtr_map_ty) vrf_pk uid pk n_vers : iProp Σ :=
  "#Hhist" ∷
    (∀ ver, ⌜ uint.Z ver < uint.Z (word.sub n_vers (W64 1)) ⌝ -∗
    ∃ label val,
    "#Hlabel" ∷ is_map_label vrf_pk uid ver label ∗
    "%Hlook_map" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#Hlatest" ∷
    (∃ ep commit label,
    "#Hcommit" ∷ is_commit pk commit ∗
    "#Hlabel" ∷ is_map_label vrf_pk uid (word.sub n_vers (W64 1)) label ∗
    "%Hlook_map" ∷ ⌜ m !! label = Some (ep, commit) ⌝) ∗
  "#Hbound" ∷
    (∃ label,
    "#Hlabel" ∷ is_map_label vrf_pk uid n_vers label ∗
    "%Hlook_map" ∷ ⌜ m !! label = None ⌝).

Lemma msv_Some_vers_agree_aux m vrf_pk uid pk0 n_vers0 pk1 n_vers1 :
  uint.Z n_vers0 < uint.Z n_vers1 →
  msv_Some m vrf_pk uid pk0 n_vers0 -∗
  msv_Some m vrf_pk uid pk1 n_vers1 -∗
  False.
Proof.
  iIntros (?).
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iClear "Hhist0 Hlatest0 Hbound1".
  iNamedSuffix "Hbound0" "0".
  destruct (decide (n_vers0 = word.sub n_vers1 (W64 1))).
  - subst. iNamedSuffix "Hlatest1" "1".
    iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
    naive_solver.
  - iSpecialize ("Hhist1" $! n_vers0 with "[]"); [word|].
    iNamedSuffix "Hhist1" "1".
    iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
    naive_solver.
Qed.

Lemma msv_Some_vers_agree m vrf_pk uid pk0 n_vers0 pk1 n_vers1 :
  msv_Some m vrf_pk uid pk0 n_vers0 -∗
  msv_Some m vrf_pk uid pk1 n_vers1 -∗
  ⌜ n_vers0 = n_vers1 ⌝.
Proof.
  iIntros "Hmsv0 Hmsv1".
  destruct (decide (uint.Z n_vers0 < uint.Z n_vers1)).
  { by iDestruct (msv_Some_vers_agree_aux with "Hmsv0 Hmsv1") as "[]". }
  destruct (decide (uint.Z n_vers1 < uint.Z n_vers0)).
  { by iDestruct (msv_Some_vers_agree_aux with "Hmsv1 Hmsv0") as "[]". }
  word.
Qed.

Lemma msv_Some_nonzero_ver m vrf_pk uid pk n_vers :
  msv_Some m vrf_pk uid pk n_vers -∗
  ⌜ 0 < uint.Z n_vers ⌝.
Proof.
  iNamed 1.
  destruct (decide (n_vers = W64 0)); [|word].
  subst.
  iSpecialize ("Hhist" $! (W64 0) with "[]"); [word|].
  iNamedSuffix "Hhist" "0". iNamedSuffix "Hbound" "1".
  iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
  naive_solver.
Qed.

Definition msv_None (m : adtr_map_ty) vrf_pk uid : iProp Σ :=
  ∃ label,
  "#Hlabel" ∷ is_map_label vrf_pk uid (W64 0) label ∗
  "%Hlook_map" ∷ ⌜ m !! label = None ⌝.

Lemma msv_Some_None_excl m vrf_pk uid pk n_vers :
  msv_Some m vrf_pk uid pk n_vers -∗
  msv_None m vrf_pk uid -∗
  False.
Proof.
  iIntros "Hmsv0".
  iDestruct (msv_Some_nonzero_ver with "Hmsv0") as %?.
  iNamedSuffix "Hmsv0" "0". iNamedSuffix 1 "1".
  destruct (decide (n_vers = W64 1)).
  + subst. iNamedSuffix "Hlatest0" "0".
    replace (word.sub _ _) with (W64 0) by word.
    iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
    naive_solver.
  + iSpecialize ("Hhist0" $! (W64 0) with "[]"); [word|].
    iNamedSuffix "Hhist0" "0".
    iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
    naive_solver.
Qed.

Definition msv γaudit vrf_pk (ep : w64) uid opt_pk : iProp Σ :=
  ∃ m dig,
  "#Hlook_gs" ∷ mono_list_idx_own γaudit (uint.nat ep) (m, dig) ∗
  "#Hmsv" ∷ match opt_pk with
    | None => "#Hmsv" ∷ msv_None m vrf_pk uid
    | Some pk => ∃ n_vers, "#Hmsv" ∷ msv_Some m vrf_pk uid pk n_vers
    end.

Lemma msv_agree γ vrf_pk ep uid opt_pk0 opt_pk1 :
  msv γ vrf_pk ep uid opt_pk0 -∗
  msv γ vrf_pk ep uid opt_pk1 -∗
  ⌜ opt_pk0 = opt_pk1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (mono_list_idx_agree with "Hlook_gs0 Hlook_gs1") as %?.
  simplify_eq/=.
  destruct opt_pk0, opt_pk1; [..|done];
    iNamedSuffix "Hmsv0" "0"; iNamedSuffix "Hmsv1" "1".
  - iDestruct (msv_Some_vers_agree with "Hmsv0 Hmsv1") as %->.
    iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
    iClear "Hhist0 Hbound0 Hhist1 Hbound1".
    iNamedSuffix "Hlatest0" "0". iNamedSuffix "Hlatest1" "1".
    iDestruct (is_vrf_out_det with "Hlabel0 Hlabel1") as %->.
    simplify_eq/=.
    iDestruct (is_commit_inj with "Hcommit0 Hcommit1") as %?.
    by simplify_eq/=.
  - iDestruct (msv_Some_None_excl with "Hmsv0 Hmsv1") as "[]".
  - iDestruct (msv_Some_None_excl with "Hmsv1 Hmsv0") as "[]".
Qed.

End proof.
