From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From RecordUpdate Require Import RecordSet.
From Perennial.base_logic.lib Require Import ghost_map.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.program_proof.pav Require Import auditor core cryptoffi merkle serde server.

(* TODO: unify these with core as soon as core uses w64's instead of nat's. *)
Notation comm_ty := (list w8) (only parsing).
Notation dig_ty := (list w8) (only parsing).
Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
Notation epoch_ty := w64 (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation map_val_ty := (option (epoch_ty * comm_ty))%type (only parsing).
Notation cli_map_ty := (gmap map_label_ty map_val_ty) (only parsing).

Module Client.
Record t :=
  mk {
    (* client's ghost state. *)
    γ: gname;
    uid: uid_ty;
    next_ver: ver_ty;
    serv_cli: loc;
    serv_γ: gname;
    serv_sig_pk: list w8;
    serv_vrf_pk: loc;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; next_ver; serv_cli; serv_γ; serv_sig_pk; serv_vrf_pk>.

Section defs.
Context `{!heapGS Σ, !mono_listG (option (dig_ty * gname)) Σ, !ghost_mapG Σ map_label_ty map_val_ty}.

Definition have_merkle (dig : list w8) (m : cli_map_ty) : iProp Σ :=
  ([∗ map] k ↦ x ∈ m,
    ∃ proof,
    let label := MapLabelPre.encodesF (MapLabelPre.mk k.1 k.2) in
    match x with
    | None => is_merkle_proof proof label None dig
    | Some y =>
      let val := MapValPre.encodesF (MapValPre.mk y.1 y.2) in
      is_merkle_proof proof label (Some val) dig
    end).

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ (seen_maps : list (option (dig_ty * gname))) sl_serv_sig_pk,
  (* TODO: vrf. *)
  (* key maps. *)
  "Hseen_maps" ∷ mono_list_auth_own obj.(γ) 1 seen_maps ∗
  "Hsubmaps" ∷ ([∗ list] x ∈ seen_maps,
    match x with
    | None => True
    | Some y => ∃ submap, ghost_map_auth y.2 1 submap ∗ have_merkle y.1 submap
    end) ∗
  (* uid and next_ver. *)
  "Hptr_uid" ∷ ptr ↦[Client :: "uid"] #obj.(uid) ∗
  "Hptr_nextVer" ∷ ptr ↦[Client :: "nextVer"] #obj.(next_ver) ∗
  (* clients and parameterized keys. *)
  "#Hptr_servSigPk" ∷ ptr ↦[Client :: "servSigPk"]□ (slice_val sl_serv_sig_pk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded obj.(serv_sig_pk) ∗
  "#His_servSigPk" ∷ is_pk obj.(serv_sig_pk) (serv_sigpred obj.(serv_γ)).
End defs.
End Client.

Section specs.
Context `{!heapGS Σ, !mono_listG (option (dig_ty * gname)) Σ, !ghost_mapG Σ map_label_ty map_val_ty}.

Definition is_key cli_γ uid ver ep comm : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hlatest" ∷ (uid, ver) ↪[sm_γ]□ (Some (ep, comm)) ∗
  "#Hbound" ∷ (uid, word.add (W64 1) ver) ↪[sm_γ]□ None.

Definition is_bound cli_γ uid ver (ep : w64) : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hbound" ∷ (uid, ver) ↪[sm_γ]□ None.

(* an opening exists that binds pk to comm. *)
Definition is_comm (pk : pk_ty) (comm : comm_ty) : iProp Σ. Admitted.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    (ep : w64) (ptr_evid : loc) (err : bool), RET (#ep, #ptr_evid, #err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    if negb err then
      ∃ comm,
      let new_c := set Client.next_ver (word.add (W64 1)) c in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_key" ∷ is_key c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep comm ∗
      "#Hcomm" ∷ is_comm pk comm
    else "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Lemma wp_Client__SelfMon ptr_c c :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    (ep : w64) (ptr_evid : loc) (err : bool), RET (#ep, #ptr_evid, #err);
    "Hown_cli" ∷ Client.own ptr_c c ∗
    if negb err then
      "#His_bound" ∷ is_bound c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep
    else True
  }}}.
Proof. Admitted.

End specs.
