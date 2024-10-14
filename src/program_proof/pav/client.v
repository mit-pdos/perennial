From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From RecordUpdate Require Import RecordSet.
From Perennial.base_logic.lib Require Import ghost_map.
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
Global Instance eta_cli : Settable _ :=
  settable! mk <γ; uid; next_ver; serv_cli; serv_γ; serv_sig_pk; serv_vrf_pk>.

Section defs.
Context `{!heapGS Σ, !ghost_mapG Σ epoch_ty (dig_ty * gname)%type, !ghost_mapG Σ map_label_ty map_val_ty}.

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
  ∃ (epoch_maps : gmap epoch_ty (dig_ty * gname)) sl_serv_sig_pk,
  (* TODO: vrf. *)
  (* key maps. *)
  "Hepoch_maps" ∷ ghost_map_auth obj.(γ) 1 epoch_maps ∗
  "Hsubmaps" ∷ ([∗ map] x ∈ epoch_maps,
    ∃ (submap : cli_map_ty),
    ghost_map_auth x.2 1 submap ∗
    have_merkle x.1 submap) ∗
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
Context `{!heapGS Σ, !ghost_mapG Σ epoch_ty (dig_ty * gname)%type, !ghost_mapG Σ map_label_ty map_val_ty}.

(* timeseries. the general abstraction is having a key view at every epoch.
timeseries is a concrete impl. *)
Record ts_ty :=
  mk_ts {
    entries: list (epoch_ty * comm_ty);
    bound: epoch_ty;
  }.

Definition ts_epoch_mono (ts : ts_ty) :=
  ∀ i j ep_i val_i ep_j val_j,
  ts.(entries) !! i = Some (ep_i, val_i) →
  ts.(entries) !! j = Some (ep_j, val_j) →
  i < j →
  uint.nat ep_i < uint.nat ep_j.

Definition ts_bound_ok (ts : ts_ty) :=
  ∀ i ep val,
  ts.(entries) !! i = Some (ep, val) →
  uint.nat ep ≤ uint.nat ts.(bound).

Definition is_key_entry cli_γ uid (ver : nat) e : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ e.1 ↪[cli_γ]□ (dig, sm_γ) ∗
  "#Hlatest" ∷ (uid, (W64 ver)) ↪[sm_γ]□ (Some e) ∗
  "#Hbound" ∷ (uid, W64 (S ver)) ↪[sm_γ]□ None.

Definition is_key_bound cli_γ uid (ver : nat) ep : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ ep ↪[cli_γ]□ (dig, sm_γ) ∗
  "#Hbound" ∷ (uid, W64 (ver)) ↪[sm_γ]□ None.

(* two of the invariants remain from the pure version,
while the rest have RA analogs. *)
Definition is_my_keys γ uid (ts : ts_ty) : iProp Σ :=
  "#Hentries" ∷ ([∗ list] ver ↦ x ∈ ts.(entries),
    is_key_entry γ uid ver x) ∗
  "#Hbound" ∷ is_key_bound γ uid (length ts.(entries)) ts.(bound) ∗
  "%Hinv_epoch_mono" ∷ ⌜ ts_epoch_mono ts ⌝ ∗
  "%Hinv_bound_ok" ∷ ⌜ ts_bound_ok ts ⌝.

Definition is_comm (pk : pk_ty) (comm : comm_ty) : iProp Σ. Admitted.

Lemma wp_Client__Put ptr_c c ts sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "#Hmy_keys" ∷ is_my_keys c.(Client.γ) c.(Client.uid) ts ∗
    "%Hlatest_keys" ∷ ⌜ length ts.(entries) = uint.nat c.(Client.next_ver) ⌝ ∗
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
      let new_keys := (mk_ts (ts.(entries) ++ [(ep, comm)]) ep) in
      "#Hmy_keys" ∷ is_my_keys c.(Client.γ) c.(Client.uid) new_keys ∗
      "#Hcomm" ∷ is_comm pk comm
    else "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

End specs.
