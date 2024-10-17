From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor core cryptoffi merkle serde server.

Module Client.
Record t :=
  mk {
    (* client's ghost state. *)
    γ: gname;
    uid: uid_ty;
    next_ver: ver_ty;
    next_epoch: epoch_ty;
    serv_cli: loc;
    serv_γ: gname;
    serv_sig_pk: list w8;
    serv_vrf_pk: loc;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; next_ver; next_epoch; serv_cli; serv_γ; serv_sig_pk; serv_vrf_pk>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

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

Definition list_map_equiv {A B} (EQ : A → B → Prop) (l : list (option A)) (m : gmap w64 B) :=
  (∀ (i : nat) a, l !! i = Some (Some a) → (∃ b, m !! (W64 i) = Some b ∧ EQ a b)) ∧
  (∀ (i : nat) b, m !! (W64 i) = Some b → (∃ a, l !! i = Some (Some a) ∧ EQ a b)).

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ (seen_maps : list (option (dig_ty * gname))) ptr_sd sd_ptrs seen_digs sl_serv_sig_pk,
  (* TODO: vrf. *)
  (* key maps. *)
  "Hseen_maps" ∷ mono_list_auth_own obj.(γ) 1 seen_maps ∗
  "Hsubmaps" ∷ ([∗ list] x ∈ seen_maps,
    match x with
    | None => True
    | Some y => ∃ submap, ghost_map_auth y.2 1 submap ∗ have_merkle y.1 submap
    end) ∗
  (* seenDigs. *)
  "Hown_sd" ∷ own_map ptr_sd (DfracOwn 1) sd_ptrs ∗
  "Hptr_sd" ∷ ptr ↦[Client :: "seenDigs"] #ptr_sd ∗
  "Hown_sd_structs" ∷ ([∗ map] l;v ∈ sd_ptrs;seen_digs, SigDig.own l v) ∗
  "%Hagree_sd" ∷ ⌜ list_map_equiv (λ a b, a.1 = b.(SigDig.Dig)) seen_maps seen_digs ⌝ ∗
  (* uid, next_ver, next_epoch. *)
  "Hptr_uid" ∷ ptr ↦[Client :: "uid"] #obj.(uid) ∗
  "Hptr_nextVer" ∷ ptr ↦[Client :: "nextVer"] #obj.(next_ver) ∗
  "Hptr_nextEpoch" ∷ ptr ↦[Client :: "nextEpoch"] #obj.(next_epoch) ∗
  "%Hep_bound" ∷ ⌜ length seen_maps = uint.nat obj.(next_epoch) ⌝ ∗
  (* clients and parameterized keys. *)
  "#Hptr_servSigPk" ∷ ptr ↦[Client :: "servSigPk"]□ (slice_val sl_serv_sig_pk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded obj.(serv_sig_pk) ∗
  "#His_servSigPk" ∷ is_pk obj.(serv_sig_pk) (serv_sigpred obj.(serv_γ)).
End defs.
End Client.

Module clientErr.
Record t :=
  mk {
    err: bool;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  "Hptr_err" ∷ ptr ↦[clientErr :: "err"] #obj.(err).
End defs.
End clientErr.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.

(* an opening exists that binds pk to comm. *)
Definition is_comm (pk : pk_ty) (comm : comm_ty) : iProp Σ. Admitted.
Global Instance is_comm_persis pk comm :
  Persistent (is_comm pk comm).
Proof. Admitted.

Definition is_my_key cli_γ uid ver ep pk : iProp Σ :=
  ∃ dig sm_γ comm,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hlatest" ∷ (uid, ver) ↪[sm_γ]□ (Some (ep, comm)) ∗
  "#Hcomm" ∷ is_comm pk comm ∗
  "#Hbound" ∷ (uid, word.add (W64 1) ver) ↪[sm_γ]□ None.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    (ep : w64) ptr_err err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      let new_c := set Client.next_ver (word.add (W64 1))
        (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_key" ∷ is_my_key c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep pk
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_my_bound cli_γ uid ver (ep : w64) : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hbound" ∷ (uid, ver) ↪[sm_γ]□ None.

Lemma wp_Client__SelfMon ptr_c c :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    (ep : w64) ptr_err err, RET (#ep, #ptr_err);
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      let new_c := (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_bound" ∷ is_my_bound c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_no_other_key cli_γ uid (ep : epoch_ty) : iProp Σ :=
  ∃ dig sm_γ,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hbound" ∷ (uid, W64 0) ↪[sm_γ]□ None.

Definition is_other_key cli_γ uid (ep : epoch_ty) pk : iProp Σ :=
  ∃ (ver : nat) dig sm_γ (ep0 : w64) comm0,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hhist" ∷ ∀ (ver' : w64), ⌜ uint.nat ver' < ver ⌝ -∗
    ∃ ep1 comm1, (uid, ver') ↪[sm_γ]□ (Some (ep1, comm1)) ∗
  "#Hlatest" ∷ (uid, W64 ver) ↪[sm_γ]□ (Some (ep0, comm0)) ∗
  "#Hcomm" ∷ is_comm pk comm0 ∗
  "#Hbound" ∷ (uid, W64 (S ver)) ↪[sm_γ]□ None.

Lemma wp_Client__Get ptr_c c uid :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    (is_reg : bool) sl_pk pk (ep : w64) ptr_err err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      let new_c := (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      if is_reg then
        "Hsl_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
        "#His_key" ∷ is_other_key c.(Client.γ) uid ep pk
      else
        "#His_no_key" ∷ is_no_other_key c.(Client.γ) uid ep
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

(* is_audit says we've audited up *to* ep. *)
Definition is_audit cli_γ adtr_γ (ep : w64) : iProp Σ :=
  ∃ adtr_st cli_st,
  "#Hadtr_st" ∷ comm_st.valid adtr_γ adtr_st ∗
  "#Hcli_seen_maps" ∷ mono_list_lb_own cli_γ cli_st ∗
  "%Hlen_ep" ∷ ⌜ length cli_st = uint.nat ep ⌝ ∗
  "%Hagree_dig" ∷ ([∗ list] ep ↦ x ∈ cli_st,
    match x with
    | None => True
    | Some y => ⌜ ∃ dig, adtr_st.(comm_st.digs) !! ep = Some dig ∧ y.1 = dig ⌝
    end).

Lemma wp_Client__Audit ptr_c c (adtrAddr : w64) sl_adtrPk adtrPk adtr_γ :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk ∗
    "#His_adtrPk" ∷ is_pk adtrPk (adtr_sigpred adtr_γ)
  }}}
  Client__Audit #ptr_c #adtrAddr (slice_val sl_adtrPk)
  {{{
    ptr_err err, RET #ptr_err;
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      "#His_audit" ∷ is_audit c.(Client.γ) adtr_γ c.(Client.next_epoch)
    else True
  }}}.
Proof. Admitted.

Lemma wp_newClient (uid servAddr : w64) (servSigPk servVrfPk : loc) :
  {{{ True }}}
  newClient #uid #servAddr #servSigPk #servVrfPk
  {{{
    ptr_cli cli_γ r1 r2 r3 r4, RET #ptr_cli;
    "Hown_cli" ∷ Client.own ptr_cli (Client.mk cli_γ uid (W64 0) (W64 0) r1 r2 r3 r4)
  }}}.
Proof. Admitted.

End specs.
