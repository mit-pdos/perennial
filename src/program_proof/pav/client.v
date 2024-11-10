From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import auditor core classes cryptoffi merkle serde server.

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

Definition is_my_key cli_γ uid ver ep pk : iProp Σ :=
  ∃ dig sm_γ comm label0 label1,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hcomm" ∷ is_comm pk comm ∗
  "#Hin_map_lat" ∷ (uid, ver) ↪[sm_γ]□ (Some (ep, comm)) ∗
  "#His_label0" ∷ is_vrf uid ver label0 ∗
  "#Hnin_map_next" ∷ (uid, word.add (W64 1) ver) ↪[sm_γ]□ None ∗
  "#His_label1" ∷ is_vrf uid (word.add (W64 1) ver) label1.

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
      "#His_key" ∷ is_my_key c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep pk ∗
      "%Hnoof_ver" ∷ ⌜ uint.Z new_c.(Client.next_ver) = (uint.Z c.(Client.next_ver) + 1)%Z ⌝ ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z new_c.(Client.next_epoch) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) ≤ uint.Z ep ⌝
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_my_bound cli_γ uid ver (ep : w64) : iProp Σ :=
  ∃ dig sm_γ label,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
  "#Hnin_map_next" ∷ (uid, ver) ↪[sm_γ]□ None ∗
  "#His_label" ∷ is_vrf uid ver label.

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
      "#His_bound" ∷ is_my_bound c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z new_c.(Client.next_epoch) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_other_key cli_γ uid (ep : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (vals : list opaque_map_val_ty) dig m_γ,
  "#Hpk_comm_reln" ∷ pk_comm_reln lat (last vals) ∗
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, m_γ)) ∗
  "#Hhist" ∷
    ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#Hin_map" ∷ (uid, W64 ver) ↪[m_γ]□ Some val ∗
    "#His_label" ∷ is_vrf uid (W64 ver) label) ∗
  "#Hbound" ∷
    (∃ label,
    "#Hin_map" ∷ (uid, W64 $ length vals) ↪[m_γ]□ None ∗
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label).

Lemma wp_Client__Get ptr_c c uid :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    (is_reg : bool) sl_pk pk (ep : w64) ep' ptr_err err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      let new_c := (set Client.next_epoch (λ _, word.add ep (W64 1)) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z new_c.(Client.next_epoch) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝ ∗
      "Hsl_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
      "#His_key" ∷ is_other_key c.(Client.γ) uid ep
        (if is_reg then Some (ep', pk) else None)
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

(* is_audit says we've audited up *to* (not including) bound. *)
Definition is_audit (cli_γ adtr_γ : gname) (bound : w64) : iProp Σ :=
  ∃ ms,
  "#Hadtr_maps" ∷ mono_list_lb_own adtr_γ ms ∗
  "%Hlen_maps" ∷ ⌜ length ms = uint.nat bound ⌝ ∗
  "%Hinv_adtr" ∷ ⌜ adtr_inv ms ⌝ ∗
  "#Hmap_transf" ∷ (□ ∀ (ep : w64) m uid ver val dig sm_γ label,
    ("%Hlook_map" ∷ ⌜ ms !! uint.nat ep = Some m ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (dig, sm_γ)) ∗
    "#Hin_cli" ∷ (uid, ver) ↪[sm_γ]□ val ∗
    "#His_label" ∷ is_vrf uid ver label)
    -∗
    "%Hin_adtr" ∷ ⌜ m !! label = val ⌝).

Lemma wp_Client__Audit ptr_c c (adtrAddr : w64) sl_adtrPk adtrPk :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk
  }}}
  Client__Audit #ptr_c #adtrAddr (slice_val sl_adtrPk)
  {{{
    ptr_err err, RET #ptr_err;
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Herr" ∷ clientErr.own ptr_err err ∗
    if negb err.(clientErr.err) then
      "Hcan_audit" ∷ (∀ adtr_γ, is_pk adtrPk (adtr_sigpred adtr_γ) -∗
        ("#His_audit" ∷ is_audit c.(Client.γ) adtr_γ c.(Client.next_epoch)))
    else True
  }}}.
Proof. Admitted.

Lemma wp_newClient (uid servAddr : w64) sl_servSigPk servSigPk (servVrfPk : loc) :
  {{{
    "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded servSigPk
  }}}
  newClient #uid #servAddr (slice_val sl_servSigPk) #servVrfPk
  {{{
    ptr_cli cli_γ r1 r2 r3, RET #ptr_cli;
    "Hown_cli" ∷ Client.own ptr_cli (Client.mk cli_γ uid (W64 0) (W64 0) r1 r2 servSigPk r3)
  }}}.
Proof. Admitted.

End specs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma get_audit_msv cli_γ uid ep lat adtr_γ aud_ep :
  uint.Z ep < uint.Z aud_ep →
  ("#His_key" ∷ is_other_key cli_γ uid ep lat ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  msv adtr_γ ep uid lat.
Proof.
  intros ?. iNamed 1. iNamed "His_audit". iNamed "His_key". iNamedSuffix "Hbound" "_bnd".
  list_elem ms (uint.nat ep) as m.
  iDestruct (mono_list_idx_own_get with "Hadtr_maps") as "Hadtr_map"; [exact Hm_lookup|].
  iFrame "#". iSplit.
  - iApply big_sepL_forall.  iIntros "* %Hlook_val".
    iDestruct (big_sepL_lookup with "Hhist") as "H"; [exact Hlook_val|]. iNamed "H".
    iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_map $His_label]") as %?; [done|].
    iFrame "#%".
  - by iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_map_bnd $His_label_bnd]") as %?.
Qed.

End derived.
