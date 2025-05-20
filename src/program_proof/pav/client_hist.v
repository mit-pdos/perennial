From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc auditor core classes client cryptoffi evidence
  logical_audit logical_hist merkle msv rpc serde server.

Module hist_epochs_puts.

(* length-extends hist with its last element. *)
Definition lookup_epochs (hist : list $ option pk_ty) (ep : w64) :=
  match hist !! (uint.nat ep) with
  | Some opt_pk => opt_pk
  | None => mjoin $ last hist
  end.

Definition reln epochs puts :=
  ∀ ep,
  lookup_epochs epochs ep = lookup_puts_hist puts ep.

Lemma update_replicate epochs puts n :
  reln epochs puts →
  reln (epochs ++ replicate n (mjoin $ last epochs)) puts.
Proof.
  rewrite /reln /lookup_epochs.
  intros Hreln ep.
  ospecialize (Hreln ep).
  rewrite last_replicate_option_app.
  destruct (decide (uint.Z ep < Z.of_nat $ length epochs)).
  { rewrite lookup_app_l; [done|word]. }
  rewrite lookup_ge_None_2 in Hreln; [|word].
  rewrite lookup_app_r; [|word].
  case_match; [|done].
  apply lookup_replicate in H.
  intuition.
  by simplify_eq/=.
Qed.

Lemma update_new epochs puts ep pk :
  (* something to tie together epochs and puts (ep). *)
  Z.of_nat $ length epochs = uint.Z ep →
  reln epochs puts →
  reln (epochs ++ [Some pk]) (puts ++ [(ep, pk)]).
Proof.
  rewrite /reln /lookup_epochs /lookup_puts_hist.
  intros ? Hreln ep0.
  rewrite filter_snoc /=.
  destruct (decide (uint.Z ep0 < Z.of_nat $ length epochs)).
  (* revert lookups back to the original hists. *)
  - ospecialize (Hreln ep0).
    (* epochs. *)
    rewrite lookup_app_l; [|word].
    opose proof (list_lookup_lt epochs (uint.nat ep0) _) as [? Ht]; [word|].
    rewrite Ht in Hreln |-*.
    (* puts. *)
    case_decide; [word|].
    by list_simplifier.
  (* extract snoc'd entry out of hists. *)
  - clear Hreln.
    (* puts. *)
    case_decide; [|word].
    rewrite !last_snoc /=.
    (* epochs. *)
    rewrite lookup_app_r; [|word].
    case_match; [|done].
    by list_simplifier.
Qed.

End hist_epochs_puts.

Module ClientHist.
Record t :=
  mk {
    γ: gname;
    uid: w64;
    (* epochs_hist allows stating the "intuitive" KT consistency property:
    that a client knows its key at every epoch. *)
    epochs_hist: list (option pk_ty);
    serv: Server.t;
    serv_is_good: bool;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; epochs_hist; serv; serv_is_good>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ puts_hist (next_epoch : w64),
  (* this doesn't hold for Get ops, but those are intentionally not part
  of the ClientHist api. *)
  "%Heq_next_ep" ∷ ⌜ Z.of_nat $ length obj.(epochs_hist) = uint.Z next_epoch ⌝ ∗
  "%Hhist_reln" ∷ ⌜ hist_epochs_puts.reln obj.(epochs_hist) puts_hist ⌝ ∗

  "Hcli" ∷ Client.own ptr (Client.mk obj.(γ) obj.(uid)
    (W64 $ length puts_hist) next_epoch obj.(serv) obj.(serv_is_good)) ∗
  "#Hhist" ∷ is_hist obj.(γ) obj.(serv).(Server.vrf_pk) obj.(uid)
    puts_hist next_epoch.

Lemma lookup_msv ptr_c c ep opt_pk γaudit aud_ep :
  c.(epochs_hist) !! (uint.nat ep) = Some opt_pk →
  (* it's hard to give tighter aud_ep bound, since a particular ep of
  epochs_hist might only be an msv with some later ep bound. *)
  Z.of_nat $ length c.(epochs_hist) <= uint.Z aud_ep →
  own ptr_c c -∗
  logical_audit c.(γ) γaudit c.(serv).(Server.vrf_pk) aud_ep -∗
  msv γaudit c.(serv).(Server.vrf_pk) ep c.(uid) opt_pk.
Proof.
  iIntros (Hlook ?) "H #Haudit". iNamed "H".
  ospecialize (Hhist_reln ep).
  rewrite /hist_epochs_puts.lookup_epochs Hlook in Hhist_reln.
  subst.
  iDestruct (hist_to_msv ep with "Hhist Haudit") as "$".
  { apply lookup_lt_Some in Hlook. word. }
  { word. }
Qed.

End defs.
End ClientHist.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_ClientHist__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        let len_diff := uint.Z ep - Z.of_nat (length c.(ClientHist.epochs_hist)) in
        let new_c := set ClientHist.epochs_hist (λ x, x ++
          replicate (Z.to_nat len_diff) (mjoin $ last x) ++
          [Some pk]) c in
        "%Hlt_diff" ∷ ⌜ len_diff >= 0 ⌝ ∗
        "%Hnoof_ep" ∷ ⌜ uint.Z $ word.add ep (W64 1) = (uint.Z ep + 1)%Z ⌝ ∗
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__Put with "[$Hcli $Hsl_pk]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; [by iFrame "∗#"|].
  iSplit; [word|].
  iSplit; [word|].
  iExists (puts_hist ++ [(ep, pk)]), (word.add ep (W64 1)).
  do 3 try iSplit; simpl in *.
  - rewrite !length_app length_replicate /=. word.
  - iPureIntro.
    rewrite (assoc (++)).
    apply hist_epochs_puts.update_new.
    { rewrite length_app length_replicate. word. }
    by apply hist_epochs_puts.update_replicate.
  - rewrite length_app /=.
    replace (W64 (_ + _)%nat) with
      (word.add (W64 $ length puts_hist) (W64 1)); [|word].
    iFrame.
  - iApply (hist_extend_put with "[$Hhist $His_put_post]"); word.
Qed.

Lemma wp_ClientHist__SelfMon ptr_c c :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        let new_len := uint.Z ep + 1 in
        let len_diff := new_len - Z.of_nat (length c.(ClientHist.epochs_hist)) in
        let new_c := set ClientHist.epochs_hist (λ x, x ++
          replicate (Z.to_nat len_diff) (mjoin $ last x)) c in
        "%Hlt_diff" ∷ ⌜ len_diff >= 0 ⌝ ∗
        "%Hnoof_ep" ∷ ⌜ new_len = uint.Z $ word.add ep (W64 1) ⌝ ∗
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__SelfMon with "[$Hcli]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; [by iFrame "∗#"|].
  iSplit; [word|].
  iSplit; [word|].
  iExists puts_hist, (word.add ep (W64 1)).
  do 3 try iSplit; simpl in *.
  - rewrite !length_app length_replicate. word.
  - iPureIntro.
    by apply hist_epochs_puts.update_replicate.
  - iFrame.
  - iApply (hist_extend_selfmon with "[$Hhist $His_selfmon_post]"); word.
Qed.

End proof.

Global Typeclasses Opaque ClientHist.own.
