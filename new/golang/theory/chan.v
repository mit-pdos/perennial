From New.golang.defn Require Export chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base chan_au_send chan_au_recv.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Import exception list mem loop typing struct proofmode pkg auto.
From Perennial Require Import base.

Open Scope Z_scope.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.for_range chan.select_nonblocking chan.select_blocking.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_make (cap: Z) {B: BoundedTypeSize t} :
  0 ≤ cap < 2^63 ->
  {{{ True }}}
    chan.make #t #(W64 cap)
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch cap γ ∗
      own_channel ch cap (if decide (cap = 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  intros Hcap.
  wp_start.
  wp_call.
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_send (ch: loc) (cap: Z) (v: V) (γ: chan_names):
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch cap v γ (Φ #())) -∗
  WP chan.send #t #ch #v {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close (ch: loc) (cap: Z) (γ: chan_names):
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch cap γ (Φ #())) -∗
  WP chan.close #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive (ch: loc) (cap: Z) (γ: chan_names) :
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ rcv_au_slow ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

Lemma wp_cap (ch: loc) (cap: Z) (γ: chan_names) :
  {{{ is_channel ch cap γ }}}
    chan.cap #t #ch
  {{{ RET #(W64 cap); True }}}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Cap with "[$Hch]").
  by iApply "HΦ".
Qed.

End proof.

Section select_proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Inductive op :=
| select_send_f (t: go_type) (v : val) (ch : chan.t) (handler : func.t)
| select_receive_f (t: go_type) (ch : chan.t) (handler : func.t).

Global Instance into_val_op : IntoVal op :=
  {|
    to_val_def := λ o,
        match o with
        | select_send_f t v ch f => InjLV (#t, #ch, v, #f)
        | select_receive_f t ch f => InjRV (#t, #ch, #f)
        end
  |}.

Global Instance wp_select_send `{!IntoVal V} `{!IntoValTyped V t} ch (v : val) f :
  PureWp True (chan.select_send #t #ch v #f)
    #(select_send_f t v ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Global Instance wp_select_receive `{!IntoVal V} `{!IntoValTyped V t} ch f :
  PureWp True (chan.select_receive #t #ch #f)
    #(select_receive_f t ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Lemma wp_try_select_case_blocking cs :
  ∀ Ψ Φ,
  (match cs with
   | select_send_f t send_val send_chan send_handler =>
       ∃ cap V γ (v : V) `(!IntoVal V) `(!chanGhostStateG Σ V) `(!IntoValTyped V t),
     ⌜ send_val = #v ⌝ ∗
     is_channel (V:=V) (t:=t) send_chan cap γ ∗
     send_au_slow send_chan cap v γ (WP #send_handler #() {{ Ψ }})
  | select_receive_f t recv_chan recv_handler =>
      ∃ cap γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanGhostStateG Σ V),
     is_channel (V:=V) (t:=t) recv_chan cap γ ∗
     rcv_au_slow recv_chan cap γ (λ (v: V) ok,
                                    WP #recv_handler (#v, #ok)%V {{ Ψ }})
   end
   ) -∗
  (∀ v, Ψ v -∗ Φ (v, #true)%V) ∧
  (match cs with
   | select_send_f t send_val send_chan send_handler =>
       ∃ cap V γ (v : V) `(!IntoVal V) `(!chanGhostStateG Σ V) `(!IntoValTyped V t),
     ⌜ send_val = #v ⌝ ∗
     is_channel (V:=V) (t:=t) send_chan cap γ ∗
     send_au_slow send_chan cap v γ (WP #send_handler #() {{ Ψ }})
  | select_receive_f t recv_chan recv_handler =>
      ∃ cap γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanGhostStateG Σ V),
     is_channel (V:=V) (t:=t) recv_chan cap γ ∗
     rcv_au_slow recv_chan cap γ (λ (v: V) ok,
                                    WP #recv_handler (#v, #ok)%V {{ Ψ }})
   end -∗ Φ (#(), #false)%V
  ) -∗
  WP chan.try_select_case #cs #true {{ Φ }}.
Proof.
  iIntros (Ψ Φ) "HΨ HΦ".
  wp_call. rewrite [in (_ op)]to_val_unseal /=. destruct cs; wp_auto.
  - iNamed "HΨ". iDestruct "HΨ" as "(-> & #? & Hau)".
    (* FIXME: TrySend spec forces wp_frame_wand to reuse Φ in both cases.  *)
    iApply (wp_frame_wand with "[HΦ]"); first iNamedAccu.
    wp_apply (wp_TrySend with "[$] [-] []").
    + iSplitL "Hau"; first iExact "Hau".
      iIntros "Hau". iMod "Hau". iModIntro. iNext.
      iNamed "Hau". iFrame. destruct s.
      * case_decide.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto.
           wp_apply (wp_wand with "Hcont").
           iIntros (?) "HΨ". wp_auto. iNamed 1. by iApply "HΦ".
        -- iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame. iIntros "H". iSpecialize ("Hcontinner" with "[$]").
        (* FIXME: naming: "continner"? *)
        iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
        iIntros (v) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
      * iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont"). iIntros (v) "HΨ".
        wp_auto. iNamed 1. iApply "HΦ". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
    + iIntros "Hau". wp_auto. iNamed 1. iApply "HΦ". iFrame "∗#%".  done.
  - (* FIXME: only get `V : Type` after deciding to fire the update now. *)
    iNamed "HΨ". iDestruct "HΨ" as "(#? & Hau)".
    (* FIXME: TrySend spec forces wp_frame_wand to reuse Φ in both cases.  *)
    iApply (wp_frame_wand with "[HΦ]"); first iNamedAccu.
    wp_apply (wp_TryReceive with "[$] [-] []").
    + iSplitL "Hau"; first iExact "Hau".
      iIntros "Hau". iMod "Hau". iModIntro. iNext.
      iNamed "Hau". iFrame. destruct s.
      * destruct buff.
        -- iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto.
           wp_apply (wp_wand with "Hcont").
           iIntros (?) "HΨ". wp_auto. iNamed 1. by iApply "HΦ".
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame.
        -- iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
           iIntros (ret) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
        -- destruct draining; try iFrame.
           iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
           iIntros (ret) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (ret) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
      * destruct draining.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΨ". wp_auto. iNamed 1. iApply "HΦ". iFrame.
    + iIntros "Hau". wp_auto. iNamed 1. iApply "HΦ". iFrame "∗#".
Qed.

Local Lemma wp_try_select_blocking P (cases : list op) :
  ∀ Φ,
  □(P -∗ ([∧ list] case ∈ cases,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         ∃ cap V γ (v : V) `(!IntoVal V) `(!chanGhostStateG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan cap γ ∗
             send_au_slow send_chan cap v γ (WP #send_handler #() {{ Φ }})
     | select_receive_f t recv_chan recv_handler =>
         ∃ cap γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanGhostStateG Σ V),
             is_channel (V:=V) (t:=t) recv_chan cap γ ∗
             rcv_au_slow recv_chan cap γ (λ (v: V) ok,
               WP #recv_handler (#v, #ok)%V {{ Φ }})
     end
  )) -∗
  P -∗
  (P -∗ Φ #false) -∗
  WP chan.try_select #cases #true {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases HP HΦfalse".
  assert (∃ Ψ, Φ = Ψ) as [Ψ Heq] by by eexists.
  iEval (rewrite Heq). iEval (rewrite Heq) in "HΦfalse". clear Heq.
  iLöb as "IH" forall (Ψ cases).
  wp_call.
  destruct cases.
  { wp_auto. by iApply "HΦfalse". }
  wp_auto.
  wp_call. rewrite [in #o]to_val_unseal /=. destruct o; wp_auto.
  -
  destruct cs; wp_auto.
  wp_apply (wp_do_select_case_blocking with "[Hcases] HP").
  {
    iIntros "P". iSpecialize ("Hcases" with "P").
    simpl. iDestruct "Hcases" as "[Hcase _]". admit.
  }
  { iIntros "HP". wp_auto. iApply "IH". }
  { i }
  wp_bind
Qed.

(* FIXME: rename fast and slow. *)
Lemma wp_select_blocking (cases : list op) :
  ∀ Φ,
  ([∧ list] case ∈ cases,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         ∃ cap V γ (v : V) `(!IntoVal V) `(!chanGhostStateG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan cap γ ∗
             send_au_slow send_chan cap v γ (WP #send_handler #() {{ Φ }})
     | select_receive_f t recv_chan recv_handler =>
         ∃ cap γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanGhostStateG Σ V),
             is_channel (V:=V) (t:=t) recv_chan cap γ ∗
             rcv_au_slow recv_chan cap γ (λ (v: V) ok,
               WP #recv_handler (#v, #ok)%V {{ Φ }})
     end
  ) -∗
  WP chan.select_blocking #cases {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH" forall (Φ).
  wp_call. wp_bind. iLöb as "IHtry" forall . wp_call.
  destruct cases.
  { wp_auto. wp_apply ("IH" with "[$]"). }
  wp_auto.
  wp_apply "IHtry".
  wp_bind

Admitted.

(* FIXME: what precondition for default case? *)
Lemma wp_select_nonblocking (cases : list op) (def: func.t) :
  ∀ Φ,
  ([∧ list] case ∈ cases,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         ∃ cap V γ (v : V) `(!IntoVal V) `(!chanGhostStateG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan cap γ ∗
             send_au_fast send_chan cap v γ (WP #send_handler #() {{ Φ }})
     | select_receive_f t recv_chan recv_handler =>
         ∃ cap γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanGhostStateG Σ V),
             is_channel (V:=V) (t:=t) recv_chan cap γ ∗
             rcv_au_fast recv_chan cap γ (λ (v: V) ok,
               WP #recv_handler #v {{ Φ }})
     end
  ) ∧ WP #def #() {{ Φ }} -∗
  WP chan.select_nonblocking #cases #def {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  wp_call.
Admitted.

End proof.

End chan.
