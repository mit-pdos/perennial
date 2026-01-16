From Perennial.Helpers Require Import List.
From New.golang.defn Require Export chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_init chan_au_base chan_au_send chan_au_recv.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Export exception loop proofmode.
From Perennial Require Import base.

Open Scope Z_scope.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.receive chan.send chan.for_range.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics} {slice_sem : go.SliceSemantics} {chan_sem : go.ChanSemantics}.
Local Set Default Proof Using "All".

Context `[!chanG Σ V].
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t] `[!go.TypeRepr t V].

Lemma wp_make (cap : w64) dir :
  {{{ ⌜ 0 ≤ sint.Z cap ⌝ }}}
    #(functions go.make2 [go.ChannelType dir t]) #cap
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch γ ∗
      ⌜chan_cap γ = sint.Z cap⌝ ∗
      own_channel ch (if decide (cap = 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  wp_start as "%Hle".
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_send (ch: loc) (v: V) (γ: chan_names):
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch v γ (Φ #())) -∗
  WP chan.send t #ch #v {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close (ch: loc) (γ: chan_names) dir :
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch γ (Φ #())) -∗
  WP #(functions go.close [go.ChannelType dir t]) #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive (ch: loc) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ rcv_au_slow ch γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

Lemma wp_cap (ch: loc) (γ: chan_names) dir :
  {{{ is_channel ch γ }}}
    #(functions go.cap [go.ChannelType dir t]) #ch
  {{{ RET #(chan_cap γ); True }}}.
Proof.
  wp_start as "#Hch".
  wp_apply (wp_Cap with "[$Hch]").
  by iApply "HΦ".
Qed.

End proof.

Section select_proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics} {slice_sem : go.SliceSemantics} {chan_sem : go.ChanSemantics}.
Local Set Default Proof Using "All".

(* The lemmas use Ψ because the original client-provided `send/rcv_au_slow` will
   have some specific postcondition predicate. We don't want to force the caller
   to transform that into a `send_au_slow` of a different. So, these lemmas are
   written to take a wand that turns Ψ into Φ. *)
Local Lemma wp_try_comm_clause_blocking c Ψ :
  ∀ Φ,
  (match c with
   | CommClause (SendCase t send_chan_expr send_val) send_handler =>
       ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
         `(!go.TypeRepr t V) `(!chanG Σ V),
     ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
     is_channel (V:=V) send_chan γ ∗
     send_au_slow send_chan v γ (WP send_handler {{ Ψ }})
   | CommClause (RecvCase t recv_chan_expr) recv_handler =>
       ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
         `(!go.TypeRepr t V),
     ⌜ recv_chan_expr = #recv_chan ⌝ ∗
     is_channel (V:=V) recv_chan γ ∗
     rcv_au_slow recv_chan γ (λ (v: V) ok,
                                WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Ψ }})
   end
  ) ∧ (Φ (#(), #false)%V) -∗
  (∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_comm_clause c #true {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ Hwand".
  wp_call. destruct c as [[|]]; simpl.
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V send_chan γ v' ? ? ? ? ?) "HΦ".
    iNamed "HΦ".
    iAssert (⌜ e = #v' ∧ ch = #send_chan ⌝ ∗ is_channel send_chan γ)%I with "[-]" as "[[-> ->] #?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iMod "Hau". iModIntro. iNext. iNamed "Hau".
      iFrame. destruct s.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_bind (body).
        iApply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame. iIntros "H". iSpecialize ("Hcontinner" with "[$]").
        iMod "Hcontinner". iModIntro. wp_auto. wp_bind (body). iApply (wp_wand with "Hcontinner").
        iIntros (v) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        wp_auto. wp_bind body. iApply (wp_wand with "Hcont"). iIntros (v) "HΦ".
        wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
    + wp_auto. iRight in "HΦ". done.
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V recv_chan γ ? ? ? ? ?) "HΦ".
    iAssert (⌜ ch = #recv_chan ⌝ ∗ is_channel recv_chan γ)%I with "[-]" as "#[-> ?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TryReceive with "[$]").
    iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iMod "Hau". iModIntro. iNext.
      iNamed "Hau". iFrame. destruct s.
      * destruct buff.
        -- iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_bind (subst _ _ _).
           iApply (wp_wand with "Hcont").
           iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame.
        -- iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_bind (subst _ _ _).
           iApply (wp_wand with "Hcontinner").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
        -- destruct draining; try iFrame.
           iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_bind (subst _ _ _).
           iApply (wp_wand with "Hcontinner").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_bind (subst _ _ _). iApply (wp_wand with "Hcont").
        iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
      * destruct draining.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_bind (subst _ _ _). iApply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_bind (subst _ _ _). iApply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
    + wp_auto. iRight in "HΦ". iFrame.
Qed.

Local Lemma wp_try_select_blocking (clauses : list comm_clause) :
  ∀ Ψ Φ,
  ([∧ list] c ∈ clauses,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
            `(!go.TypeRepr t V) `(!chanG Σ V),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_channel (V:=V) send_chan γ ∗
        send_au_slow send_chan v γ (WP send_handler {{ Ψ }})
     | CommClause (RecvCase t recv_chan_expr) recv_handler =>
         ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
           `(!go.TypeRepr t V),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_channel (V:=V) recv_chan γ ∗
        rcv_au_slow recv_chan γ (λ (v: V) ok,
                                   WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Ψ }})
      end
  )) ∧ (Φ (#(), #false)%V) -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select true clauses {{ Φ }}.
Proof.
  simpl. iIntros (Ψ Φ) "HΦ #Hwand".
  iLöb as "IH" forall (clauses).
  destruct clauses.
  { wp_auto. iRight in "HΦ". iApply "HΦ". }
  simpl.
  wp_apply (wp_try_comm_clause_blocking _ Ψ with "[-Hwand] [Hwand]").
  2:{ iIntros (?) "HΨ". wp_auto. iApply "Hwand". iFrame. }
  iSplit.
  { simpl. iLeft in "HΦ". iLeft in "HΦ". iFrame. }
  wp_auto. iApply ("IH" with "[HΦ]"); try iFrame.
  iSplit.
  - iLeft in "HΦ". simpl. iRight in "HΦ". iFrame.
  - iRight in "HΦ". done.
Qed.

Local Lemma wp_SelectStmt_blocking {stk E} clauses Φ :
  (∀ clauses',
     ⌜ clauses' ≡ₚ clauses ⌝ -∗
     WP (let: ("v", "succeeded") := chan.try_select true clauses' in
          if: "succeeded" then "v"
          else (λ: <>, SelectStmt (SelectStmtClauses None clauses))%V #()) @ stk; E {{ Φ }}
  ) -∗
  WP SelectStmt (SelectStmtClausesV None clauses) @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_apply (wp_GoInstruction []).
  { intros. eexists. repeat econstructor. erewrite go.chan_select_blocking.
    exists clauses; split; done. }
  simpl. iIntros "* %Hstep". rewrite go.chan_select_blocking in Hstep.
  destruct Hstep as [[? []]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

(* FIXME: rename fast and slow. *)
Lemma wp_select_blocking (clauses : list comm_clause) :
  ∀ Φ,
  ([∧ list] c ∈ clauses,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
            `(!go.TypeRepr t V) `(!chanG Σ V),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_channel (V:=V) send_chan γ ∗
        send_au_slow send_chan v γ (WP send_handler {{ Φ }})
     | CommClause (RecvCase t recv_chan_expr) recv_handler =>
         ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
           `(!go.TypeRepr t V),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_channel (V:=V) recv_chan γ ∗
        rcv_au_slow recv_chan γ (λ (v: V) ok,
                                   WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Φ }})
      end
     )) -∗
  WP SelectStmt (SelectStmtClausesV None clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH" forall (Φ).
  wp_apply wp_SelectStmt_blocking.
  iIntros (clauses') "%Hperm".
  wp_bind (chan.try_select _ _). iApply (wp_try_select_blocking with "[-]").
  - rewrite Hperm.
    iSplit; first iFrame.
    wp_auto. iApply "IH". iFrame.
  - iModIntro. iIntros "% HΦ". wp_auto. iFrame.
Qed.

Local Lemma wp_try_comm_clause_nonblocking c Ψ :
  ∀ Φ,
  (match c with
   | CommClause (SendCase t send_chan_expr send_val) send_handler =>
       ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
         `(!go.TypeRepr t V) `(!chanG Σ V),
     ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
     is_channel (V:=V) send_chan γ ∗
     send_au_fast send_chan v γ (WP send_handler {{ Ψ }}) True
   | CommClause (RecvCase t recv_chan_expr) recv_handler =>
       ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
         `(!go.TypeRepr t V),
     ⌜ recv_chan_expr = #recv_chan ⌝ ∗
     is_channel (V:=V) recv_chan γ ∗
     rcv_au_fast recv_chan γ (λ (v: V) ok,
                                WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Ψ }}) True
   end
  ) ∧ (Φ (#(), #false)%V) -∗
  (∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_comm_clause c #false {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ Hwand".
  wp_call. destruct c as [[|]].
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V send_chan γ v' ? ? ? ? ?) "HΦ".
    iAssert (⌜ e = #v' ∧ ch = #send_chan ⌝ ∗ is_channel send_chan γ)%I with "[-]" as "[[-> ->] #?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iLeft. iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iLeft in "Hau". iMod "Hau". iModIntro. iNext. iNamed "Hau".
      iFrame. destruct s.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_bind body.
        wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * done.
      * done.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont"). iIntros "% HΨ". wp_auto.
        iApply "Hwand". done.
      * done.
      * done.
      * done.
    + wp_auto. iRight in "HΦ". done.
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V recv_chan γ ? ? ? ? ?) "HΦ".
    iAssert (⌜ ch = #recv_chan ⌝ ∗ is_channel recv_chan γ)%I with "[-]" as "#[-> ?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TryReceive with "[$]").
    iLeft. iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iLeft in "Hau". iMod "Hau". iModIntro. iNext.
      iNamed "Hau". iFrame. destruct s.
      * destruct buff.
        -- iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto.
           wp_apply (wp_wand with "Hcont").
           iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * done.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont"). iIntros "% HΨ". wp_auto.
        iApply "Hwand". done.
      * done.
      * done.
      * done.
      * destruct draining.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
    + wp_auto. iRight in "HΦ". iFrame.
Qed.

Local Lemma wp_try_select_nonblocking (clauses : list comm_clause) :
  ∀ Ψ Φ,
  ([∧ list] c ∈ clauses ,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
            `(!go.TypeRepr t V) `(!chanG Σ V),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_channel (V:=V) send_chan γ ∗
        send_au_fast send_chan v γ (WP send_handler {{ Ψ }}) True
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
            `(!go.TypeRepr t V),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_channel (V:=V) recv_chan γ ∗
        rcv_au_fast recv_chan γ (λ (v: V) ok,
                                   WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Ψ }}) True
      end
  )) ∧ Φ (#(), #false)%V -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select false clauses {{ Φ }}.
Proof.
  simpl. iIntros (Ψ Φ) "HΦ #Hwand".
  iLöb as "IH" forall (clauses).
  destruct clauses.
  { wp_auto. iRight in "HΦ". iApply "HΦ". }
  simpl.
  wp_apply (wp_try_comm_clause_nonblocking _ Ψ with "[-Hwand] [Hwand]").
  2:{ iIntros (?) "HΨ". wp_auto. iApply "Hwand". iFrame. }
  iSplit.
  { simpl. iLeft in "HΦ". iLeft in "HΦ". iFrame. }
  wp_auto. wp_apply ("IH" with "[HΦ]"); try iFrame.
  iSplit.
  - iLeft in "HΦ". simpl. iRight in "HΦ". iFrame.
  - iRight in "HΦ". done.
Qed.

Local Lemma wp_SelectStmt_nonblocking {stk E} (def : expr) clauses Φ :
  (∀ clauses' : list comm_clause,
     ⌜clauses' ≡ₚ clauses⌝ -∗
     WP (let: "__p" := chan.try_select false clauses' in
         let: "v" := Fst "__p" in
         let: "succeeded" := Snd "__p" in
         if: "succeeded" then "v" else (λ: <>, def)%V #()) @ stk; E {{ v, Φ v }}) -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_apply (wp_GoInstruction []).
  { intros. eexists. repeat econstructor. erewrite go.chan_select_nonblocking.
    exists clauses; split; done. }
  simpl. iIntros "* %Hstep". rewrite go.chan_select_nonblocking in Hstep.
  destruct Hstep as [[? []]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_select_nonblocking (clauses : list comm_clause) def :
  ∀ Φ,
  ([∧ list] c ∈ clauses,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t)
            `(!go.TypeRepr t V) `(!chanG Σ V),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_channel (V:=V) send_chan γ ∗
        send_au_fast send_chan v γ (WP send_handler {{ Φ }}) True
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t) `(!chanG Σ V)
            `(!go.TypeRepr t V),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_channel (V:=V) recv_chan γ ∗
        rcv_au_fast recv_chan γ (λ (v: V) ok,
                                   WP (subst "$ok" #ok (subst "$v" #v recv_handler)) {{ Φ }}) True
      end
  )) ∧ WP def {{ Φ }} -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH" forall (Φ).
  wp_apply wp_SelectStmt_nonblocking.
  iIntros (clauses') "%Hperm".
  wp_apply (wp_try_select_nonblocking with "[-]").
  - rewrite Hperm.
    iSplit.
    + iLeft in "Hcases". iFrame.
    + iRight in "Hcases". wp_auto. iFrame.
  - iModIntro. iIntros "% HΦ". wp_auto. iFrame.
Qed.

Local Lemma wp_try_select_case_nonblocking_alt cs Ψ Ψnotready :
  ∀ P Φ,
  P -∗
  (match cs with
   | select_send_f t send_val send_chan send_handler =>
       ∃ V γ (v : V) `(!IntoVal V) `(!chanG Σ V) `(!IntoValTyped V t),
     ⌜ send_val = #v ⌝ ∗
     is_channel (V:=V) (t:=t) send_chan γ ∗
     send_au_fast_alt send_chan v γ (P -∗ WP #send_handler #() {{ Ψ }}) Ψnotready
  | select_receive_f t recv_chan recv_handler =>
      ∃ V γ `(!IntoVal V) `(!IntoValTyped V t) `(!chanG Σ V),
     is_channel (V:=V) (t:=t) recv_chan γ ∗
     rcv_au_fast_alt recv_chan γ
       (λ (v: V) ok, P -∗ WP #recv_handler (#v, #ok)%V {{ Ψ }}) Ψnotready
   end
  ) -∗
  ((∀ retv, Ψ retv -∗ Φ (retv, #true)%V) ∧ (P -∗ Ψnotready -∗ Φ (#(), #false)%V)) -∗
  WP chan.try_select_case #cs #false {{ Φ }}.
Proof.
  iIntros (P Φ) "HP HΦ Hwand".
  wp_call. rewrite [in (_ op)]to_val_unseal /=. destruct cs; wp_auto.
  - iNamed "HΦ". iDestruct "HΦ" as "(-> & #? & Hau)".
    wp_apply (wp_TrySend with "[$]").
    iRight.
    iMod "Hau". iModIntro. iNext. iNamed "Hau".
    iFrame. destruct s.
    + destruct decide.
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro. wp_auto.
        wp_apply (wp_wand with "Hcont"). iIntros (?) "HΨ".
        iLeft in "Hwand". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iMod ("Hcont" with "[$]") as "Hcont". iModIntro. wp_auto.
        iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$]") as "Hcont". iModIntro. wp_auto.
      iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$]") as "Hcont". iModIntro. wp_auto.
      iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro. wp_auto.
      wp_apply (wp_wand with "Hcont"). iIntros (?) "HΨ".
      iLeft in "Hwand". wp_auto. iApply "Hwand". iFrame.
    + iIntros "H". iMod ("Hcont" with "[$]") as "Hcont". iModIntro. wp_auto.
      iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$]") as "Hcont". iModIntro. wp_auto.
      iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + done.
  - iNamed "HΦ". iDestruct "HΦ" as "(#? & Hau)".
    wp_apply (wp_TryReceive with "[$]").
    iRight.
    iMod "Hau". iModIntro. iNext.
    iNamed "Hau". iFrame. destruct s.
    + destruct buff.
      * iIntros "H". iMod ("Hcont" with "[$]"). iModIntro.
        wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + iIntros "H". iMod ("Hcont" with "[$]"). iModIntro.
      wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
      wp_auto. wp_apply (wp_wand with "Hcont").
      iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + iIntros "H". iMod ("Hcont" with "[$]"). iModIntro.
      wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$]"). iModIntro.
      wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + iIntros "H". iMod ("Hcont" with "[$]"). iModIntro.
      wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$] [$]").
    + destruct draining.
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
Qed.

Local Lemma wp_try_select_nonblocking_alt Φnrs (cases : list op) :
  ∀ P Ψ Φ,
  ([∗ list] case; Φnr ∈ cases; Φnrs,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         (∃ V γ (v : V) `(!IntoVal V) `(!chanG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan γ ∗
             send_au_fast_alt send_chan v γ (P -∗ WP #send_handler #() {{ Ψ }})
               Φnr)
     | select_receive_f t recv_chan recv_handler =>
         (∃ V γ `(!IntoVal V) `(!IntoValTyped V t) `(!chanG Σ V),
             is_channel (V:=V) (t:=t) recv_chan γ ∗
             rcv_au_fast_alt recv_chan γ
               (λ (v: V) ok, P -∗ WP #recv_handler (#v, #ok)%V {{ Ψ }}) Φnr)
     end) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ (Φ (#(), #false)%V)) -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select #cases #false {{ Φ }}.
Proof.
  simpl. iIntros (P Ψ Φ) "HΦ HP Hwandnr #Hwand".
  iLöb as "IH" forall (cases Φnrs).
  wp_call.
  destruct cases.
  { wp_auto. iDestruct (big_sepL2_nil_inv_l with "HΦ") as %?. subst.
    iApply ("Hwandnr" with "[$]"). done. }
  wp_auto.
  iDestruct (big_sepL2_cons_inv_l with "HΦ") as (Φnr Φnrs' Heq) "[H HΦ]". subst.
  wp_apply (wp_try_select_case_nonblocking_alt _ Ψ with "HP [H]").
  { simpl. iFrame. }
  iSplit.
  - iIntros "% HΨ". wp_auto. iApply "Hwand". iFrame.
  - iIntros "HP Hnr". wp_auto.
    wp_apply ("IH" with "[HΦ] [$]"); try iFrame.
    simpl. iIntros "P Hnrs". iApply ("Hwandnr" with "[$] [$]").
Qed.

(** This specification requires proving _separate_ atomic updates for each case,
    and requires a proposition [P] to represent the resources that are available
    to ALL of the handlers (rather than having to be split up among the cases).
    Users should do:
     wp_apply (wp_select_nonblocking_alt [Φnr1; Φnr2;] with
               "[list of props for proving atomic updates] [-]"); [|iNamedAccu|].

    The reason this uses [au1 ∗ au2 ∗ ...] instead of [au1 ∧ au2 ∧ ...] is
    because in the event that the default case is chosen, ALL of the case's
    atomic updates will have to be fired to produce witnesses that all the cases
    were not ready ([[∗] Φnrs]). *)
Lemma wp_select_nonblocking_alt Φnrs P (cases : list op) (def: func.t) :
  ∀ Φ,
  ([∗ list] case; Φnr ∈ cases; Φnrs,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         (∃ V γ (v : V) `(!IntoVal V) `(!chanG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan γ ∗
             send_au_fast_alt send_chan v γ (P -∗ WP #send_handler #() {{ Φ }}) Φnr)
     | select_receive_f t recv_chan recv_handler =>
         (∃ V γ `(!IntoVal V) `(!IntoValTyped V t) `(!chanG Σ V),
             is_channel (V:=V) (t:=t) recv_chan γ ∗
             rcv_au_fast_alt recv_chan γ
               (λ (v: V) ok, P -∗ WP #recv_handler (#v, #ok)%V {{ Φ }}) Φnr)
     end) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ WP #def #() {{ Φ }}) -∗
  WP chan.select_nonblocking #cases #def {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases HP Hdef".
  wp_call.
  wp_apply wp_list_Shuffle.
  iIntros (cases') "%Hperm".
  iDestruct (big_sepL2_alt with "Hcases") as "[%Hlen Hcases]".
  destruct (permutation_zip cases cases' Φnrs) as [Φnrs' [Hperm_Φnrs Hperm_zip]]; [done|done|].
  rewrite Hperm_zip.
  rewrite Hperm_Φnrs.
  wp_apply (wp_try_select_nonblocking_alt with "[Hcases] HP [Hdef]").
  - iApply big_sepL2_alt.
    iFrame "Hcases".
    apply Permutation_length in Hperm, Hperm_Φnrs.
    iPureIntro. lia.
  - iIntros "HP Hnrs". wp_auto. iApply ("Hdef" with "[$] [$]").
  - iModIntro. iIntros. wp_auto. iFrame.
Qed.

End select_proof.

End chan.
