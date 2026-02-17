From Perennial.Helpers Require Import List.
From New.golang.defn Require Export chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Export chan_au_base.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_init chan_au_send chan_au_recv.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Export pre.
From Perennial Require Import base.

Open Scope Z_scope.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.receive chan.send chan.for_range.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Global Instance pure_wp_chan_for_range (c : chan.t) elem_type (body : val) :
  PureWp True (chan.for_range elem_type #c body)%E
    ((for: (λ: <>, #true)%V; (λ: <>, #())%V :=
        λ: <>,
          let: ("v", "ok") := chan.receive elem_type #c in
          if: "ok" then
            body "v"
          else
            (* channel is closed *)
            break: #()
    )).
Proof using sem_fn + pre_sem + sem.
  iIntros (?????) "HΦ". unfold chan.for_range.
  wp_pure_lc "?". wp_pure. wp_pure. by iApply "HΦ".
Qed.

(* These are carefully ordered so that when the lemmas are applied, typeclass
   search can fill everything in. Do not change the order or add new things here
   without considering how it will affect TC search when lemmas are applied. *)
Context [ct dir t] [Hunder : ct ↓u go.ChannelType dir t].
Context [V] `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

Collection W := sem_fn + pre_sem + sem + IntoValTyped0.

Implicit Types (ch : loc) (v : V) (γ : chan_names).

Lemma wp_make2 (cap : w64) :
  {{{ ⌜ 0 ≤ sint.Z cap ⌝ }}}
    #(functions go.make2 [ct]) #cap
  {{{ ch γ, RET #ch;
      is_chan ch γ V ∗
      ⌜ chan_cap γ = cap ⌝ ∗
      own_chan γ V (if decide (cap = W64 0) then chanstate.Idle else chanstate.Buffered (@nil V))
  }}}.
Proof using W Hunder IntoValTyped0.
  wp_start as "%Hle".
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_make1 :
  {{{ True }}}
    #(functions go.make1 [ct]) #()
  {{{ ch γ, RET #ch;
      is_chan ch γ V ∗
      ⌜ chan_cap γ = W64 0 ⌝ ∗
      own_chan γ V chanstate.Idle
  }}}.
Proof using W Hunder IntoValTyped0.
  wp_start.
  wp_apply wp_make2; first done.
  iFrame.
Qed.

Lemma wp_send ch v γ:
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au γ v (Φ #())) -∗
  WP chan.send t #ch #v {{ Φ }}.
Proof using W.
  wp_start as "#Hch".
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au γ V (Φ #())) -∗
  WP #(functions go.close [ct]) #ch {{ Φ }}.
Proof using W Hunder.
  wp_start as "#Hch".
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ recv_au γ V (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive t #ch {{ Φ }}.
Proof using W.
  wp_start as "#Hch".
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

Lemma wp_cap ch γ :
  {{{ is_chan ch γ V }}}
    #(functions go.cap [ct]) #ch
  {{{ RET #(chan_cap γ); True }}}.
Proof using W Hunder.
  wp_start as "#Hch".
  wp_apply (wp_Cap with "[$Hch]").
  by iApply "HΦ".
Qed.

End proof.

Section select_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.
Local Set Default Proof Using "All".

(* The lemmas use Ψ because the original client-provided `send/recv_au` will
   have some specific postcondition predicate. We don't want to force the caller
   to transform that into a `send_au` of a different. So, these lemmas are
   written to take a wand that turns Ψ into Φ. *)
Local Lemma wp_try_comm_clause_blocking c Ψ :
  ∀ Φ,
  (match c with
   | CommClause (SendCase t send_chan_expr send_val) send_handler =>
       ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
     is_chan send_chan γ V ∗
     send_au γ v (WP send_handler {{ Ψ }})
   | CommClause (RecvCase t recv_chan_expr) recv_handler =>
       ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ recv_chan_expr = #recv_chan ⌝ ∗
     is_chan recv_chan γ V ∗
     recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }})
   end
  ) ∧ (Φ (#(), #false)%V) -∗
  (∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_comm_clause c #true {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ Hwand".
  wp_call. destruct c as [[|]]; simpl.
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V send_chan γ v' ? ? ?) "HΦ".
    iNamed "HΦ".
    iAssert (⌜ e = #v' ∧ ch = #send_chan ⌝ ∗ is_chan send_chan γ V)%I with "[-]" as "[[-> ->] #?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iMod "Hau". iModIntro. iNext. iNamed "Hau".
      iFrame. destruct s.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame. iIntros "H". iSpecialize ("Hcontinner" with "[$]").
        iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
        iIntros (v) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont"). iIntros (v) "HΦ".
        wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
    + wp_auto. iRight in "HΦ". done.
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V recv_chan γ ? ? ?) "HΦ".
    iAssert (⌜ ch = #recv_chan ⌝ ∗ is_chan recv_chan γ V)%I with "[-]" as "#[-> ?]".
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
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]"). iMod "Hcont". iModIntro.
        iMod "Hcont". iModIntro. iNext. iNamed "Hcont". iFrame.
        destruct s; try iFrame.
        -- iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
        -- destruct drain; try iFrame.
           iIntros "H". iSpecialize ("Hcontinner" with "[$]").
           iMod "Hcontinner". iModIntro. wp_auto. wp_apply (wp_wand with "Hcontinner").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * iFrame.
      * iFrame.
      * iFrame.
      * destruct drain.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
        -- iIntros "H". iSpecialize ("Hcont" with "[$]").
           iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
           iIntros (ret) "HΦ". wp_auto. iApply "Hwand". iFrame.
    + wp_auto. iRight in "HΦ". iFrame.
Qed.

Local Lemma wp_try_select_blocking (clauses : list comm_clause) :
  ∀ Ψ Φ,
  ([∧ list] c ∈ clauses,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_chan send_chan γ V ∗
        send_au γ v (WP send_handler {{ Ψ }})
     | CommClause (RecvCase t recv_chan_expr) recv_handler =>
         ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_chan recv_chan γ V ∗
        recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }})
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

Lemma wp_select_blocking (clauses : list comm_clause) :
  ∀ Φ,
  ([∧ list] c ∈ clauses,
     (match c with
      | CommClause (SendCase t send_chan_expr send_val) send_handler =>
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_chan send_chan γ V ∗
        send_au γ v (WP send_handler {{ Φ }})
     | CommClause (RecvCase t recv_chan_expr) recv_handler =>
         ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_chan recv_chan γ V ∗
        recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Φ }})
      end
     )) -∗
  WP SelectStmt (SelectStmtClausesV None clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH" forall (Φ).
  wp_apply wp_SelectStmt_blocking.
  iIntros (clauses') "%Hperm".
  wp_apply (wp_try_select_blocking with "[-]").
  - rewrite Hperm.
    iSplit; first iFrame.
    wp_auto. iApply "IH". iFrame.
  - iModIntro. iIntros "% HΦ". wp_auto. iFrame.
Qed.

Local Lemma wp_try_comm_clause_nonblocking c Ψ :
  ∀ Φ,
  (match c with
   | CommClause (SendCase t send_chan_expr send_val) send_handler =>
       ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
     is_chan send_chan γ V ∗
     nonblocking_send_au γ v (WP send_handler {{ Ψ }}) True
   | CommClause (RecvCase t recv_chan_expr) recv_handler =>
       ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ recv_chan_expr = #recv_chan ⌝ ∗
     is_chan recv_chan γ V ∗
     nonblocking_recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }}) True
   end
  ) ∧ (Φ (#(), #false)%V) -∗
  (∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_comm_clause c #false {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ Hwand".
  wp_call. destruct c as [[|]].
  - repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V send_chan γ v' ? ? ?) "HΦ".
    iAssert (⌜ e = #v' ∧ ch = #send_chan ⌝ ∗ is_chan send_chan γ V)%I with "[-]" as "[[-> ->] #?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iLeft. iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      iLeft in "Hau". iMod "Hau". iModIntro. iNext. iNamed "Hau".
      iFrame. destruct s.
      * iIntros "H". iSpecialize ("Hcont" with "[$]").
        iMod "Hcont". iModIntro. wp_auto. wp_apply (wp_wand with "Hcont").
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
    iDestruct "HΦ" as (V recv_chan γ ? ? ?) "HΦ".
    iAssert (⌜ ch = #recv_chan ⌝ ∗ is_chan recv_chan γ V)%I with "[-]" as "#[-> ?]".
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
      * destruct drain.
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
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_chan send_chan γ V ∗
        nonblocking_send_au γ v (WP send_handler {{ Ψ }}) True
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_chan recv_chan γ V ∗
        nonblocking_recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }}) True
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
          ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
        is_chan send_chan γ V ∗
        nonblocking_send_au γ v (WP send_handler {{ Φ }}) True
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ recv_chan_expr = #recv_chan ⌝ ∗
        is_chan recv_chan γ V ∗
        nonblocking_recv_au γ V (λ v ok, WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Φ }}) True
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

Local Lemma wp_try_select_case_nonblocking_alt c Ψ Ψnotready :
  ∀ P Φ,
  P -∗
  (match c with
   | CommClause (SendCase t send_chan_expr send_val) send_handler =>
       ∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
     is_chan send_chan γ V ∗
     nonblocking_send_au_alt γ v (P -∗ WP send_handler {{ Ψ }}) Ψnotready
  | CommClause (RecvCase t recv_chan_expr) recv_handler =>
      ∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
     ⌜ recv_chan_expr = #recv_chan ⌝ ∗
     is_chan recv_chan γ V ∗
     nonblocking_recv_au_alt γ V
       (λ v ok,
          P -∗ WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }}) Ψnotready
   end
  ) -∗
  ((∀ retv, Ψ retv -∗ Φ (retv, #true)%V) ∧ (P -∗ Ψnotready -∗ Φ (#(), #false)%V)) -∗
  WP chan.try_comm_clause c #false {{ Φ }}.
Proof.
  iIntros (P Φ) "HP HΦ Hwand".
  wp_call. destruct c as [[|]].
  - iNamed "HΦ". iDestruct "HΦ" as "([-> ->] & #? & Hau)". simpl. wp_auto.
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
  - iNamed "HΦ". iDestruct "HΦ" as "(-> & #? & Hau)". simpl. wp_auto.
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
    + destruct drain.
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
      * iIntros "H". iMod ("Hcont" with "[$] [$]") as "Hcont". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont").
        iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
Qed.

Local Lemma wp_try_select_nonblocking_alt Φnrs (clauses : list comm_clause) :
  ∀ P Ψ Φ,
  ([∗ list] c; Φnr ∈ clauses; Φnrs,
     match c with
     | CommClause (SendCase t send_chan_expr send_val) send_handler =>
         (∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
             ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
             is_chan send_chan γ V ∗
             nonblocking_send_au_alt γ v (P -∗ WP send_handler {{ Ψ }}) Φnr)
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          (∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
              ⌜ recv_chan_expr = #recv_chan ⌝ ∗
              is_chan recv_chan γ V ∗
              nonblocking_recv_au_alt γ V
                (λ v ok, P -∗ WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Ψ }}) Φnr)
     end) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ (Φ (#(), #false)%V)) -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select false clauses {{ Φ }}.
Proof.
  simpl. iIntros (P Ψ Φ) "HΦ HP Hwandnr #Hwand".
  iLöb as "IH" forall (clauses Φnrs).
  destruct clauses.
  { wp_auto. iDestruct (big_sepL2_nil_inv_l with "HΦ") as %?. subst.
    iApply ("Hwandnr" with "[$]"). done. }
  simpl.
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
Lemma wp_select_nonblocking_alt Φnrs P (clauses : list comm_clause) (def : expr) :
  ∀ Φ,
  ([∗ list] c; Φnr ∈ clauses; Φnrs,
     match c with
     | CommClause (SendCase t send_chan_expr send_val) send_handler =>
         (∃ V send_chan γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
             ⌜ send_val = #v ∧ send_chan_expr = #send_chan ⌝ ∗
             is_chan send_chan γ V ∗
             nonblocking_send_au_alt γ v (P -∗ WP send_handler {{ Φ }}) Φnr)
      | CommClause (RecvCase t recv_chan_expr) recv_handler =>
          (∃ V recv_chan γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
              ⌜ recv_chan_expr = #recv_chan ⌝ ∗
              is_chan recv_chan γ V ∗
              nonblocking_recv_au_alt γ V
                (λ v ok, P -∗ WP (subst "$recvVal" (#v, #ok) recv_handler) {{ Φ }}) Φnr)
     end) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ WP def {{ Φ }}) -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases HP Hdef".
  wp_apply wp_SelectStmt_nonblocking.
  iIntros (clauses') "%Hperm".
  iDestruct (big_sepL2_alt with "Hcases") as "[%Hlen Hcases]".
  destruct (permutation_zip clauses clauses' Φnrs) as [Φnrs' [Hperm_Φnrs Hperm_zip]]; [done|done|].
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
