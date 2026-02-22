Require Export New.code.go_etcd_io.etcd.server.v3.etcdserver.

Require Export New.generatedproof.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.proof.proof_prelude.
From New.proof Require Import context log fmt time
  go_etcd_io.etcd.pkg.v3.idutil
  go_etcd_io.etcd.pkg.v3.wait
  go_etcd_io.etcd.api.v3.etcdserverpb
  go_etcd_io.raft.v3.

Existing Instance channel.Channel_underlying.
Definition x := @etcdserver.zapRaftLogger_underlying.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.
Existing Instance x. Existing Instance x. Existing Instance x. Existing Instance x.

Section instance1.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}
  {go_lctx : GoLocalContext} {sem : go.Semantics}.
Global Instance z T :
  channel.Channel T <u channel.Channelⁱᵐᵖˡ T | 2.
Proof using.
  intros.
  Existing Instance channel.Channel_underlying.
  Existing Instance x.
  Existing Instance x.
  Set Debug "tactic-unification".
  (* Opaque channel.Channel. *)
  Time Fail apply _; [|].
  About id_byte_string.
  (* Time simple eapply @channel.Channel_underlying. *)
Qed.
End instance1.

Section instance2.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}
  {go_lctx : GoLocalContext} {sem : go.Semantics}.
Instance w T :
  channel.Channel T <u channel.Channelⁱᵐᵖˡ T | 2.
Proof using.
  Set Typeclasses Debug.
  intros.
  Print Hint.
  Time apply _.
  (* Time simple eapply @channel.Channel_underlying. *)
Qed.
End instance1.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : etcdserver.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) proto := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) proto := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) proto := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) traceutil := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) pkg_id.apply := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) pkg_id.auth := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) wait := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) prometheus := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) errors.pkg_id.errors := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit (iProp Σ) config := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit (iProp Σ) etcdserver := define_is_pkg_init True%I.

Lemma wp_EtcdServer__Put (s : loc) ctx (r : loc) :
  {{{ is_pkg_init etcdserver }}}
    s @! (go.PointerType etcdserver.EtcdServer) @! "Put" #(interface.ok ctx) #r
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_bind.
  (* Need to translate traceutil.StartTimeKey. so struct literal can be allocated *)
Abort.

Axiom EtcdServer_names : Type.
Axiom raft_gn : EtcdServer_names → raft_names.
Implicit Type γ : EtcdServer_names.

Definition waitR (id' : w64) v : iProp Σ :=
  (⌜ v = interface.nil ⌝) ∨
    ∃ res_ptr (res : apply.Result.t),
      ⌜ v = interface.mk_ok (apply.Result) #res_ptr ⌝ ∗ res_ptr ↦ res.

Axiom own_ID : ∀ γ (i : w64), iProp Σ.
Axiom own_EtcdServer : ∀ (s : loc) γ, iProp Σ.
#[local] Axiom is_EtcdServer_internal : ∀ (s : loc) γ, iProp Σ.
Axiom own_EtcdServer_access : ∀ s γ,
  own_EtcdServer s γ -∗
  ∃ (reqIDGen : loc) (MaxRequestBytes : w64) w γw rn,
    "#reqIDGen" ∷ s .[etcdserver.EtcdServer.t, "reqIDGen"] ↦□ reqIDGen ∗
    "#HreqIDGen" ∷ is_Generator reqIDGen (own_ID γ) ∗
    "#Cfg_MaxRequestBytes" ∷
      s.[etcdserver.EtcdServer.t, "Cfg"].[config.ServerConfig.t, "MaxRequestBytes"] ↦□ MaxRequestBytes ∗
    "#w" ∷ s.[etcdserver.EtcdServer.t, "w"] ↦□ (interface.ok w) ∗
    "#Hinternal" ∷ is_EtcdServer_internal s γ ∗
    "#raftNode" ∷ s.[etcdserver.EtcdServer.t, "r"].[etcdserver.raftNode.t, "raftNodeConfig"]
       .[etcdserver.raftNodeConfig.t, "Node"] ↦□ (interface.ok rn) ∗
    "#Hr" ∷ is_Node (raft_gn γ) rn ∗
    "Hw" ∷ own_Wait γw w waitR ∗
    "Hclose" ∷ (own_Wait γw w waitR -∗ own_EtcdServer s γ)
.

Axiom is_EtcdServer_internal_pers : ∀ s γ, Persistent (is_EtcdServer_internal s γ).
Existing Instance is_EtcdServer_internal_pers.

(* `own_EtcdServer` can't be persistent because it has a `wait.Wait` inside of it,
   and the implementation of `wait.Wait` uses `RWMutex`, so there can't be a
   persistent `is_Wait`. Moreover, the `own_Wait` depends on the value on the
   RHS of the persistent points-to for field `w`. That means that we can't even
   have a persistent `is_EtcdServer s γ` contained inside of `own_EtcdServer` to
   encapsulate all the persistent things, since an existential variable in the
   persistent part must be referred to in the exclusive part.

   This would make using helper functions like `getAppliedIndex` and
   `getCommittedIndex` annoying if their precondition were the standard
   `own_EtcdServer`. So, instead, they are given weaker preconditions that are
   persistent, and abstract away whatever knowledge they require.

   AuthInfoFromCtx is trickier, because its callstack is harder to audit.
   That being said, there is at least one RWMutex required by
   `EtcdServer.AuthInfoFromCtx -> AuthStore.AuthInfoFromCtx -> authStore.AuthInfoFromCtx ->
   authStore.IsAuthEnabled -> RWMutex.RLock`, so its precondition is the full
   `own_EtcdServer`.
 *)

Axiom wp_EtcdServer__getAppliedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer_internal s γ }}}
    s @! (go.PointerType etcdserver.EtcdServer) @! "getAppliedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Axiom wp_EtcdServer__getCommittedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer_internal s γ }}}
    s @! (go.PointerType etcdserver.EtcdServer) @! "getCommittedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Definition is_SimpleRequest r : iProp Σ :=
  "%HAuthenticate" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.Authenticate') = null ⌝ ∗
  "%HID" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.ID') = W64 0 ⌝ ∗
  "_" ∷ True
.

Axiom wp_EtcdServer__AuthInfoFromCtx : ∀ s γ ctx ctx_desc,
  {{{ is_pkg_init etcdserver ∗ own_EtcdServer s γ ∗ is_Context ctx ctx_desc }}}
    s @! (go.PointerType etcdserver.EtcdServer) @! "AuthInfoFromCtx" #(interface.ok ctx)
  {{{ (a_ptr : loc) (err : interface.t), RET (#a_ptr, #err);
      own_EtcdServer s γ ∗
      if decide (a_ptr = null) then
        True
      else
        ∃ (a : auth.AuthInfo.t), a_ptr ↦ a
  }}}.

Theorem wp_optional (R: iProp Σ) e :
  ∀ Φ, R -∗ (R -∗ WP e {{ v, ⌜ v = execute_val ⌝ ∗ R }}) -∗ (R -∗ Φ execute_val) -∗ WP e {{ Φ }}.
Proof.
  iIntros "% HR He HΦ".
  iSpecialize ("He" with "[$]").
  iApply (wp_wand with "He"). iFrame.
  iIntros "* [-> HR]". iApply "HΦ". done.
Qed.


Instance struct_underlying `{!TCEq t (go.StructType fds)}: t ↓u t.
Proof. inversion TCEq0. subst t. apply _. Qed.

Program Definition C := sealed channel.Channel.
Definition C_unseal : C = _ := seal_eq _.

Instance y : ∀ T : go.type,
  C T <u C T.
Proof. Admitted.

(* Time Eval compute in channel.Channel. *)
(* Time Eval compute in etcdserver.EtcdServer. *)

Lemma x :
  ∀ T : go.type,
  C T <u C T.
Proof.
  intros.
  Print Hint.
  Time apply _.
Abort.

About go.UnderlyingDirectedEq.
Instance z T `{!channel.Assumptions} :
  channel.Channel T <u channel.Channelⁱᵐᵖˡ T | 2.
Proof using.
  Set Typeclasses Debug.
  intros.
  Time apply _.
  (* Time simple eapply @channel.Channel_underlying. *)
Qed.

Instance w :
  ∀ T : go.type, channel.Channel T <u channel.Channelⁱᵐᵖˡ T.
Proof.
  Set Typeclasses Debug.
  intros.
  Print Hint.
  Time apply _.
  (* Time simple eapply @channel.Channel_underlying. *)
Qed.

Global Hint Mode go.UnderlyingDirectedEq + + + + : typeclass_instances.

Instance a : channel.Assumptions.
Proof. apply _. Qed.
Instance x V t : ∀ (H : ZeroVal V) (H' : TypedPointsto V), IntoValTyped V t →
                 IntoValTyped (channel.Channel.t V) (channel.Channel t).
Proof.
  intros.

  Time Fail simple eapply @underlying_to_into_val_typed;
  [ simple apply @defn.go.core_sem |
    simple eapply @is_underlying_unfold;
    [ (* simple eapply @channel.Channel_underlying;  *)apply _
      (* simple apply @channel.Channel_instance; exact a  *) |
      apply _] |
    apply _]; [|].


  Time Fail simple eapply @underlying_to_into_val_typed;
  [ simple apply @defn.go.core_sem |
    simple eapply @is_underlying_unfold;
    [ simple eapply @channel.Channel_underlying; simple apply @channel.Channel_instance; exact a |
      simple apply struct_underlying ] |
    simple apply @channel.channel.Channel.Channel_into_val_typed;
    [ exact a | exact H0 ]]; [|].

  Set Ltac2
  simple eapply @underlying_to_into_val_typed.
  - simple apply @defn.go.core_sem.
  - simple eapply @is_underlying_unfold.
    + simple eapply @channel.Channel_underlying. simple apply @channel.Channel_instance. exact a.
    + simple apply struct_underlying.
  - simple apply @channel.channel.Channel.Channel_into_val_typed.
    + exact a.
    + exact H0.
Qed.

Instance a : channel.Assumptions.
Proof. apply _. Qed.
Instance x V t : ∀ (H : ZeroVal V) (H' : TypedPointsto V), IntoValTyped V t →
                 IntoValTyped (channel.Channel.t V) (channel.Channel t).
Proof.
  clear.
  intros.
  Set Typeclasses Debug.
  Time apply _.
Qed.

Instance x : IntoValTyped etcdserverpb.InternalRaftRequest.t etcdserverpb.InternalRaftRequest.
Proof.
  Typeclasses Opaque etcdserverpb.InternalRaftRequest.
  Time apply _.
Qed.

Lemma wp_EtcdServer__processInternalRaftRequestOnce (s : loc) γ ctx ctx_desc req req_abs :
  {{{ is_pkg_init etcdserver ∗
      "Hsrv" ∷ own_EtcdServer s γ ∗
      "req" ∷ own_InternalRaftRequest req req_abs ∗
      "#Hsimple" ∷ is_SimpleRequest req ∗
      "#Hctx" ∷ is_Context ctx ctx_desc
  }}}
    s @! (go.PointerType etcdserver.EtcdServer) @! "processInternalRaftRequestOnce" #(interface.ok ctx) #req
  {{{ (a : loc) (err : interface.t), RET (#a, #err); own_EtcdServer s γ }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_apply wp_with_defer as "%defer Hdefer" . simpl subst.

  Time wp_alloc_auto.
  (* wp_bind. *)
  (* Time eapply (@tac_wp_alloc _ _ _ _ _ _ _ []). *)
  (* { *)
  (*   Set Typeclasses Debug. *)
  (*   Reset Ltac Profile. *)
  (*   Time apply _. *)
  (* } *)
  wp_pure.
  wp_pure.
  (* Typeclasses Opaque etcdserverpb.InternalRaftRequest. *)
  (* Typeclasses Opaque etcdserverpb.InternalRaftRequestⁱᵐᵖˡ. *)
  (* Typeclasses Opaque etcdserverpb.InternalRaftRequest'fds. *)
  (* Time wp_alloc_auto. *)
  (* Time wp_alloc_auto. *)

  Time wp_alloc_auto.
  wp_pure.
  wp_pure.
  Typeclasses Opaque context.Context.
  Time wp_alloc_auto.
  wp_pure.
  wp_pure.
  wp_pure.
  Typeclasses Opaque go.uint64.
  assert (IntoValTyped w64 go.uint64) by admit.
  Time wp_alloc_auto.
  wp_pure.
  wp_pure.
  Typeclasses Opaque etcdserver.EtcdServer.
  assert (∀ t, IntoValTyped loc $ go.PointerType t) by admit.
  Time wp_load.

  Time wp_bind.

  assert (IntoValTyped etcdserverpb.InternalRaftRequest.t etcdserverpb.InternalRaftRequest).
  { apply _. }
  Time wp_alloc_auto.
  Time eapply (@tac_wp_alloc _ _ _ _ _ _ _ []).
  {
    Set Typeclasses Debug.
    Reset Ltac Profile.

    Time simple eapply @underlying_to_into_val_typed.
    { simple apply @defn.go.core_sem. }
    {
      simple eapply @is_underlying_unfold;
        [
          simple eapply @etcdserverpb.InternalRaftRequest_underlying |
        ].
      { Print Hint.
        simple apply @etcdserverpb.InternalRaftRequest_instance (cost 1, pattern
      }

    }
      Print Hint.
    }
    [ apply _ | | ].
    {
      apply _.
    }
    Time apply _.
  }
    Time simple eapply @underlying_to_into_val_typed.
    { Time apply _. }
    {
      Time apply _.
    }
    {
      Time apply _.
    }
  }
      simple eapply @is_underlying_unfold.
      {
        Typeclasses Opaque etcdserverpb.InternalRaftRequest.
        Time apply _.
        unfold etcdserverpb.InternalRaftRequest.
        simple eapply @etcdserverpb.InternalRaftRequest_underlying.
        apply _.
      }
      apply _.
    }

    Time apply _.
  }
  iApply wp_alloc. --no-auto.
  Time wp_apply wp_alloc --no-auto.
  Show Ltac Profile.
  Time wp_alloc_auto.
  Show Ltac Profile.
  wp_pure.
  wp_pure.
  wp_pure.

  Set Ltac Profiling.
  Set Ltac2 In Ltac1 Profiling.
  wp_alloc_auto.
  wp_pure.
  wp_auto.
  Show Ltac Profile.
  Time Fail wp_pure.
  Time Fail wp_load.
  Time Fail wp_store.
  Time wp_alloc_auto.
  wp_auto. iRename "r" into "req_ptr".
  iDestruct (own_EtcdServer_access with "Hsrv") as "H". iNamed "H".
  wp_apply (wp_EtcdServer__getAppliedIndex with "[$Hinternal]") as "%ai _".
  wp_apply (wp_EtcdServer__getCommittedIndex with "[$Hinternal]") as "%ci _".
  wp_if_destruct.
  {
    (* FIXME: declare then access init predicate of errors. *)
    admit.
  }
  wp_apply (wp_Generator__Next with "[]"). { iFrame "#". }
  iIntros "%i Hid". wp_auto. wp_alloc hdr_ptr as "hdr". wp_auto.
  iNamed "Hsimple". rewrite HAuthenticate. wp_auto.
  iDestruct ("Hclose" with "[$]") as "Hsrv".
  wp_apply (wp_EtcdServer__AuthInfoFromCtx with "[$Hctx $Hsrv]").
  iIntros "* (Hsrv & Hauth)". wp_auto.
  destruct err.
  { wp_auto. iApply "HΦ". done. }
  wp_auto. wp_bind (if: _ then _ else _)%E.
  iAssert ( ∃ hdr,
      "hdr" ∷ hdr_ptr ↦ hdr ∗
      "%hdr_id" ∷ ⌜ hdr.(etcdserverpb.RequestHeader.ID') = i ⌝)%I with "[$hdr //]" as "H".
  wp_apply (wp_optional with "[-]").
  { iNamedAccu. }
  { iNamed 1. case_bool_decide; wp_auto.
    - iSplitR; first done. iFrame.
    - rewrite decide_False //. iNamed "Hauth". iNamed "H".
      wp_auto. iSplitR; first done. iFrame. done. }
  iIntros "*". iNamed 1. iNamed "H".
  wp_auto.

  iDestruct (own_InternalRaftRequest_new_header with "[$] [$]") as "[%req_abs' req]".
  wp_apply (wp_InternalRaftRequest__Marshal with "[$req_ptr $req]").
  iIntros "* Hmarshal". wp_auto.
  destruct err.
  { wp_auto. iApply "HΦ". done. }
  iEval (rewrite decide_True //) in "Hmarshal".
  iDestruct "Hmarshal" as "(req_ptr & req & %data & data_sl & %Hmarshal)".
  wp_auto. wp_if_destruct.
  { wp_bind. (* FIXME: access errors init predicate *) admit. }
  rewrite HID. wp_auto. wp_bind.
  wp_apply (wp_wand with "[req]").
  {
    instantiate (1:=(λ v, "->" ∷ ⌜ v = #hdr.(etcdserverpb.RequestHeader.ID') ⌝ ∗
                        "req" ∷ own_InternalRaftRequest (req <| etcdserverpb.InternalRaftRequest.Header' := hdr_ptr |>) req_abs'
                    )%I).
    admit.
  }
  iIntros "*". iNamed 1.
  iDestruct (own_EtcdServer_access with "Hsrv") as "H".
  iClear "reqIDGen HreqIDGen Cfg_MaxRequestBytes w Hinternal Hr raftNode".
  clear dependent reqIDGen MaxRequestBytes w γw.
  iNamed "H".
  wp_auto. wp_apply (wp_Wait__Register with "[Hw]").
  { iFrame. admit. } (* FIXME: own_unregistered as postcondition of idutil.Generator.Next() *)
  iIntros (ch γch) "(Hw & Hch)". wp_auto. wp_bind. wp_apply wp_wand.
  { instantiate (1:=λ v, (∃ (t : time.Duration.t), ⌜ v = #t ⌝)%I). admit. }
  iIntros "% [% ->]".
  wp_auto. wp_apply wp_WithTimeout. { iFrame "#". } iIntros "* (Hcancel & #Hcctx)".
  wp_auto. wp_apply wp_Now as "% _".
  wp_bind.
  wp_method_call.
  wp_auto.
  wp_method_call.
  wp_auto.
  wp_apply (wp_Node__Propose with "[data_sl]").
  {
    simpl.
    (* FIXME: iFrame "#". still leaves an evar for the [own_raft_log] gname,
       unless first unfolding named. *)
    rewrite /named. iFrame "∗#".
    admit. (* TODO: actually fire the atomic update. *)
  }

  (* TODO:
     axiomatize prometheus Counter inc
     axiomatize `parseProposeCtxErr`
   *)
Admitted.

End wps.
