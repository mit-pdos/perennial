From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_send chan_au_recv chan_au_base chan_init.
From New.proof.github_com.goose_lang.goose.model.channel Require Export dsp_ghost_theory.
From iris.proofmode Require Import coq_tactics reduction spec_patterns proofmode.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp.

(** * Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** * Normalization of protocols *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  dual_action_if : a2 = if d then action_dual a1 else a1.
Global Hint Mode ActionDualIf ! ! - : typeclass_instances.

Global Instance action_dual_if_false a : ActionDualIf false a a := eq_refl.
Global Instance action_dual_if_true_send : ActionDualIf true Send Recv := eq_refl.
Global Instance action_dual_if_true_recv : ActionDualIf true Recv Send := eq_refl.

Class ProtoNormalize {Σ V} (d : bool) (p : iProto Σ V)
    (pas : list (bool * iProto Σ V)) (q : iProto Σ V) :=
  proto_normalize :
    ⊢ iProto_dual_if d p <++>
        foldr (iProto_app ∘ uncurry iProto_dual_if) END%proto pas ⊑ q.
Global Hint Mode ProtoNormalize ! ! ! ! ! - : typeclass_instances.
Arguments ProtoNormalize {_ _} _ _%_proto _%_proto _%_proto.

Notation ProtoUnfold p1 p2 := (∀ d pas q,
  ProtoNormalize d p2 pas q → ProtoNormalize d p1 pas q).

Class MsgNormalize {Σ V} (d : bool) (m1 : iMsg Σ V)
    (pas : list (bool * iProto Σ V)) (m2 : iMsg Σ V) :=
  msg_normalize a :
    ProtoNormalize d (<a> m1) pas (<(if d then action_dual a else a)> m2).
Global Hint Mode MsgNormalize ! ! ! ! ! - : typeclass_instances.
Arguments MsgNormalize {_ _} _ _%_msg _%_msg _%_msg.

Section classes.
  Context `{!protoG Σ V}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.
  Implicit Types P : iProp Σ.

  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoNormalize=> Hp d pas q. by rewrite Hp. Qed.

  Global Instance proto_normalize_done p : ProtoNormalize false p [] p | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual p :
    ProtoNormalize true p [] (iProto_dual p) | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual_end :
    ProtoNormalize (Σ:=Σ) true END [] (END:iProto Σ V) | 0.
  Proof. rewrite /ProtoNormalize /= right_id iProto_dual_end. auto. Qed.

  Global Instance proto_normalize_dual d p pas q :
    ProtoNormalize (negb d) p pas q →
    ProtoNormalize d (iProto_dual p) pas q.
  Proof. rewrite /ProtoNormalize. by destruct d; rewrite /= ?involutive. Qed.

  Global Instance proto_normalize_app_l d p1 p2 pas q :
    ProtoNormalize d p1 ((d,p2) :: pas) q →
    ProtoNormalize d (p1 <++> p2) pas q.
  Proof.
    rewrite /ProtoNormalize /=. rewrite assoc.
    by destruct d; by rewrite /= ?iProto_dual_app.
  Qed.

  Global Instance proto_normalize_end d d' p pas q :
    ProtoNormalize d p pas q →
    ProtoNormalize d' END ((d,p) :: pas) q | 0.
  Proof.
    rewrite /ProtoNormalize /=.
    destruct d'; by rewrite /= ?iProto_dual_end left_id.
  Qed.

  Global Instance proto_normalize_app_r d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize false p1 ((d,p2) :: pas) (p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance proto_normalize_app_r_dual d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize true p1 ((d,p2) :: pas) (iProto_dual p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance msg_normalize_base d v P p q pas :
    ProtoNormalize d p pas q →
    MsgNormalize d (MSG v {{ P }}; p) pas (MSG v {{ P }}; q).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    iApply iProto_le_trans; [|by iApply iProto_le_base].
    destruct d; by rewrite /= ?iProto_dual_message ?iMsg_dual_base
      iProto_app_message iMsg_app_base.
  Qed.

  Global Instance msg_normalize_exist {A} d (m1 m2 : A → iMsg Σ V) pas :
    (∀ x, MsgNormalize d (m1 x) pas (m2 x)) →
    MsgNormalize d (∃ x, m1 x) pas (∃ x, m2 x).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    destruct d, a; simpl in *; rewrite ?iProto_dual_message ?iMsg_dual_exist
      ?iProto_app_message ?iMsg_app_exist /=; iIntros (x); iExists x; first
      [move: (H x Send); by rewrite ?iProto_dual_message ?iProto_app_message
      |move: (H x Recv); by rewrite ?iProto_dual_message ?iProto_app_message].
  Qed.

  Global Instance proto_normalize_message d a1 a2 m1 m2 pas :
    ActionDualIf d a1 a2 →
    MsgNormalize d m1 pas m2 →
    ProtoNormalize d (<a1> m1) pas (<a2> m2).
  Proof. by rewrite /ActionDualIf /MsgNormalize /ProtoNormalize=> ->. Qed.

End classes.

Section lang.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem : go.Semantics}.
  Collection W := sem.
  Local Set Default Proof Using "W".
  Context `{!dspG Σ V}.
  Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.
  Implicit Types P : iProp Σ.

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance pointsto_proto_from_assumption q c p1 p2 γ :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (c ↣{γ} p1) (c ↣{γ} p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "H". by iApply (iProto_pointsto_le with "H").
  Qed.
  Global Instance pointsto_proto_from_frame q c p1 p2 γ :
    ProtoNormalize false p1 [] p2 →
    Frame q (c ↣{γ} p1) (c ↣{γ} p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "[H _]". by iApply (iProto_pointsto_le with "H").
  Qed.

End lang.

(** * Symbolic execution tactics *)
(* TODO: Maybe strip laters from other hypotheses in the future? *)
Lemma tac_wp_recv
  `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics} `{!dspG Σ V}
  `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
  {TT : tele} Δ i j K (lr_chan rl_chan:loc) γ p m (tv : TT -t> V) tP tP' tp Φ :
  envs_lookup i Δ = Some (false, (lr_chan, rl_chan) ↣{γ} p)%I →
  ProtoNormalize false p [] (<?> m) →
  MsgTele m tv tP tp →
  (∀.. x, MaybeIntoLaterN false 1 (tele_app tP x) (tele_app tP' x)) →
  let Δ' := envs_delete false i false Δ in
  (∀.. x : TT,
    match envs_app false
        (Esnoc (Esnoc Enil j (tele_app tP' x)) i ((lr_chan,rl_chan) ↣{γ} tele_app tp x)) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (#(tele_app tv x), #true)) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (chan.receive t #rl_chan) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /MaybeIntoLaterN /=.
  rewrite !tforall_forall right_id.
  intros ? Hp Hm HP HΦ. rewrite envs_lookup_sound //; simpl.
  assert ((lr_chan,rl_chan) ↣{γ} p ⊢ (lr_chan,rl_chan) ↣{γ} <?.. x>
    MSG tele_app tv x {{ ▷ tele_app tP' x }}; tele_app tp x) as ->.
  { iIntros "Hc". iApply (iProto_pointsto_le with "Hc"). iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|rewrite Hm].
    iApply iProto_le_texist_elim_l; iIntros (x).
    iApply iProto_le_trans; [|iApply (iProto_le_texist_intro_r _ x)]; simpl.
    iIntros "H". by iDestruct (HP with "H") as "$". }
  rewrite -wp_bind. eapply bi.wand_apply;
    [by eapply bi.wand_entails, (wp_dsp_recv _ lr_chan _ (tele_app tv) (tele_app tP') (tele_app tp))|
      f_equiv; first done].
  rewrite -bi.later_intro; apply bi.forall_intro=> x.
  specialize (HΦ x). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΦ.
Qed.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (@AppLCtx _ v) K e
    | App ?e1 ?e2                     => add_item (@AppRCtx _ e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Pair (Val ?v) ?e                => add_item (PairRCtx v) K e
    | Pair ?e1 ?e2                    => add_item (PairLCtx e2) K e1
    | Fst ?e                          => add_item (@FstCtx _) K e
    | Snd ?e                          => add_item (@SndCtx _) K e
    | Primitive2 ?op (Val ?v) ?e      => add_item (@Primitive2RCtx _ op v) K e
    | Primitive2 ?op ?e1 ?e2          => add_item (@Primitive2LCtx _ op e2) K e1
    | Primitive1 ?op ?e               => add_item (@Primitive1Ctx _ op) K e
    | ExternalOp ?op ?e               => add_item (@ExternalOpCtx _ op) K e
    (* | Primitive3 ?op (Val ?v0) (Val ?v1) ?e2 => add_item (Primitive3RCtx op v0 v1) K e2
    | Primitive3 ?op (Val ?v0) ?e1 ?e2     => add_item (Primitive3MCtx op v0 e2) K e1
    | Primitive3 ?op ?e0 ?e1 ?e2           => add_item (Primitive3LCtx op e1 e2) K e0 *)
    | CmpXchg (Val ?v0) (Val ?v1) ?e2 => add_item (CmpXchgRCtx v0 v1) K e2
    | CmpXchg (Val ?v0) ?e1 ?e2       => add_item (CmpXchgMCtx v0 e2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgLCtx e1 e2) K e0
    | ResolveProph (Val ?v) ?e        => add_item (@ResolveProphRCtx _ v) K e
    | ResolveProph ?e1 ?e2            => add_item (@ResolveProphLCtx _ e2) K e1
    | fill ?K' ?e                     => match K with [] => go K' e end
    end
  with add_item Ki K e :=
    go (Ki :: K) e
  in
  go (@nil ectx_item) e.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_} _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣{γ} ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_pointsto ()
       |tc_solve || fail 1 "wp_recv: protocol not of the shape <?>"
    |tc_solve || fail 1 "wp_recv: cannot convert to telescope"
    |tc_solve
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     pm_prettify]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as"
    "(" ne_simple_intropattern_list(ys) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => _iDestructHyp H ys pat).

Lemma tac_wp_send
  `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics} `{!dspG Σ V}
  `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
  {TT : tele} Δ neg i js K (lr_chan rl_chan : loc) γ v p m tv tP tp Φ :
  envs_lookup i Δ = Some (false, (lr_chan,rl_chan) ↣{γ} p)%I →
  ProtoNormalize false p [] (<!> m) →
  MsgTele m tv tP tp →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then base.Right else base.Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i ((lr_chan,rl_chan) ↣{γ} tele_app tp x)) Δ2 with
       | Some Δ2' =>
          v = tele_app tv x ∧
          envs_entails Δ1 (tele_app tP x) ∧
          envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (chan.send t #lr_chan #v) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /= right_id texist_exist.
  intros ? Hp Hm [x HΦ]. rewrite envs_lookup_sound //; simpl.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as (-> & -> & ->). rewrite right_id assoc.
  assert ((lr_chan,rl_chan) ↣{γ} p ⊢
    (lr_chan,rl_chan) ↣{γ} <!.. (x : TT)> MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x) as ->.
  { iIntros "Hc". iApply (iProto_pointsto_le with "Hc"); iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|]. by rewrite Hm. }
  eapply bi.wand_apply; [rewrite -wp_bind; by eapply bi.wand_entails, wp_dsp_send_tele|].
  by rewrite -bi.later_intro.
Qed.

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_} _)%I) => c end in
    iAssumptionCore || fail "wp_send: cannot find" c "↣{γ} ? @ ?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'chan.send' in" e];
       [solve_pointsto ()
       |tc_solve || fail 1 "wp_send: protocol not of the shape <!>"
       |tc_solve || fail 1 "wp_send: cannot convert to telescope"
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => notypeclasses refine (conj (eq_refl _) (conj _ _));
                [iFrame Hs_frame; solve_done d
                |pm_prettify]
        end]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" ne_uconstr_list(xs) ")" "with" constr(pat) :=
  wp_send_core (ltac1_list_iter ltac:(fun x => eexists x) xs) with pat.
