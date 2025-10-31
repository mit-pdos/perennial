(* TODO: Clean imports *)
Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_send chan_au_recv chan_au_base chan_init.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp_ghost_theory.
From iris.base_logic.lib Require Export token.
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
  Context `{!chanGhostStateG Σ V} `{!IntoVal V} `{!IntoValTyped V tV}.
  Context `{!globalsGS Σ} {go_ctx : GoContext}.
  Context `{!dspG Σ V}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.
  Implicit Types P : iProp Σ.

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance pointsto_proto_from_assumption q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (c ↣ p1) (c ↣ p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "H". by iApply (iProto_pointsto_le with "H").
  Qed.
  Global Instance pointsto_proto_from_frame q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    Frame q (c ↣ p1) (c ↣ p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "[H _]". by iApply (iProto_pointsto_le with "H").
  Qed.

End lang.

Section proofmode.
  Context `{!protoG Σ V}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.
  Implicit Types P : iProp Σ.

  Lemma iProto_le_prepare {TT:tele} a p m (tv : TT -t> V) tP tp :
    ProtoNormalize false p [] (<a> m) →
    MsgTele m tv tP tp →
    ⊢ (p ⊑ (<a @.. (x:TT)> MSG tele_app tv x {{ tele_app tP x }} ; tele_app tp x))%proto.
  Proof.
    intros. rewrite /MsgTele in H0. rewrite -H0.
    rewrite /ProtoNormalize in H.
    simpl in *. rewrite right_id in H.
    done.
  Qed.

End proofmode.

Tactic Notation "iProto_prepare" constr(pat) :=
  iDestruct (iProto_pointsto_le with pat) as pat;
  iDestruct (pat with "[]") as pat;
  [iApply iProto_le_prepare|].

Tactic Notation "iProto_prepare" constr(pat) "with" constr(pat2) :=
  iProto_prepare pat;
  iDestruct (iProto_pointsto_le with pat) as pat;
  iDestruct (pat with pat2) as pat;
  [iIntros "!>"; simpl;
    iFrame; iApply iProto_le_refl|].

Tactic Notation "iProto_prepare" constr(pat) "with" "(" ne_uconstr_list(xs) ")" constr(pat2) :=
  iProto_prepare pat;
  iDestruct (iProto_pointsto_le with pat) as pat;
  iDestruct (pat with pat2) as pat;
  [iIntros "!>"; simpl;
   base.ltac1_list_iter ltac:(fun x => iExists (x)) xs;
   iFrame; iApply iProto_le_refl|].

Tactic Notation "wp_recv_core" "with" constr(pat) :=
  let Htmp := iFresh in
  iDestruct (dsp_recv with "[//]") as Htmp;
  iProto_prepare pat;
  wp_apply (Htmp with pat);
  rewrite -bi_tforall_forall /=;
  iClear Htmp.

Tactic Notation "wp_recv" "with" constr(pat) :=
  wp_recv_core with pat; iIntros pat.

Tactic Notation "wp_recv" "with" constr(pat) "as" constr(pat2) :=
  wp_recv_core with pat;
  iIntros "[_FOO _BAR]"; iRevert "_FOO _BAR"; iIntros pat; iIntros pat2.

Tactic Notation "wp_recv" "with" constr(pat) "as"
    "(" simple_intropattern_list(xs) ")" constr(pat2) :=
  wp_recv_core with pat;
  base.ltac1_list_iter ltac:(fun x => iIntros (x)) xs;
  iIntros "[_FOO _BAR]"; iRevert "_FOO _BAR"; iIntros pat; iIntros pat2.

Tactic Notation "wp_send_core" "with" constr(pat) :=
  let Htmp := iFresh in
  iDestruct (dsp_send with "[//]") as Htmp;
  wp_apply (Htmp with pat);
  iIntros pat.

Tactic Notation "wp_send" "with" constr(pat) :=
  iProto_prepare pat;
  wp_send_core with pat.

Tactic Notation "wp_send" "with" constr(pat) "and" constr(pat2) :=
  iProto_prepare pat with pat2; wp_send_core with pat.

Tactic Notation "wp_send" "with" constr(pat) "and" "("  ne_uconstr_list(xs) ")" constr(pat2) :=
  (* ROCQ BUG: cannot forward [xs] argument to inner [iProto_pepare} tactic. *)
  iProto_prepare pat;
  iDestruct (iProto_pointsto_le with pat) as pat;
  iDestruct (pat with pat2) as pat;
  [iIntros "!>"; simpl;
   base.ltac1_list_iter ltac:(fun x => iExists (x)) xs;
   iFrame; iApply iProto_le_refl|];
  wp_send_core with pat.
