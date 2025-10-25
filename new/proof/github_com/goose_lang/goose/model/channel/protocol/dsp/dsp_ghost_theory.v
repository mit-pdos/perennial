(*
   This file is part of Actris (https://gitlab.mpi-sws.org/iris/actris).

   Copyright (c) Actris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

(** This file defines the core of the Actris logic: It defines dependent
separation protocols and the various operations on it like dual, append, and
branching.

Dependent separation protocols [iProto] are defined by instantiating the
parameterized version in [proto_model] with the type of propositions [iProp] of Iris.
We define ways of constructing instances of the instantiated type via two
constructors:
- [iProto_end], which is identical to [proto_end].
- [iProto_message], which takes an [action] and an [iMsg]. The type [iMsg] is a
  sequence of binders [iMsg_exist], terminated by the payload constructed with
  [iMsg_base] based on arguments [v], [P] and [prot], which are the value, the
  carried proposition and the [iProto] tail, respectively.

For convenience sake, we provide the following notations:
- [END], which is simply [iProto_end].
- [∃ x, m], which is [iMsg_exist] with argument [m].
- [MSG v {{ P }}; prot], which is [iMsg_Base] with arguments [v], [P] and [prot].
- [<a> m], which is [iProto_message] with arguments [a] and [m].

We also include custom notation to more easily construct complete constructions:
- [<a x1 .. xn> m], which is [<a> ∃ x1, .. ∃ xn, m].
- [<a x1 .. xn> MSG v; {{ P }}; prot], which constructs a full protocol.

Futhermore, we define the following operations:
- [iProto_dual], which turns all [Send] of a protocol into [Recv] and vice-versa.
- [iProto_app], which appends two protocols.

In addition we define the subprotocol relation [iProto_le] [⊑], which generalises
the following inductive definition for asynchronous subtyping on session types:

                 p1 <: p2           p1 <: p2          p1 <: !B.p3    ?A.p3 <: p2
----------   ----------------   ----------------     ----------------------------
end <: end    !A.p1 <: !A.p2     ?A.p1 <: ?A.p2             ?A.p1 <: !B.p2

Example:

!R <: !R  ?Q <: ?Q      ?Q <: ?Q
-------------------  --------------
?Q.!R <: !R.?Q       ?P.?Q <: ?P.?Q
------------------------------------
   ?P.?Q.!R <: !R.?P.?Q

Lastly, relevant type classes instances are defined for each of the above
notions, such as contractiveness and non-expansiveness, after which the
specifications of the message-passing primitives are defined in terms of the
protocol connectives. *)
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From New.proof.github_com.goose_lang.goose.model.channel Require Import proto_model.
Set Default Proof Using "Type".
Export action.

(** * Types *)
Definition iProto Σ V := proto V (iPropO Σ) (iPropO Σ).
Declare Scope proto_scope.
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.
Open Scope proto.

(** * Setup of Iris's cameras *)
Class protoG Σ V :=
  protoG_authG ::
    inG Σ (excl_authR (laterO (iProto Σ V))).

Definition protoΣ V := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF)))))
].
Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V.
Proof. solve_inG. Qed.

(** * Messages *)
Section iMsg.
  Set Primitive Projections.
  Record iMsg Σ V := IMsg { iMsg_car : V → laterO (iProto Σ V) -n> iPropO Σ }.
End iMsg.
Arguments IMsg {_ _} _.
Arguments iMsg_car {_ _} _.

Declare Scope msg_scope.
Delimit Scope msg_scope with msg.
Bind Scope msg_scope with iMsg.
Global Instance iMsg_inhabited {Σ V} : Inhabited (iMsg Σ V) := populate (IMsg inhabitant).

Section imsg_ofe.
  Context {Σ : gFunctors} {V : Type}.

  Instance iMsg_equiv : Equiv (iMsg Σ V) := λ m1 m2,
    ∀ w p, iMsg_car m1 w p ≡ iMsg_car m2 w p.
  Instance iMsg_dist : Dist (iMsg Σ V) := λ n m1 m2,
    ∀ w p, iMsg_car m1 w p ≡{n}≡ iMsg_car m2 w p.

  Lemma iMsg_ofe_mixin : OfeMixin (iMsg Σ V).
  Proof. by apply (iso_ofe_mixin (iMsg_car : _ → V -d> _ -n> _)). Qed.
  Canonical Structure iMsgO := Ofe (iMsg Σ V) iMsg_ofe_mixin.

  Global Instance iMsg_cofe : Cofe iMsgO.
  Proof. by apply (iso_cofe (IMsg : (V -d> _ -n> _) → _) iMsg_car). Qed.
End imsg_ofe.

Program Definition iMsg_base_def {Σ V}
    (v : V) (P : iProp Σ) (p : iProto Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ⌜ v = v' ⌝ ∗ Next p ≡ p' ∗ P)%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_base_aux : seal ( @iMsg_base_def). Proof. by eexists. Qed.
Definition iMsg_base := iMsg_base_aux.(unseal).
Definition iMsg_base_eq : @iMsg_base = @iMsg_base_def := iMsg_base_aux.(seal_eq).
Arguments iMsg_base {_ _} _%_V _%_I _%_proto.
Global Instance: Params ( @iMsg_base) 3 := {}.

Program Definition iMsg_exist_def {Σ V A} (m : A → iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ∃ x, iMsg_car (m x) v' p')%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_exist_aux : seal ( @iMsg_exist_def). by eexists. Qed.
Definition iMsg_exist := iMsg_exist_aux.(unseal).
Definition iMsg_exist_eq : @iMsg_exist = @iMsg_exist_def := iMsg_exist_aux.(seal_eq).
Arguments iMsg_exist {_ _ _} _%_msg.
Global Instance: Params ( @iMsg_exist) 3 := {}.

Definition iMsg_texist {Σ V} {TT : tele} (m : TT → iMsg Σ V) : iMsg Σ V :=
  tele_fold ( @iMsg_exist Σ V) (λ x, x) (tele_bind m).
Arguments iMsg_texist {_ _ !_} _%_msg /.

Notation "'MSG' v {{ P } } ; p" := (iMsg_base v P p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v  {{  P  } } ;  p") : msg_scope.
Notation "'MSG' v ; p" := (iMsg_base v True p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v ;  p") : msg_scope.
Notation "∃ x .. y , m" :=
  (iMsg_exist (λ x, .. (iMsg_exist (λ y, m)) ..)%msg) : msg_scope.
Notation "'∃..' x .. y , m" :=
  (iMsg_texist (λ x, .. (iMsg_texist (λ y, m)) .. )%msg)
  (at level 200, x binder, y binder, right associativity,
   format "∃..  x  ..  y ,  m") : msg_scope.

Lemma iMsg_texist_exist {Σ V} {TT : tele} w lp (m : TT → iMsg Σ V) :
  iMsg_car (∃.. x, m x)%msg w lp ⊣⊢ (∃.. x, iMsg_car (m x) w lp).
Proof.
  rewrite /iMsg_texist iMsg_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. apply IH.
Qed.

(** * Operators *)
Definition iProto_end_def {Σ V} : iProto Σ V := proto_end.
Definition iProto_end_aux : seal ( @iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_ _}.

Definition iProto_message_def {Σ V} (a : action) (m : iMsg Σ V) : iProto Σ V :=
  proto_message a (iMsg_car m).
Definition iProto_message_aux : seal ( @iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq :
  @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _} _ _%_msg.
Global Instance: Params ( @iProto_message) 3 := {}.

Notation "'END'" := iProto_end : proto_scope.

Notation "< a > m" := (iProto_message a m)
  (at level 200, a at level 10, m at level 200,
   format "< a >  m") : proto_scope.
Notation "< a @ x1 .. xn > m" := (iProto_message a (∃ x1, .. (∃ xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @  x1  ..  xn >  m") : proto_scope.
Notation "< a @.. x1 .. xn > m" := (iProto_message a (∃.. x1, .. (∃.. xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @..  x1  ..  xn >  m") : proto_scope.

Notation "<!> m" := (<Send> m) (at level 200, m at level 200) : proto_scope.
Notation "<! x1 .. xn > m" := (<!> ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!  x1  ..  xn >  m") : proto_scope.
Notation "<!.. x1 .. xn > m" := (<!> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!..  x1  ..  xn >  m") : proto_scope.

Notation "<?> m" := (<Recv> m) (at level 200, m at level 200) : proto_scope.
Notation "<? x1 .. xn > m" := (<?> ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?  x1  ..  xn >  m") : proto_scope.
Notation "<?.. x1 .. xn > m" := (<?> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?..  x1  ..  xn >  m") : proto_scope.

Class MsgTele {Σ V} {TT : tele} (m : iMsg Σ V)
    (tv : TT -t> V) (tP : TT -t> iProp Σ) (tp : TT -t> iProto Σ V) :=
  msg_tele : m ≡ (∃.. x, MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)%msg.
Global Hint Mode MsgTele ! ! - ! - - - : typeclass_instances.

(** * Operations *)
Program Definition iMsg_map {Σ V}
    (rec : iProto Σ V → iProto Σ V) (m : iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v, λne p1', ∃ p1, iMsg_car m v (Next p1) ∗ p1' ≡ Next (rec p1))%I.
Next Obligation. solve_proper. Qed.

Program Definition iProto_map_app_aux {Σ V}
    (f : action → action) (p2 : iProto Σ V)
    (rec : iProto Σ V -n> iProto Σ V) : iProto Σ V -n> iProto Σ V := λne p,
  proto_elim p2 (λ a m,
    proto_message (f a) (iMsg_car (iMsg_map rec (IMsg m)))) p.
Next Obligation.
  intros Σ V f p2 rec n p1 p1' Hp. apply proto_elim_ne=> // a m1 m2 Hm.
  apply proto_message_ne=> v p' /=. by repeat f_equiv.
Qed.

Global Instance iProto_map_app_aux_contractive {Σ V} f (p2 : iProto Σ V) :
  Contractive (iProto_map_app_aux f p2).
Proof.
  intros n rec1 rec2 Hrec p1; simpl. apply proto_elim_ne=> // a m1 m2 Hm.
  apply proto_message_ne=> v p' /=. by repeat (f_contractive || f_equiv).
Qed.

Definition iProto_map_app {Σ V} (f : action → action)
    (p2 : iProto Σ V) : iProto Σ V -n> iProto Σ V :=
  fixpoint (iProto_map_app_aux f p2).

Definition iProto_app_def {Σ V} (p1 p2 : iProto Σ V) : iProto Σ V :=
  iProto_map_app id p2 p1.
Definition iProto_app_aux : seal ( @iProto_app_def). Proof. by eexists. Qed.
Definition iProto_app := iProto_app_aux.(unseal).
Definition iProto_app_eq : @iProto_app = @iProto_app_def := iProto_app_aux.(seal_eq).
Arguments iProto_app {_ _} _%_proto _%_proto.
Global Instance: Params ( @iProto_app) 2 := {}.
Infix "<++>" := iProto_app (at level 60) : proto_scope.
Notation "m <++> p" := (iMsg_map (flip iProto_app p) m) : msg_scope.

Definition iProto_dual_def {Σ V} (p : iProto Σ V) : iProto Σ V :=
  iProto_map_app action_dual proto_end p.
Definition iProto_dual_aux : seal ( @iProto_dual_def). Proof. by eexists. Qed.
Definition iProto_dual := iProto_dual_aux.(unseal).
Definition iProto_dual_eq :
  @iProto_dual = @iProto_dual_def := iProto_dual_aux.(seal_eq).
Arguments iProto_dual {_ _} _%_proto.
Global Instance: Params ( @iProto_dual) 2 := {}.
Notation iMsg_dual := (iMsg_map iProto_dual).

Definition iProto_dual_if {Σ V} (d : bool) (p : iProto Σ V) : iProto Σ V :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_ _} _ _%_proto.
Global Instance: Params ( @iProto_dual_if) 3 := {}.

(** * Protocol entailment *)
Definition iProto_le_pre {Σ V}
    (rec : iProto Σ V → iProto Σ V → iProp Σ) (p1 p2 : iProto Σ V) : iProp Σ :=
  (p1 ≡ END ∗ p2 ≡ END) ∨
  ∃ a1 a2 m1 m2,
    (p1 ≡ <a1> m1) ∗ (p2 ≡ <a2> m2) ∗
    match a1, a2 with
    | Recv, Recv => ∀ v p1',
       iMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ rec p1' p2' ∗ iMsg_car m2 v (Next p2')
    | Send, Send => ∀ v p2',
       iMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ rec p1' p2' ∗ iMsg_car m1 v (Next p1')
    | _, _ => False
    end.
Global Instance iProto_le_pre_ne {Σ V} (rec : iProto Σ V → iProto Σ V → iProp Σ) :
  NonExpansive2 (iProto_le_pre rec).
Proof. solve_proper. Qed.

Program Definition iProto_le_pre' {Σ V}
    (rec : iProto Σ V -n> iProto Σ V -n> iPropO Σ) :
    iProto Σ V -n> iProto Σ V -n> iPropO Σ := λne p1 p2,
  iProto_le_pre (λ p1' p2', rec p1' p2') p1 p2.
Solve Obligations with solve_proper.
Local Instance iProto_le_pre_contractive {Σ V} : Contractive ( @iProto_le_pre' Σ V).
Proof.
  intros n rec1 rec2 Hrec p1 p2. rewrite /iProto_le_pre' /iProto_le_pre /=.
  by repeat (f_contractive || f_equiv).
Qed.
Definition iProto_le {Σ V} (p1 p2 : iProto Σ V) : iProp Σ :=
  fixpoint iProto_le_pre' p1 p2.
Arguments iProto_le {_ _} _%_proto _%_proto.
Global Instance: Params ( @iProto_le) 2 := {}.
Notation "p ⊑ q" := (iProto_le p q) : bi_scope.

Global Instance iProto_le_ne {Σ V} : NonExpansive2 ( @iProto_le Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_le_proper {Σ V} : Proper ((≡) ==> (≡) ==> (⊣⊢)) ( @iProto_le Σ V).
Proof. solve_proper. Qed.

Fixpoint iProto_app_recvs {Σ V} (vs : list V) (p : iProto Σ V) : iProto Σ V :=
  match vs with
  | [] => p
  | v :: vs => <?> MSG v; iProto_app_recvs vs p
  end.
Definition iProto_interp {Σ V} (vsl vsr : list V) (pl pr : iProto Σ V) : iProp Σ :=
  ∃ p, iProto_app_recvs vsr p ⊑ pl ∗ iProto_app_recvs vsl (iProto_dual p) ⊑ pr.

Definition iProto_own_frag `{!protoG Σ V} (γ : gname)
    (p : iProto Σ V) : iProp Σ :=
  own γ (◯E (Next p)).
Definition iProto_own_auth `{!protoG Σ V} (γ : gname)
    (p : iProto Σ V) : iProp Σ :=
  own γ (●E (Next p)).

(** In the original Actris papers we a single ghost name for [iProto_ctx] and
[iProto_own]. To distinguish the two [iProto_own]s for both sides, we used
an enum [Left]/[Right]. This turned out to be cumbersome because at various
places we need to case at this enum. The current version of [iProto_ctx] has two
ghost names, one for each [iProto_own], enabling more uniform definitions. *)
Definition iProto_ctx `{protoG Σ V}
    (γl γr : gname) (vsl vsr : list V) : iProp Σ :=
  ∃ pl pr,
    iProto_own_auth γl pl ∗
    iProto_own_auth γr pr ∗
    ▷ iProto_interp vsl vsr pl pr.

(** * The connective for ownership of channel ends *)
Definition iProto_own `{!protoG Σ V} (γ : gname) (p : iProto Σ V) : iProp Σ :=
  ∃ p', ▷ (p' ⊑ p) ∗ iProto_own_frag γ p'.
Arguments iProto_own {_ _ _} _ _%_proto.
Global Instance: Params ( @iProto_own) 4 := {}.

Global Instance iProto_own_contractive `{protoG Σ V} γ :
  Contractive (iProto_own γ).
Proof. solve_contractive. Qed.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma own_prot_excl `{!protoG Σ V} γ (p1 p2 : iProto Σ V) :
    own γ (◯E (Next p1)) -∗
    own γ (◯E (Next p2)) -∗
    False.
  Proof.
    iIntros "Hi Hj". iDestruct (own_valid_2 with "Hi Hj") as "H".
    by rewrite uPred.cmra_valid_elim excl_auth_frag_op_validN.
  Qed.

  Lemma iProto_own_excl `{!protoG Σ V} γ (p1 p2 : iProto Σ V) :
    iProto_own γ p1 -∗ iProto_own γ p2 -∗ False.
  Proof.
    rewrite /iProto_own.
    iDestruct 1 as (p1') "[_ Hp1]".
    iDestruct 1 as (p2') "[_ Hp2]".
    iDestruct (own_prot_excl with "Hp1 Hp2") as %[].
  Qed.

  (** ** Equality *)
  Lemma iProto_case p : p ≡ END ∨ ∃ a m, p ≡ <a> m.
  Proof.
    rewrite iProto_message_eq iProto_end_eq.
    destruct (proto_case p) as [|(a&m&?)]; [by left|right].
    by exists a, (IMsg m).
  Qed.
  Lemma iProto_message_equivI `{!BiInternalEq SPROP} a1 a2 m1 m2 :
    (<a1> m1) ≡ (<a2> m2) ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧
      (∀ v lp, iMsg_car m1 v lp ≡ iMsg_car m2 v lp).
  Proof. rewrite iProto_message_eq. apply proto_message_equivI. Qed.

  Lemma iProto_message_end_equivI `{!BiInternalEq SPROP} a m :
    (<a> m) ≡ END ⊢@{SPROP} False.
  Proof. rewrite iProto_message_eq iProto_end_eq. apply proto_message_end_equivI. Qed.
  Lemma iProto_end_message_equivI `{!BiInternalEq SPROP} a m :
    END ≡ (<a> m) ⊢@{SPROP} False.
  Proof. by rewrite internal_eq_sym iProto_message_end_equivI. Qed.

  (** ** Non-expansiveness of operators *)
  Global Instance iMsg_car_proper :
    Proper (iMsg_equiv ==> (=) ==> (≡) ==> (≡)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.
  Global Instance iMsg_car_ne n :
    Proper (iMsg_dist n ==> (=) ==> (dist n) ==> (dist n)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.

  Global Instance iMsg_contractive v n :
    Proper (dist n ==> dist_later n ==> dist n) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_contractive. Qed.
  Global Instance iMsg_ne v : NonExpansive2 (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_proper. Qed.
  Global Instance iMsg_proper v :
    Proper ((≡) ==> (≡) ==> (≡)) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iMsg_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) ( @iMsg_exist Σ V A).
  rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iMsg_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) ( @iMsg_exist Σ V A).
  Proof. rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance msg_tele_base (v:V) (P : iProp Σ) (p : iProto Σ V) :
    MsgTele (TT:=TeleO) (MSG v {{ P }}; p) v P p.
  Proof. done. Qed.
  Global Instance msg_tele_exist {A} {TT : A → tele} (m : A → iMsg Σ V) tv tP tp :
  (∀ x, MsgTele (TT:=TT x) (m x) (tv x) (tP x) (tp x)) →
  MsgTele (TT:=TeleS TT) (∃ x, m x) tv tP tp.
  Proof. intros Hm. rewrite /MsgTele /=. f_equiv=> x. apply Hm. Qed.

  Global Instance iProto_message_ne a :
    NonExpansive (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. rewrite iProto_message_eq. solve_proper. Qed.
  Global Instance iProto_message_proper a :
    Proper ((≡) ==> (≡)) (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_message_equiv {TT1 TT2 : tele} a1 a2
        (m1 m2 : iMsg Σ V)
        (v1 : TT1 -t> V) (v2 : TT2 -t> V)
        (P1 : TT1 -t> iProp Σ) (P2 : TT2 -t> iProp Σ)
        (prot1 : TT1 -t> iProto Σ V) (prot2 : TT2 -t> iProto Σ V) :
    MsgTele m1 v1 P1 prot1 →
    MsgTele m2 v2 P2 prot2 →
    ⌜ a1 = a2 ⌝ -∗
    (■ ∀.. (xs1 : TT1), tele_app P1 xs1 -∗
       ∃.. (xs2 : TT2), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P2 xs2) -∗
    (■ ∀.. (xs2 : TT2), tele_app P2 xs2 -∗
       ∃.. (xs1 : TT1), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P1 xs1) -∗
      (<a1> m1) ≡ (<a2> m2).
  Proof.
    iIntros (Hm1 Hm2 Heq) "#Heq1 #Heq2".
    unfold MsgTele in Hm1. rewrite Hm1. clear Hm1.
    unfold MsgTele in Hm2. rewrite Hm2. clear Hm2.
    rewrite iProto_message_eq proto_message_equivI.
    iSplit; [ done | ].
    iIntros (v p').
    do 2 rewrite iMsg_texist_exist.
    rewrite iMsg_base_eq /=.
    iApply prop_ext.
    iIntros "!>". iSplit.
    - iDestruct 1 as (xs1 Hveq1) "[Hrec1 HP1]".
      iDestruct ("Heq1" with "HP1") as (xs2 Hveq2) "[Hrec2 HP2]".
      iExists xs2. rewrite -Hveq1 Hveq2.
      iSplitR; [ done | ]. iSplitR "HP2"; [ | done ].
      iRewrite -"Hrec1". iApply later_equivI. iIntros "!>". by iRewrite "Hrec2".
    - iDestruct 1 as (xs2 Hveq2) "[Hrec2 HP2]".
      iDestruct ("Heq2" with "HP2") as (xs1 Hveq1) "[Hrec1 HP1]".
      iExists xs1. rewrite -Hveq2 Hveq1.
      iSplitR; [ done | ]. iSplitR "HP1"; [ | done ].
      iRewrite -"Hrec2". iApply later_equivI. iIntros "!>". by iRewrite "Hrec1".
  Qed.

  (** Helpers *)
  Lemma iMsg_map_base f v P p :
    NonExpansive f →
    iMsg_map f (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; f p)%msg.
  Proof.
    rewrite iMsg_base_eq. intros ? v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[(->&Hp&$) Hp']". iSplit; [done|].
      iRewrite "Hp'". iIntros "!>". by iRewrite "Hp".
    - iIntros "(->&Hp'&$)". iExists p. iRewrite -"Hp'". auto.
  Qed.
  Lemma iMsg_map_exist {A} f (m : A → iMsg Σ V) :
    iMsg_map f (∃ x, m x) ≡ (∃ x, iMsg_map f (m x))%msg.
  Proof.
    rewrite iMsg_exist_eq. intros v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[H Hp']". iDestruct "H" as (x) "H"; auto.
    - iDestruct 1 as (x p'') "[Hm Hp']". auto.
  Qed.

  (** ** Dual *)
  Global Instance iProto_dual_ne : NonExpansive ( @iProto_dual Σ V).
   rewrite iProto_dual_eq. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) ( @iProto_dual Σ V).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_if_ne d : NonExpansive ( @iProto_dual_if Σ V d).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_if_proper d :
    Proper ((≡) ==> (≡)) ( @iProto_dual_if Σ V d).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) (V:=V) END ≡ END.
  Proof.
    rewrite iProto_end_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_dual_message a m :
    iProto_dual (<a> m) ≡ <action_dual a> iMsg_dual m.
  Proof.
    rewrite iProto_message_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    rewrite /iProto_message_def. rewrite ->proto_elim_message; [done|].
    intros a' m1 m2 Hm; f_equiv; solve_proper.
  Qed.
  Lemma iMsg_dual_base v P p :
    iMsg_dual (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; iProto_dual p)%msg.
  Proof. apply iMsg_map_base, _. Qed.
  Lemma iMsg_dual_exist {A} (m : A → iMsg Σ V) :
    iMsg_dual (∃ x, m x) ≡ (∃ x, iMsg_dual (m x))%msg.
  Proof. apply iMsg_map_exist. Qed.

  Global Instance iProto_dual_involutive : Involutive (≡) ( @iProto_dual Σ V).
  Proof.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&m&->)].
    { by rewrite !iProto_dual_end. }
    rewrite !iProto_dual_message involutive.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>"; iSplit.
    - iDestruct 1 as (pd) "[H Hp']". iRewrite "Hp'".
      iDestruct "H" as (pdd) "[H #Hpd]".
      iApply (internal_eq_rewrite); [|done]; iIntros "!>".
      iRewrite "Hpd". by iRewrite ("IH" $! pdd).
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists _.
      rewrite Hp'. iSplitL; [by auto|]. iIntros "!>". by iRewrite ("IH" $! p'').
  Qed.

  (** ** Append *)
  Global Instance iProto_app_end_l : LeftId (≡) END ( @iProto_app Σ V).
  Proof.
    intros p. rewrite iProto_end_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_app_message a m p2 : (<a> m) <++> p2 ≡ <a> m <++> p2.
  Proof.
    rewrite iProto_message_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    rewrite /iProto_message_def. rewrite ->proto_elim_message; [done|].
    intros a' m1 m2 Hm. f_equiv; solve_proper.
  Qed.

  Global Instance iProto_app_ne : NonExpansive2 ( @iProto_app Σ V).
  Proof.
    assert (∀ n, Proper (dist n ==> (=) ==> dist n) ( @iProto_app Σ V)).
    { intros n p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    assert (Proper ((≡) ==> (=) ==> (≡)) ( @iProto_app Σ V)).
    { intros p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    intros n p1 p1' Hp1 p2 p2' Hp2. rewrite Hp1. clear p1 Hp1.
    revert p1'. induction (lt_wf n) as [n _ IH]; intros p1.
    destruct (iProto_case p1) as [->|(a&m&->)].
    { by rewrite !left_id. }
    rewrite !iProto_app_message. f_equiv=> v p' /=. do 4 f_equiv.
    f_contractive. apply IH; eauto using dist_lt.
  Qed.
  Global Instance iProto_app_proper : Proper ((≡) ==> (≡) ==> (≡)) ( @iProto_app Σ V).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iMsg_app_base v P p1 p2 :
    ((MSG v {{ P }}; p1) <++> p2)%msg ≡ (MSG v {{ P }}; p1 <++> p2)%msg.
  Proof. apply: iMsg_map_base. Qed.
  Lemma iMsg_app_exist {A} (m : A → iMsg Σ V) p2 :
    ((∃ x, m x) <++> p2)%msg ≡ (∃ x, m x <++> p2)%msg.
  Proof. apply iMsg_map_exist. Qed.

  Global Instance iProto_app_end_r : RightId (≡) END ( @iProto_app Σ V).
  Proof.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&m&->)].
    { by rewrite left_id. }
    rewrite iProto_app_message.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H Hp']". iRewrite "Hp'".
      iApply (internal_eq_rewrite); [|done]; iIntros "!>".
      by iRewrite ("IH" $! p1').
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists p''.
      rewrite Hp'. iSplitL; [by auto|]. iIntros "!>". by iRewrite ("IH" $! p'').
  Qed.
  Global Instance iProto_app_assoc : Assoc (≡) ( @iProto_app Σ V).
  Proof.
    intros p1 p2 p3. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1). destruct (iProto_case p1) as [->|(a&m&->)].
    { by rewrite !left_id. }
    rewrite !iProto_app_message.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p123) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H #Hp']".
      iExists (p1' <++> p2). iSplitL; [by auto|].
      iRewrite "Hp'". iIntros "!>". iApply "IH".
    - iDestruct 1 as (p12) "[H #Hp123]". iDestruct "H" as (p1') "[H #Hp12]".
      iExists p1'. iFrame "H". iRewrite "Hp123".
      iIntros "!>". iRewrite "Hp12". by iRewrite ("IH" $! p1').
  Qed.

  Lemma iProto_dual_app p1 p2 :
    iProto_dual (p1 <++> p2) ≡ iProto_dual p1 <++> iProto_dual p2.
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1 p2). destruct (iProto_case p1) as [->|(a&m&->)].
    { by rewrite iProto_dual_end !left_id. }
    rewrite iProto_dual_message !iProto_app_message iProto_dual_message /=.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p12) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p12d) "[H #Hp12]". iDestruct "H" as (p1') "[H #Hp12d]".
      iExists (iProto_dual p1'). iSplitL; [by auto|].
      iRewrite "Hp12". iIntros "!>". iRewrite "Hp12d". iApply "IH".
    - iDestruct 1 as (p1') "[H #Hp12]". iDestruct "H" as (p1d) "[H #Hp1']".
      iExists (p1d <++> p2). iSplitL; [by auto|].
      iRewrite "Hp12". iIntros "!>". iRewrite "Hp1'". by iRewrite ("IH" $! p1d p2).
  Qed.

  (** ** Protocol entailment **)
  Lemma iProto_le_unfold p1 p2 : iProto_le p1 p2 ≡ iProto_le_pre iProto_le p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_pre'). Qed.

  Lemma iProto_le_end : ⊢ END ⊑ (END : iProto Σ V).
  Proof. rewrite iProto_le_unfold. iLeft. auto 10. Qed.

  Lemma iProto_le_send m1 m2 :
    (∀ v p2', iMsg_car m2 v (Next p2') -∗ ∃ p1',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1')) -∗
    (<!> m1) ⊑ (<!> m2).
  Proof. rewrite iProto_le_unfold. iIntros "H". iRight. auto 10. Qed.
  Lemma iProto_le_recv m1 m2 :
    (∀ v p1', iMsg_car m1 v (Next p1') -∗ ∃ p2',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2')) -∗
    (<?> m1) ⊑ (<?> m2).
  Proof. rewrite iProto_le_unfold. iIntros "H". iRight. auto 10. Qed.

  Lemma iProto_le_end_inv_l p : p ⊑ END -∗ (p ≡ END).
  Proof.
    rewrite iProto_le_unfold. iIntros "[[Hp _]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(_ & Heq & _)".
    by iDestruct (iProto_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iProto_le_end_inv_r p : END ⊑ p -∗ (p ≡ END).
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Hp]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(Heq & _ & _)".
    iDestruct (iProto_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iProto_le_send_inv p1 m2 :
    p1 ⊑ (<!> m2) -∗ ∃ m1,
      (p1 ≡ <!> m1) ∗
      ∀ v p2',
         iMsg_car m2 v (Next p2') -∗ ∃ p1',
           ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    iDestruct (iProto_message_equivI with "Hp2") as (<-) "{Hp2} #Hm".
    iExists _.
    destruct a1.
    - iFrame. iIntros (v p2') "Hm2".
      iApply "H". by iRewrite -("Hm" $! v (Next p2')).
    - done.
  Qed.
  Lemma iProto_le_send_send_inv m1 m2 v p2' :
    (<!> m1) ⊑ (<!> m2) -∗
    iMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_send_inv with "H") as (m1') "[Hm1 H]".
    iDestruct (iProto_message_equivI with "Hm1") as (_) "Hm1".
    iDestruct ("H" with "Hm2") as (p1') "[Hle Hm]".
    iRewrite -("Hm1" $! v (Next p1')) in "Hm". auto with iFrame.
  Qed.
  Lemma iProto_le_recv_send_inv m1 m2 v1 v2 p1' p2' :
    (<?> m1) ⊑ (<!> m2) -∗ False.
  Proof.
    iIntros "H". iDestruct (iProto_le_send_inv with "H") as (m1') "[Hm H]".
    iDestruct (iProto_message_equivI with "Hm") as (H) "{Hm} #Hm".
    done.
  Qed.

  Lemma iProto_le_recv_inv p1 m2 :
    p1 ⊑ (<?> m2) -∗ ∃ m1,
      (p1 ≡ <?> m1) ∗
      ∀ v p1', iMsg_car m1 v (Next p1') -∗ ∃ p2',
        ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    iExists m1.
    iDestruct (iProto_message_equivI with "Hp2") as (<-) "{Hp2} #Hm2".
    destruct a1; [done|]. iSplit; [done|].
    iIntros (v p1') "Hm". iDestruct ("H" with "Hm") as (p2') "[Hle Hm]".
    iExists p2'. iIntros "{$Hle}". by iRewrite ("Hm2" $! v (Next p2')).
  Qed.
  Lemma iProto_le_recv_recv_inv m1 m2 v p1' :
    (<?> m1) ⊑ (<?> m2) -∗
    iMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_recv_inv with "H") as (m1') "[Hm1 H]".
    iApply "H". iDestruct (iProto_message_equivI with "Hm1") as (_) "Hm1".
    by iRewrite -("Hm1" $! v (Next p1')).
  Qed.

  Lemma iProto_le_refl p : ⊢ p ⊑ p.
  Proof.
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|([]&m&->)].
    - iApply iProto_le_end.
    - iApply iProto_le_send. auto 10 with iFrame.
    - iApply iProto_le_recv. auto 10 with iFrame.
  Qed.

  Lemma iProto_le_trans p1 p2 p3 : p1 ⊑ p2 -∗ p2 ⊑ p3 -∗ p1 ⊑ p3.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (iProto_case p3) as [->|([]&m3&->)].
    - iDestruct (iProto_le_end_inv_l with "H2") as "H2". by iRewrite "H2" in "H1".
    - iDestruct (iProto_le_send_inv with "H2") as (m2) "[Hp2 H2]".
      iRewrite "Hp2" in "H1"; clear p2.
      + iDestruct (iProto_le_send_inv with "H1") as (m1) "[Hp1 H1]".
        iRewrite "Hp1"; clear p1.
        iApply iProto_le_send. iIntros (v p3') "Hm3".
        iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
        iDestruct ("H1" with "Hm2") as (p1') "[Hle' Hm1]".
        iExists p1'. iIntros "{$Hm1} !>". by iApply ("IH" with "Hle'").
    - iDestruct (iProto_le_recv_inv with "H2") as (m2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_recv_inv with "H1") as (m1) "[Hp1 H2]".
      iRewrite "Hp1". iApply iProto_le_recv. iIntros (v p1') "Hm1".
      iDestruct ("H2" with "Hm1") as (p2') "[Hle Hm2]".
      iDestruct ("H3" with "Hm2") as (p3') "[Hle' Hm3]".
      iExists p3'. iIntros "{$Hm3} !>". by iApply ("IH" with "Hle").
  Qed.

  Lemma iProto_le_payload_elim_l m v P p :
    (P -∗ (<?> MSG v; p) ⊑ (<?> m)) ⊢
    (<?> MSG v {{ P }}; p) ⊑ (<?> m).
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_recv_recv_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_elim_r m v P p :
    (P -∗ (<!> m) ⊑ (<!> MSG v; p)) ⊢
    (<!> m) ⊑ (<!> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_send_send_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_intro_l v P p :
    P -∗ (<!> MSG v {{ P }}; p) ⊑ (<!> MSG v; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_send. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.
  Lemma iProto_le_payload_intro_r v P p :
    P -∗ (<?> MSG v; p) ⊑ (<?> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_recv. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.

  Lemma iProto_le_exist_elim_l {A} (m1 : A → iMsg Σ V) m2 :
    (∀ x, (<?> m1 x) ⊑ (<?> m2)) ⊢
    (<? x> m1 x) ⊑ (<?> m2).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v p1') "/=". iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_recv_recv_inv with "H").
  Qed.

  Lemma iProto_le_exist_elim_r {A} m1 (m2 : A → iMsg Σ V) :
    (∀ x, (<!> m1) ⊑ (<!> m2 x)) ⊢
    (<!> m1) ⊑ (<! x> m2 x).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v p2'). iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_send_send_inv with "H").
  Qed.
  Lemma iProto_le_exist_intro_l {A} (m : A → iMsg Σ V) a :
    ⊢ (<! x> m x) ⊑ (<!> m a).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_send. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.
  Lemma iProto_le_exist_intro_r {A} (m : A → iMsg Σ V) a :
    ⊢ (<?> m a) ⊑ (<? x> m x).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_recv. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_texist_elim_l {TT : tele} (m1 : TT → iMsg Σ V) m2 :
    (∀ x, (<?> m1 x) ⊑ (<?> m2)) ⊢
    (<?.. x> m1 x) ⊑ (<?> m2).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_l; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma iProto_le_texist_elim_r {TT : tele} m1 (m2 : TT → iMsg Σ V) :
    (∀ x, (<!> m1) ⊑ (<!> m2 x)) -∗
    (<!> m1) ⊑ (<!.. x> m2 x).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_r; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.

  Lemma iProto_le_texist_intro_l {TT : tele} (m : TT → iMsg Σ V) x :
    ⊢ (<!.. x> m x) ⊑ (<!> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [by iApply iProto_le_exist_intro_l|]. iApply IH.
  Qed.
  Lemma iProto_le_texist_intro_r {TT : tele} (m : TT → iMsg Σ V) x :
    ⊢ (<?> m x) ⊑ (<?.. x> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [|by iApply iProto_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma iProto_le_base a v P p1 p2 :
    ▷ (p1 ⊑ p2) ⊢
    (<a> MSG v {{ P }}; p1) ⊑ (<a> MSG v {{ P }}; p2).
  Proof.
    rewrite iMsg_base_eq. iIntros "H". destruct a.
    - iApply iProto_le_send. iIntros (v' p') "(->&Hp&$)".
      iExists p1. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
    - iApply iProto_le_recv. iIntros (v' p') "(->&Hp&$)".
      iExists p2. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
  Qed.

  Lemma iProto_le_dual p1 p2 : p2 ⊑ p1 -∗ iProto_dual p1 ⊑ iProto_dual p2.
  Proof.
    iIntros "H". iLöb as "IH" forall (p1 p2).
    destruct (iProto_case p1) as [->|([]&m1&->)].
    - iDestruct (iProto_le_end_inv_l with "H") as "H".
      iRewrite "H". iApply iProto_le_refl.
    - iDestruct (iProto_le_send_inv with "H") as (m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message).
      iApply iProto_le_recv. iIntros (v p1d).
      iDestruct 1 as (p1') "[Hm1 #Hp1d]".
      iDestruct ("H" with "Hm1") as (p2') "[H Hm2]".
      iDestruct ("IH" with "H") as "H". iExists (iProto_dual p2').
      iSplitL "H"; [iIntros "!>"; by iRewrite "Hp1d"|]. simpl; auto.
    - iDestruct (iProto_le_recv_inv with "H") as (m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message /=).
      iApply iProto_le_send. iIntros (v p2d).
      iDestruct 1 as (p2') "[Hm2 #Hp2d]".
      iDestruct ("H" with "Hm2") as (p1') "[H Hm1]".
      iDestruct ("IH" with "H") as "H". iExists (iProto_dual p1').
      iSplitL "H"; [iIntros "!>"; by iRewrite "Hp2d"|]. simpl; auto.
  Qed.

  Lemma iProto_le_amber_internal (p1 p2 : iProto Σ V → iProto Σ V)
      `{Contractive p1, Contractive p2}:
    □ (∀ rec1 rec2, ▷ (rec1 ⊑ rec2) → p1 rec1 ⊑ p2 rec2) ⊢
    fixpoint p1 ⊑ fixpoint p2.
  Proof.
    iIntros "#H". iLöb as "IH".
    iEval (rewrite (fixpoint_unfold p1)).
    iEval (rewrite (fixpoint_unfold p2)).
    iApply "H". iApply "IH".
  Qed.
  Lemma iProto_le_amber_external (p1 p2 : iProto Σ V → iProto Σ V)
      `{Contractive p1, Contractive p2}:
    (∀ rec1 rec2, (⊢ rec1 ⊑ rec2) → ⊢ p1 rec1 ⊑ p2 rec2) →
    ⊢ fixpoint p1 ⊑ fixpoint p2.
  Proof.
    intros IH. apply fixpoint_ind.
    - by intros p1' p2' -> ?.
    - exists (fixpoint p2). iApply iProto_le_refl.
    - intros p' ?. rewrite (fixpoint_unfold p2). by apply IH.
    - apply bi.limit_preserving_entails; [done|solve_proper].
  Qed.

  Lemma iProto_le_dual_l p1 p2 : iProto_dual p2 ⊑ p1 ⊢ iProto_dual p1 ⊑ p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iProto_dual p2)).
    by iApply iProto_le_dual.
  Qed.
  Lemma iProto_le_dual_r p1 p2 : p2 ⊑ iProto_dual p1 ⊢ p1 ⊑ iProto_dual p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iProto_dual p1)).
    by iApply iProto_le_dual.
  Qed.

  Lemma iProto_le_app p1 p2 p3 p4 :
    p1 ⊑ p2 -∗ p3 ⊑ p4 -∗ p1 <++> p3 ⊑ p2 <++> p4.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3 p4).
    destruct (iProto_case p2) as [->|([]&m2&->)].
    - iDestruct (iProto_le_end_inv_l with "H1") as "H1".
      iRewrite "H1". by rewrite !left_id.
    - iDestruct (iProto_le_send_inv with "H1") as (m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iProto_app_message.
      iApply iProto_le_send. iIntros (v p24).
      iDestruct 1 as (p2') "[Hm2 #Hp24]".
      iDestruct ("H1" with "Hm2") as (p1') "[H1 Hm1]".
      iExists (p1' <++> p3). iSplitR "Hm1"; [|by simpl; eauto].
      iIntros "!>". iRewrite "Hp24". by iApply ("IH" with "H1").
    - iDestruct (iProto_le_recv_inv with "H1") as (m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iProto_app_message. iApply iProto_le_recv.
      iIntros (v p13). iDestruct 1 as (p1') "[Hm1 #Hp13]".
      iDestruct ("H1" with "Hm1") as (p2'') "[H1 Hm2]".
      iExists (p2'' <++> p4). iSplitR "Hm2"; [|by simpl; eauto].
      iIntros "!>". iRewrite "Hp13". by iApply ("IH" with "H1").
  Qed.

  (** ** Lemmas about the auxiliary definitions and invariants *)
  Global Instance iProto_app_recvs_ne vs :
    NonExpansive (iProto_app_recvs (Σ:=Σ) (V:=V) vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance iProto_app_recvs_proper vs :
    Proper ((≡) ==> (≡)) (iProto_app_recvs (Σ:=Σ) (V:=V) vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance iProto_interp_ne vsl vsr :
    NonExpansive2 (iProto_interp (Σ:=Σ) (V:=V) vsl vsr).
  Proof. solve_proper. Qed.
  Global Instance iProto_interp_proper vsl vsr :
    Proper ((≡) ==> (≡) ==> (≡)) (iProto_interp (Σ:=Σ) (V:=V) vsl vsr).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iProto_own_frag_ne γ : NonExpansive (iProto_own_frag γ).
  Proof. solve_proper. Qed.

  Lemma iProto_own_auth_agree γ p p' :
    iProto_own_auth γ p -∗ iProto_own_frag γ p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "H● H◯". iCombine "H● H◯" gives "H✓".
    iDestruct (excl_auth_agreeI with "H✓") as "{H✓} H✓".
    iApply (later_equivI_1 with "H✓").
  Qed.

  Lemma iProto_own_auth_update γ p p' p'' :
    iProto_own_auth γ p -∗ iProto_own_frag γ p' ==∗
    iProto_own_auth γ p'' ∗ iProto_own_frag γ p''.
  Proof.
    iIntros "H● H◯". iDestruct (own_update_2 with "H● H◯") as "H".
    { eapply (excl_auth_update _ _ (Next p'')). }
    by rewrite own_op.
  Qed.

  Lemma iProto_interp_nil p : ⊢ iProto_interp [] [] p (iProto_dual p).
  Proof. iExists p; simpl. iSplitL; iApply iProto_le_refl. Qed.

  Lemma iProto_interp_sym vsl vsr pl pr :
    iProto_interp vsl vsr pl pr ⊢ iProto_interp vsr vsl pr pl.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp]". iExists (iProto_dual p).
    rewrite (involutive iProto_dual). iFrame.
  Qed.

  Lemma iProto_interp_le_l vsl vsr pl pl' pr :
    iProto_interp vsl vsr pl pr -∗ pl ⊑ pl' -∗ iProto_interp vsl vsr pl' pr.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp]". iIntros "Hle". iExists p.
    iFrame "Hdp". by iApply (iProto_le_trans with "Hp").
  Qed.
  Lemma iProto_interp_le_r vsl vsr pl pr pr' :
    iProto_interp vsl vsr pl pr -∗ pr ⊑ pr' -∗ iProto_interp vsl vsr pl pr'.
  Proof.
    iIntros "H Hle". iApply iProto_interp_sym.
    iApply (iProto_interp_le_l with "[H] Hle"). by iApply iProto_interp_sym.
  Qed.

  Lemma iProto_interp_end_inv vsl vsr pr :
    iProto_interp vsl vsr END pr -∗ ⌜vsr = []⌝.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp] /=".
    destruct vsr; [done|].
    iDestruct (iProto_le_end_inv_l with "Hp") as "#Heq".
    by rewrite iProto_message_end_equivI.
  Qed.

  Lemma iProto_interp_send_end_inv vsl vsr vl pl :
    iProto_interp vsl vsr (<!> MSG vl; pl) END -∗
    False.
  Proof.
    iIntros "H".
    iDestruct (iProto_interp_sym with "H") as "H".
    iDestruct (iProto_interp_end_inv with "H") as %->.
    iDestruct (iProto_interp_sym with "H") as "H".
    iDestruct "H" as (p) "[Hp Hdp] /=".
    iDestruct (iProto_le_dual_l with "Hdp") as "Hdp".
    rewrite iProto_dual_end.
    iDestruct (iProto_le_end_inv_r with "Hdp") as "Heq".
    iRewrite "Heq" in "Hp".
    iInduction (vsr) as [|vr vsr] "IHvsr" forall (pl); simpl.
    - iDestruct (iProto_le_end_inv_r with "Hp") as "Hp".
      by rewrite iProto_message_end_equivI.
    - iDestruct (iProto_le_send_inv with "Hp") as (m') "[Heq Hp]".
      rewrite iProto_message_equivI.
      iDestruct "Heq" as (Heq) "Heq". done.
  Qed.

  Lemma iProto_interp_recv_end_inv vsl m :
    iProto_interp vsl [] (<?> m) END -∗
    False.
  Proof.
    iIntros "H".
    iDestruct (iProto_interp_sym with "H") as "H".
    iDestruct (iProto_interp_end_inv with "H") as %->.
    iDestruct (iProto_interp_sym with "H") as "H".
    iDestruct "H" as (p) "[Hp Hdp] /=".
    iDestruct (iProto_le_dual_l with "Hdp") as "Hdp".
    rewrite iProto_dual_end.
    iDestruct (iProto_le_end_inv_r with "Hdp") as "Heq".
    iRewrite "Heq" in "Hp".
    iDestruct (iProto_le_recv_inv with "Hp") as (m1) "[Heq Hp]".
    by rewrite iProto_end_message_equivI.
  Qed.

  Lemma iProto_send_end_inv_r γl γr vsl vsr vr pr :
    iProto_ctx γl γr vsl vsr -∗
    iProto_own γl END -∗
    iProto_own γr (<!> MSG vr; pr) -∗
    ▷ False.
  Proof.
    iDestruct 1 as (pl' pr') "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pl'') "[Hlel H◯l]".
    iDestruct 1 as (pr'') "[Hler H◯r]".
    iDestruct (iProto_own_auth_agree with "H●l H◯l") as "#Hpl".
    iDestruct (iProto_own_auth_agree with "H●r H◯r") as "#Hpr".
    iDestruct (iProto_interp_le_l with "Hinterp [Hlel]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpl". }
    iDestruct (iProto_interp_le_r with "Hinterp [Hler]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpr". }
    iDestruct (iProto_interp_sym with "Hinterp") as "Hinterp".
    by iDestruct (iProto_interp_send_end_inv with "Hinterp") as "Hneq".
  Qed.

  (* Make better lemma: i.e. prove that vsr = non-empty, when (<?> m) / END,
     and derive contradiction from that *)
  Lemma iProto_recv_end_inv_l γl γr vsl m :
    iProto_ctx γl γr vsl [] -∗
    iProto_own γl (<?> m) -∗
    iProto_own γr END -∗
    ▷ False.
  Proof.
    iDestruct 1 as (pl' pr') "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pl'') "[Hlel H◯l]".
    iDestruct 1 as (pr'') "[Hler H◯r]".
    iDestruct (iProto_own_auth_agree with "H●l H◯l") as "#Hpl".
    iDestruct (iProto_own_auth_agree with "H●r H◯r") as "#Hpr".
    iDestruct (iProto_interp_le_l with "Hinterp [Hlel]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpl". }
    iDestruct (iProto_interp_le_r with "Hinterp [Hler]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpr". }
    by iDestruct (iProto_interp_recv_end_inv with "Hinterp") as "Hneq".
  Qed.

  Lemma iProto_end_inv_l γl γr vsl vsr :
    iProto_ctx γl γr vsl vsr -∗
    iProto_own γl END -∗
    ▷ ⌜vsr = []⌝.
  Proof.
    iDestruct 1 as (pl' pr') "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pr'') "[Hle H◯]".
    iDestruct (iProto_own_auth_agree with "H●l H◯") as "#Hpl".
    iDestruct (iProto_interp_le_l with "Hinterp [Hle]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpl". }
    iDestruct (iProto_interp_end_inv with "Hinterp") as "Hneq".
    done.
  Qed.

  Lemma iProto_end_inv_r γl γr vsl vsr :
    iProto_ctx γl γr vsl vsr -∗
    iProto_own γr END -∗
    ▷ ⌜vsl = []⌝.
  Proof.
    iDestruct 1 as (pl' pr') "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pl'') "[Hle H◯]".
    iDestruct (iProto_own_auth_agree with "H●r H◯") as "#Hpr".
    iDestruct (iProto_interp_le_r with "Hinterp [Hle]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hpr". }
    iDestruct (iProto_interp_sym with "Hinterp") as "Hinterp".
    iDestruct (iProto_interp_end_inv with "Hinterp") as "Hneq".
    done.
  Qed.

  Lemma iProto_interp_send vl ml vsl vsr pr pl' :
    iProto_interp vsl vsr (<!> ml) pr -∗
    iMsg_car ml vl (Next pl') -∗
    iProto_interp (vsl ++ [vl]) vsr pl' pr.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp] /="; iIntros "Hml".
    iDestruct (iProto_le_trans _ _ (<!> MSG vl; pl') with "Hp [Hml]") as "Hp".
    { iApply iProto_le_send. rewrite iMsg_base_eq. iIntros (v' p') "(->&Hp&_) /=".
      iExists p'. iSplitR; [iApply iProto_le_refl|]. by iRewrite -"Hp". }
    iInduction vsr as [|vr vsr] "IH" forall (pl'); simpl.
    { iExists pl'; simpl. iSplitR; [iApply iProto_le_refl|].
      iApply (iProto_le_trans with "[Hp] Hdp").
      iInduction vsl as [|vl' vsl] "IH"; simpl.
      { iApply iProto_le_dual_r. rewrite iProto_dual_message iMsg_dual_base /=.
        by rewrite involutive. }
      iApply iProto_le_base; iIntros "!>". by iApply "IH". }
    iDestruct (iProto_le_recv_send_inv _ _ vr vl
      (iProto_app_recvs vsr p) pl' with "Hp") as "[]".
  Qed.

  Lemma iProto_interp_recv vl vsl vsr pl mr :
    iProto_interp (vl :: vsl) vsr pl (<?> mr) -∗
    ∃ pr, iMsg_car mr vl (Next pr) ∗ ▷ iProto_interp vsl vsr pl pr.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp] /=".
    iDestruct (iProto_le_recv_inv with "Hdp") as (m) "[#Hm Hpr]".
    iDestruct (iProto_message_equivI with "Hm") as (_) "{Hm} #Hm".
    iDestruct ("Hpr" $! vl (iProto_app_recvs vsl (iProto_dual p)) with "[]")
      as (pr'') "[Hler Hpr]".
    { iRewrite -("Hm" $! vl (Next (iProto_app_recvs vsl (iProto_dual p)))).
      rewrite iMsg_base_eq; auto. }
    iExists pr''. iIntros "{$Hpr} !>". iExists p. iFrame.
  Qed.

  Lemma iProto_ctx_sym γl γr vsl vsr :
    iProto_ctx γl γr vsl vsr ⊢ iProto_ctx γr γl vsr vsl.
  Proof.
    iIntros "(%pl & %pr & Hauthl & Hauthr & Hinterp)".
    iDestruct (iProto_interp_sym with "Hinterp") as "Hinterp".
    iExists pr, pl; iFrame.
  Qed.

  Global Instance iProto_own_ne γ : NonExpansive (iProto_own γ).
  Proof. solve_proper. Qed.
  Global Instance iProto_own_proper γ : Proper ((≡) ==> (≡)) (iProto_own γ).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_own_le γ p1 p2 :
    iProto_own γ p1 -∗ ▷ (p1 ⊑ p2) -∗ iProto_own γ p2.
  Proof.
    iDestruct 1 as (p1') "[Hle H]". iIntros "Hle'".
    iExists p1'. iFrame "H". by iApply (iProto_le_trans with "Hle").
  Qed.

  Lemma iProto_init p :
    ⊢ |==> ∃ γl γr,
      iProto_ctx γl γr [] [] ∗
      iProto_own γl p ∗ iProto_own γr (iProto_dual p).
  Proof.
    iMod (own_alloc (●E (Next p) ⋅ ◯E (Next p))) as (γl) "[H●l H◯l]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (●E (Next (iProto_dual p)) ⋅
      ◯E (Next (iProto_dual p)))) as (γr) "[H●r H◯r]".
    { by apply excl_auth_valid. }
    iModIntro. iExists γl, γr. iSplitL "H●l H●r".
    { iExists p, (iProto_dual p). iFrame. iApply iProto_interp_nil. }
    iSplitL "H◯l"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_send γl γr m vsr vsl vl p :
    iProto_ctx γl γr vsl vsr -∗
    iProto_own γl (<!> m) -∗
    iMsg_car m vl (Next p) ==∗
      iProto_ctx γl γr (vsl ++ [vl]) vsr ∗
      iProto_own γl p.
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pl') "[Hle H◯]". iIntros "Hm".
    iDestruct (iProto_own_auth_agree with "H●l H◯") as "#Hp".
    iAssert (▷ (pl ⊑ <!> m))%I
      with "[Hle]" as "{Hp} Hle"; first (iNext; by iRewrite "Hp").
    iDestruct (iProto_interp_le_l with "Hinterp Hle") as "Hinterp".
    iDestruct (iProto_interp_send with "Hinterp [Hm //]") as "Hinterp".
    iMod (iProto_own_auth_update _ _ _ p with "H●l H◯") as "[H●l H◯]".
    iIntros "!>". iSplitR "H◯".
    - iExists p, pr. iFrame.
    - iExists p. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma iProto_recv γl γr m vr vsr vsl :
    iProto_ctx γl γr vsl (vr :: vsr) -∗
    iProto_own γl (<?> m) ==∗
    ▷ ∃ p,
      iProto_ctx γl γr vsl vsr ∗
      iProto_own γl p ∗
      iMsg_car m vr (Next p).
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]".
    iDestruct (iProto_own_auth_agree with "H●l H◯") as "#Hp".
    iDestruct (iProto_interp_le_l with "Hinterp [Hle]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hp". }
    iDestruct (iProto_interp_sym with "Hinterp") as "Hinterp".
    iDestruct (iProto_interp_recv with "Hinterp") as (q) "[Hm Hinterp]".
    iMod (iProto_own_auth_update _ _ _ q with "H●l H◯") as "[H●l H◯]".
    iIntros "!> !> /=". iExists q. iFrame "Hm". iSplitR "H◯".
    - iExists q, pr. iFrame. by iApply iProto_interp_sym.
    - iExists q. iIntros "{$H◯} !>". iApply iProto_le_refl.
  Qed.

  (** The instances below make it possible to use the tactics [iIntros],
  [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [iProto_le] goals. *)
  Global Instance iProto_le_from_forall_l {A} (m1 : A → iMsg Σ V) m2 name :
    AsIdentName m1 name →
    FromForall (iProto_message Recv (iMsg_exist m1) ⊑ (<?> m2))
               (λ x, (<?> m1 x) ⊑ (<?> m2))%I name | 10.
  Proof. intros _. apply iProto_le_exist_elim_l. Qed.
  Global Instance iProto_le_from_forall_r {A} m1 (m2 : A → iMsg Σ V) name :
    AsIdentName m2 name →
    FromForall ((<!> m1) ⊑ iProto_message Send (iMsg_exist m2))
               (λ x, (<!> m1) ⊑ (<!> m2 x))%I name | 11.
  Proof. intros _. apply iProto_le_exist_elim_r. Qed.

  Global Instance iProto_le_from_wand_l m v P p :
    TCIf (TCEq P True%I) False TCTrue →
    FromWand ((<?> MSG v {{ P }}; p) ⊑ (<?> m)) P ((<?> MSG v; p) ⊑ (<?> m)) | 10.
  Proof. intros _. apply iProto_le_payload_elim_l. Qed.
  Global Instance iProto_le_from_wand_r m v P p :
    FromWand ((<!> m) ⊑ (<!> MSG v {{ P }}; p)) P ((<!> m) ⊑ (<!> MSG v; p)) | 11.
  Proof. apply iProto_le_payload_elim_r. Qed.

  Global Instance iProto_le_from_exist_l {A} (m : A → iMsg Σ V) p :
    FromExist ((<! x> m x) ⊑ p) (λ a, (<!> m a) ⊑ p)%I | 10.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "[] H"). iApply iProto_le_exist_intro_l.
  Qed.
  Global Instance iProto_le_from_exist_r {A} (m : A → iMsg Σ V) p :
    FromExist (p ⊑ <? x> m x) (λ a, p ⊑ (<?> m a))%I | 11.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "H"). iApply iProto_le_exist_intro_r.
  Qed.

  Global Instance iProto_le_from_sep_l m v P p :
    FromSep ((<!> MSG v {{ P }}; p) ⊑ (<!> m)) P ((<!> MSG v; p) ⊑ (<!> m)) | 10.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "[HP] H"). by iApply iProto_le_payload_intro_l.
  Qed.
  Global Instance iProto_le_from_sep_r m v P p :
    FromSep ((<?> m) ⊑ (<?> MSG v {{ P }}; p)) P ((<?> m) ⊑ (<?> MSG v; p)) | 11.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "H"). by iApply iProto_le_payload_intro_r.
  Qed.

  Global Instance iProto_le_frame_l q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<!> MSG v {{ P }}; p) ⊑ (<!> m))
              ((<!> MSG v {{ Q }}; p) ⊑ (<!> m)) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "[HR] H"). iApply iProto_le_payload_elim_r.
    iIntros "HQ". iApply iProto_le_payload_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance iProto_le_frame_r q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<?> m) ⊑ (<?> MSG v {{ P }}; p))
              ((<?> m) ⊑ (<?> MSG v {{ Q }}; p)) | 11.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "H"). iApply iProto_le_payload_elim_l.
    iIntros "HQ". iApply iProto_le_payload_intro_r. iApply HP; iFrame.
  Qed.

  Global Instance iProto_le_from_modal a v p1 p2 :
    FromModal True (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2).
  Proof. intros _. apply iProto_le_base. Qed.

End proto.

Global Typeclasses Opaque iProto_ctx iProto_own.

Global Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply iProto_le_refl] : core.
