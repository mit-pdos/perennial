(** we provide an operational model (encoded as a labeled transition
system) for:
1) an EUF-CMA signature scheme.
2) a collision-resistant random oracle hash function.

to gain assurance in the model, we prove trace invariants that capture the
core cryptographic properties of both operations.
see [sig_correct], [sig_unforg], and [coll_resis].

we should be able to prove the admitted iProps in cryptoffi.v from this. *)

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Perennial.Helpers Require Import Integers.
From stdpp Require Import ssreflect prelude gmap.
(* not using the BI parts, just gset_bijective. *)
From iris.algebra.lib Require Import gset_bij.

Section shared.

(* arb_T returns a random concrete T. *)
Definition arb_bool : bool. Admitted.
Definition arb_bytes : list w8. Admitted.
Definition arb_bytes_len (len : nat) : list w8. Admitted.

End shared.

Module signatures.

Notation sk_ty := (list w8) (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation sig_ty := (list w8) (only parsing).
Notation msg_ty := (list w8) (only parsing).

Record state_ty :=
  mk_state {
    (* bijective set of in-distr keys. *)
    key_distr: gset (sk_ty * pk_ty);
    (* make verify deterministic by memoizing outputs. *)
    verify_memo: gmap (pk_ty * msg_ty * sig_ty) bool;
  }.
Instance eta_state : Settable _ :=
  settable! mk_state <key_distr; verify_memo>.

Inductive op_ty : Type :=
  | key_gen : op_ty
  | sign : sk_ty → msg_ty → op_ty
  | verify : pk_ty → msg_ty → sig_ty → op_ty.

Inductive ret_ty : Type :=
  | ret_key_gen : sk_ty → pk_ty → ret_ty
  | ret_sign : sig_ty → ret_ty
  | ret_verify : bool → ret_ty.

Record trans_ty :=
  mk_trans {
    op: op_ty;
    ret: ret_ty;
  }.

(** the main goal is to follow the guarantees of EUF-CMA as closely as possible.
e.g., EUF-CMA says sign / verify are undefined for OOD sk's / pk's,
so we return random values.
e.g., EUF-CMA has a stateful notion of the adversary not being able to forge
signatures if it never signed the msg before.
our model tracks signed state to guarantee this.

the main divergence is in the notion of distributions.
for us, "in-distribution" means a key already gen'd by key_gen.
"out-of-distribution" means a key not yet gen'd by key_gen.
in EUF-CMA, a distribution is fixed ahead of time.

the other divergence is how we capture the constraint of a poly time adversary.
the main capability of super-poly adversaries is their ability to run crypto ops
a huge number of times to exhibit collisions.
we block this, by having the underlying machine infinite loop exactly when
it detects a collision. *)
Definition step (prev_st : state_ty) (trans : trans_ty) (next_st : state_ty) : Prop :=
  match trans.(op) with
  | key_gen =>
    let sk := arb_bytes in
    let pk := arb_bytes in
    (* check for collisions, either with prior key_gen or with OOD key. *)
    if
      bool_decide (set_Exists (λ x, x.1 = sk) prev_st.(key_distr)) ||
      bool_decide (set_Exists (λ x, x.2 = pk) prev_st.(key_distr)) ||
      bool_decide (map_Exists (λ k _, k.1.1 = pk) prev_st.(verify_memo))
    then
      (* collision. infinite loop the machine. *)
      False
    else
      (* TODO: make key_gen return sk ptr, so it's impossible for programs to
      leak it. *)
      trans.(ret) = ret_key_gen sk pk ∧
      next_st = prev_st <| key_distr ::= ({[ (sk, pk) ]} ∪.) |>

  | sign sk msg =>
    if decide (set_Forall (λ x, x.1 ≠ sk) prev_st.(key_distr))
    then
      (* sign is only defined over in-distribution sk's. return random values. *)
      let sig := arb_bytes in
      trans.(ret) = ret_sign sig ∧ next_st = prev_st
    else
      ∀ pk, (sk, pk) ∈ prev_st.(key_distr) →
      (* sign is probabilistic. might return diff sigs for same data.
      avoid sig dup in the following degenerate case:
      key_gen, verify msg sig = false, sign msg = sig, verify msg sig = ?. *)
      let sig := arb_bytes in
      match prev_st.(verify_memo) !! (pk, msg, sig) with
      | None
      | Some true =>
        trans.(ret) = ret_sign sig ∧
        (* immediately memoize so verify returns the right thing. *)
        next_st = prev_st <| verify_memo ::= <[(pk,msg,sig):=true]> |>
      | Some false =>
        (* bad sig collision (see above case). infinite loop the machine. *)
        False
      end

  | verify pk msg sig =>
    match prev_st.(verify_memo) !! (pk, msg, sig) with
    | Some ok => trans.(ret) = ret_verify ok ∧ next_st = prev_st
    | None =>
      (* memoize new verify output. *)
      (λ '(new_ok, new_state),
        trans.(ret) = ret_verify new_ok ∧
        next_st = new_state <| verify_memo ::= <[(pk,msg,sig):=new_ok]> |>)
      (if decide (set_Forall (λ x, x.2 ≠ pk) prev_st.(key_distr))
      then
        (* verify is only defined over in-distribution pk's. return random values. *)
        let ok := arb_bool in
        (ok, prev_st)
      else
        if decide (map_Exists (λ k v, k.1.1 = pk ∧ k.1.2 = msg ∧ v = true)
          prev_st.(verify_memo))
        then
          (* for already signed msgs, either:
          1) we signed this exact sig.
          in this case, memoization would run, not this code.
          2) we signed this msg, but not this sig.
          could have forged a valid sig. *)
          let ok := arb_bool in
          (ok, prev_st)
        else
          (* if never signed msg before, should be impossible to verify.
          this preserves inv that for in-distr pk and some msg, will only have
          verify_memo=True for any sig if actually signed msg. *)
          (false, prev_st))
    end
  end.

Record trace_ty :=
  mk_trace {
    states: list state_ty;
    labels: list trans_ty;
  }.

Definition valid_trace (t : trace_ty) :=
  (∀ a, t.(states) !! 0 = Some a → a.(key_distr) = ∅ ∧ a.(verify_memo) = ∅) ∧
  Forall3 (λ a b c, step a b c)
    (take (pred (length t.(states))) t.(states))
    t.(labels)
    (drop 1 t.(states)).

Lemma keys_bij {t i s} :
  valid_trace t →
  t.(states) !! i = Some s →
  gset_bijective s.(key_distr).
Proof. Admitted.

Lemma sig_correct {t i k st_i sk pk msg sig ok} :
  valid_trace t →
  (* valid key. *)
  t.(states) !! i = Some st_i →
  set_Exists (λ x, x = (sk, pk)) st_i.(key_distr) →
  (* called sign. *)
  t.(labels) !! i = Some (mk_trans (sign sk msg) (ret_sign sig)) →
  (* called verify. *)
  t.(labels) !! (i + k) = Some (mk_trans (verify pk msg sig) (ret_verify ok)) →
  (* verify will return true. *)
  ok = true.
Proof. Admitted.

Lemma sig_unforg {t i st_i sk pk msg sig ok} :
  valid_trace t →
  (* valid key. *)
  t.(states) !! i = Some st_i →
  set_Exists (λ x, x = (sk, pk)) st_i.(key_distr) →
  (* never signed msg before.
  modeling with verify_memo would under-approx adv ability,
  since adv can forge some sigs.
  this label modeling is more precise. *)
  (∀ j sig',
    j < i →
    t.(labels) !! j ≠ Some (mk_trans (sign sk msg) (ret_sign sig'))) →
  (* called verify with some sig. *)
  t.(labels) !! i = Some (mk_trans (verify pk msg sig) (ret_verify ok)) →
  (* verify will return false. *)
  ok = false.
Proof. Admitted.

End signatures.

Module hashes.

Notation msg_ty := (list w8) (only parsing).
Notation hash_ty := (list w8) (only parsing).
Notation hash_len := (32) (only parsing).

Record state_ty :=
  mk_hash_state {
    hashes: gset (msg_ty * hash_ty);
  }.
Instance eta_state : Settable _ :=
  settable! mk_hash_state <hashes>.

Inductive op_ty : Type :=
  | hash : msg_ty → op_ty.

Inductive ret_ty : Type :=
  | ret_hash : hash_ty → ret_ty.

Record trans_ty :=
  mk_trans {
    op: op_ty;
    ret: ret_ty;
  }.

Definition get_hash (d : list w8) : list w8.
Admitted.

Definition step (prev_st : state_ty) (trans : trans_ty) (next_st : state_ty) : Prop :=
  match trans.(op) with
  | hash msg =>
    if decide (set_Exists (λ x, x.1 = msg) prev_st.(hashes))
    then
      ∀ h, (msg, h) ∈ prev_st.(hashes) →
      trans.(ret) = (ret_hash h) ∧ next_st = prev_st
    else
      (* maintains inv that all hashes have same len. *)
      let new_hash := arb_bytes_len hash_len in
      if decide (set_Exists (λ x, x.2 = new_hash) prev_st.(hashes))
      (* hash collision. infinite loop the machine. *)
      then False
      else
        trans.(ret) = (ret_hash new_hash) ∧
        next_st = prev_st <| hashes ::= ({[ (msg, new_hash) ]} ∪.) |>
  end.

Record trace_ty :=
  mk_trace {
    states: list state_ty;
    labels: list trans_ty;
  }.

Definition valid_trace (t : trace_ty) :=
  (∀ a, t.(states) !! 0 = Some a → a.(hashes) = ∅) ∧
  Forall3 (λ a b c, step a b c)
    (take (pred (length t.(states))) t.(states))
    t.(labels)
    (drop 1 t.(states)).

Lemma hashes_bij {t i s} :
  valid_trace t →
  t.(states) !! i = Some s →
  gset_bijective s.(hashes).
Proof.
  (* this first chunk of proof is mostly repeated between the three helper lemmas.
  it sets up induction and grabs a step transition. *)
  intros Hvalid.
  generalize dependent s.
  induction i; intros st_Si Hlook_st_Si.
  { destruct Hvalid as [Hinit _].
    specialize (Hinit _ Hlook_st_Si) as ->.
    apply gset_bijective_empty. }
  destruct Hvalid as [_ Hsteps].
  opose proof (Forall3_lookup_r _ _ _ _ _ _ Hsteps) as
    (st_i & la & Hlook_st_i & Hlook_la & Hstep); clear Hsteps.
  { by rewrite lookup_drop. }
  opose proof (IHi _ _) as Hbij_prev.
  { apply lookup_take_Some in Hlook_st_i. naive_solver. }
  rewrite /step in Hstep.

  (* this is the actually interesting chunk.
  proving invariance across one step. *)
  case_match eqn:Hop. case_decide as Hhashed.
  - destruct Hhashed as [x [??]].
    opose proof (Hstep x.2 _) as [_ ->]; [set_solver|done].
  - case_decide as Hcoll; [done|].
    destruct Hstep as [_ ->].
    apply gset_bijective_extend; [done|set_solver..].
Qed.

Lemma hashes_mono {t i k s0 s1} :
  valid_trace t →
  t.(states) !! i = Some s0 →
  t.(states) !! (i + k) = Some s1 →
  s0.(hashes) ⊆ s1.(hashes).
Proof.
  intros Hvalid Hlook_st_i.
  generalize dependent s1.
  induction k.
  { replace (i + 0) with (i) in * by lia. naive_solver. }
  intros st_Sik Hlook_st_Sik.
  assert (∃ st_ik, t.(states) !! (i + k) = Some st_ik) as [st_ik Hlook_st_ik].
  { apply lookup_lt_is_Some. apply lookup_lt_Some in Hlook_st_Sik. lia. }
  specialize (IHk _ Hlook_st_ik).
  destruct Hvalid as [_ Hsteps].
  opose proof (Forall3_lookup_r _ _ _ _ _ _ Hsteps) as
    (st_ik' & la_ik & Hlook_st_ik' & Hlook_la_ik & Hstep); clear Hsteps.
  { replace (i + S k) with (S (i + k)) in * by lia. by rewrite lookup_drop. }
  apply lookup_take_Some in Hlook_st_ik' as [? _].
  simplify_eq/=.
  etrans; [done|]; clear s0 Hlook_st_i IHk.
  rewrite /step in Hstep.

  case_match eqn:Hop. case_decide as Hhashed.
  - destruct Hhashed as [x [??]].
    opose proof (Hstep x.2 _) as [_ ->]; [set_solver|done].
  - case_decide as Hcoll; [done|].
    destruct Hstep as [_ ->].
    set_solver.
Qed.

Lemma hashes_incl {t i s m h} :
  valid_trace t →
  t.(labels) !! i = Some (mk_trans (hash m) (ret_hash h)) →
  t.(states) !! S i = Some s →
  (m, h) ∈ s.(hashes).
Proof.
  intros Hvalid Hlook_la_i Hlook_st_Si.
  destruct Hvalid as [_ Hsteps].
  opose proof (Forall3_lookup_m _ _ _ _ _ _ Hsteps) as
    (st_i & st_Si' & _ & Hlook_st_Si' & Hstep); [done|]; clear Hsteps.
  rewrite lookup_drop in Hlook_st_Si'. simplify_eq/=.
  rewrite /step in Hstep.

  case_match eqn:Hop. inv Hop. case_decide as Hhashed.
  - destruct Hhashed as [x [??]].
    opose proof (Hstep x.2 _) as [[=] ->]; set_solver.
  - case_decide as Hcoll; [done|].
    destruct Hstep as [[=] ->]. set_solver.
Qed.

Lemma coll_resis {t i k h m0 m1} :
  valid_trace t →
  (* hashes equal. *)
  t.(labels) !! i = Some (mk_trans (hash m0) (ret_hash h)) →
  t.(labels) !! (i + k) = Some (mk_trans (hash m1) (ret_hash h)) →
  (* inputs equal. *)
  m0 = m1.
Proof.
  intros Hvalid Hlook_la_i Hlook_la_ik.
  pose proof Hvalid as [_ Hsteps].
  opose proof (Forall3_lookup_m _ _ _ _ _ _ Hsteps) as
    (_ & st_Si & _ & Hlook_st_Si & _).
  { apply Hlook_la_i. }
  opose proof (Forall3_lookup_m _ _ _ _ _ _ Hsteps) as
    (_ & st_Sik & _ & Hlook_st_Sik & _).
  { apply Hlook_la_ik. }
  rewrite lookup_drop in Hlook_st_Si.
  rewrite lookup_drop in Hlook_st_Sik.

  (* use our helper lemmas about hashes. *)
  pose proof (hashes_incl Hvalid Hlook_la_i Hlook_st_Si) as Hincl0.
  pose proof (hashes_incl Hvalid Hlook_la_ik Hlook_st_Sik) as Hincl1.
  pose proof (hashes_mono Hvalid Hlook_st_Si Hlook_st_Sik) as Hsubset.
  pose proof (hashes_bij Hvalid Hlook_st_Sik) as Hbij.

  (* carry (m0, h) to (i + k) idx. *)
  opose proof (proj1 (elem_of_subseteq _ _) Hsubset _ Hincl0) as Hincl1'.
  (* use bij to derive equality. *)
  opose proof (gset_bijective_eq_iff _ _ _ _ _ Hbij Hincl1 Hincl1') as ?.
  naive_solver.
Qed.

End hashes.
