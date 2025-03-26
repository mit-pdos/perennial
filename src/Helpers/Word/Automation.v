From stdpp Require Import prelude.
From iris.proofmode Require Import proofmode.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers Properties.

Import Ltac2.
Set Default Proof Mode "Classic".

(*
  The high-level plan: normalize the entire proof context to be in terms of .
  The steps this tactic follows
  - Unfold the types (w64) to expose the underlying [word.rep ...] type. All
    automation hereafter only needs to concern itself with any word
    satisfying the word laws spelled out in [word.ok]
  - Rewrite everything to be in terms of [word.unsigned]; even [word.signed]
    gets replaced with a sign-wrapped [word.unsigned]. All equalities of
    [word.rep] are replaced with [Z] equalities.
  - Eliminate all word ops
  - zify
  - compute away Z constants.
  - lia.
 *)

Module word.

Import Interface.word.
Local Lemma decision_assume_opposite `{!Decision P} : (¬ P → False) → P.
Proof. by destruct (decide P). Qed.

Local Lemma word_eq_iff_Z_eq {width} {word : word width} {word_ok : ok word} (x y : word):
  x = y ↔ unsigned x = unsigned y.
Proof. split; first by intros ->. apply inj. apply _. Qed.

Local Lemma unsigned_slu' {width} {word : word width} {word_ok : word.ok word}
  (x y : word) :
  Z.lt (unsigned y) width -> unsigned (slu x y) = wrap ((unsigned x) * (2^(unsigned y))).
Proof.
  intros. rewrite unsigned_slu //. pose proof (word.unsigned_range y) as [??].
  rewrite Z.shiftl_mul_pow2 //.
Qed.

Local Lemma unsigned_sru' {width} {word : word width} {word_ok : word.ok word}
  (x y : word) :
  Z.lt (unsigned y) width -> unsigned (sru x y) = ((unsigned x) / (2^(unsigned y))).
Proof.
  pose proof (word.unsigned_range y) as [??].
  pose proof (word.unsigned_range x) as [??].
  intros. rewrite unsigned_sru //. rewrite Z.shiftr_div_pow2 //. rewrite wrap_small //.
  Z.div_mod_to_equations. nia.
Qed.

Import Printf.

Ltac2 verbose_logger m := printf "word: %a" (fun () () => m) ().
Ltac2 handle_goal logger :=
  lazy_match! goal with
  | [ |- False ] => ()
  | [ |- _ ] => first [
          apply decision_assume_opposite; intros | (* if decidable, assume the opposite; *)
          logger (fprintf "eliminating goal and trying to prove false instead"); Std.cut 'False
        ]
  end.

Ltac2 unfold_w_whatever () :=
  unfold W64, W32, (* W16, *) W8, w64, w32, (* w16, *) w8 in *.

Ltac2 normalize_to_word_unsigned () :=
  (* eliminate sint.Z *)
  rewrite -> ?word.signed_eq_swrap_unsigned in *;
  (* eliminate any (eq (word.)*)
  rewrite -> ?word_eq_iff_Z_eq in *
.
Print Ltac2 Signatures.

(* FIXME: check for these and throw an error if found. *)
Ltac2 unsupported_ops () : constr list :=
  ['eqb; 'ltu; 'lts; 'mulhss ; 'mulhsu ; 'mulhuu ; 'eqb ; 'ltu ; 'lts ; 'srs; 'divs; 'mods ] .

(* This eliminates [@eq (word.rep) _ _], which should the following rewrites
   never reintroduce. *)
Ltac2 word_elim_eq_laws () : constr list := [
    'word_eq_iff_Z_eq
  ].

(* These equalities have no sideconditions, and should always be used to
   rewrite. *)
Ltac2 word_op_laws_without_side_goal () : constr list :=
  [ 'unsigned_of_Z; 'of_Z_unsigned; 'unsigned_add; 'unsigned_sub;
    'unsigned_opp; 'unsigned_or; 'unsigned_and; 'unsigned_xor;
    'unsigned_not; 'unsigned_ndn; 'unsigned_mul
    (* 'signed_mulhss; 'signed_mulhsu; 'unsigned_mulhuu; 'unsigned_eqb; *)
    (* 'unsigned_ltu; 'signed_lts *)
  ].

Ltac2 word_elim_of_Z_laws () : constr list :=
  [ 'unsigned_of_Z (* 'of_Z_unsigned *) ].
(* NOTE: don't want to rewrite by [of_Z_unsigned], since it results in a term
wrapped by [unsigned] becoming no longer wrapped. *)

(* These equalities have 1 sidegoal, and the string is a description of what
   that sidegoal must prove. The string is used in error messages. *)
Ltac2 word_op_laws_with_side_goals () : (constr * string) list := [
    ('unsigned_slu', "slu: the shift amount must be less than width");
    ('unsigned_sru', "sru: the shift amount must be less than width");
    (* signed_srs *)
    ('word.unsigned_divu_nowrap, "divu: the divisor must be non-zero");
    (* signed_divs *)
    ('word.unsigned_modu_nowrap, "modu: the modulus must be non-zero")
      (* signed_mods *)
  ].

Ltac2 mutable solve_word () := ().

Ltac2 Type exn ::= [Word_side_goal_failed (string, exn)].
Ltac2 Type exn ::= [Word_side_goal_not_expected (constr)].

Print Ltac2 Signatures.
Ltac2 solve_side_goal logger (err : string) (parent_hyp : ident) :=
  logger (fprintf "side goal: begin (%s) on %t" err (Control.goal ()));
  let parent_expr := Constr.type (Control.hyp parent_hyp) in
  Std.clear [parent_hyp];
  orelse (fun () => Control.enter solve_word)
    (fun ex =>
       let m := (fprintf "side goal failed: %s from expression: %a %t" err (fun () () => Message.force_new_line) ()
                   parent_expr) in
       Control.throw (Word_side_goal_failed (Message.to_string m) ex));
  Control.enter
    (fun () =>
       Control.throw (Tactic_failure (Some (Message.of_string "fatal solve_side_goal: expected [solve_word] to succeed or throw an exception")))
    ).

Ltac2 rewrite_everywhere logger law side_goal_solver :=
  let make_rw law := { Std.rew_orient := Some Std.LTR;
                       Std.rew_repeat := Std.RepeatPlus;
                       Std.rew_equatn := (fun () => (law, Std.NoBindings)) } in
  let make_cl h := Some { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                          Std.on_concl := Std.NoOccurrences } in
  first0 (List.map
            (fun h () =>
               let (h, _, _) := h in
               logger (fprintf "trying rewrite %t in %I" law h);
               rewrite0 false [make_rw law] (make_cl h) (Some (fun () => side_goal_solver h));
               Message.print (Message.of_string "succeeded");
               Control.enter (fun () => logger (fprintf "succeeded word law %t in hypothesis %I" law h))
            ) (Control.hyps ())).

Ltac2 no_side_condition logger h :=
  logger (fprintf "fatal: unexpected side condition in %I" h);
  Control.throw (Word_side_goal_not_expected (Control.goal ()));
  ().

(** Precondition: in all "relevant" hypotheses, all terms of type [word.rep _]
    are either fed into [uint.Z] or fed into a [word] operation.

   Postcondition: in all "relevant" hypotheses: all terms of type [word.rep _]
   are directly wrapped in a [uint.Z], with some exceptions explained next.

   Exceptions: if there are [word.rep]s showing up underneath a word-opaque
   term. E.g. if [x y : w64] and [f : w64 → w64] is some function that's not a
   standard word op, then [uint.Z [word.add (f x) y]] will turn into
   [wrap (Z.add uint.Z (f x) (uint.Z y)]], which has the [word.rep] x that is
   not getting passed into [uint.Z]. In this case, [f x] is treated as opaque
   and unrelated to [x]. Any relationships should be proven and stated upfront.
 *)
Ltac2 eliminate_word_ops logger :=
  let rewrite_everywhere := rewrite_everywhere logger in
  let no_side_condition := no_side_condition logger in

  (* Eliminate word equality. *)
  repeat (first0 (List.map (fun lem () => rewrite_everywhere lem no_side_condition)
                    (word_elim_eq_laws ())));

  (* Eliminate [signed] in favor of [swrap ∘ unsigned] *)
  repeat (rewrite_everywhere 'word.signed_eq_swrap_unsigned no_side_condition);

  (* At this point, every relevant term of type [rep] is wrapped in either
     a word op or [unsigned]. *)
  (* Eliminate word ops (add, mul, etc.). *)
  let tacs := List.map (fun law () => rewrite_everywhere law no_side_condition)
                (word_op_laws_without_side_goal ()) in
  let tacs' := List.map (fun y () =>
                           let (law, err_str) := y in
                           rewrite_everywhere law (solve_side_goal logger err_str)
                 )
                (word_op_laws_with_side_goals ()) in
  let tacs := List.append tacs' tacs in
  repeat (first0 tacs);

  (* At this point, every relevant term of type [rep] is wrapped in
     [unsigned]. *)
  (* Eliminate [of_Z]. *)
  repeat (first0 (List.map (fun lem () => rewrite_everywhere lem no_side_condition)
                    (word_elim_of_Z_laws ())));
  ().

Ltac2 unfold_word_wrap () :=
  unfold wrap, swrap in *.

Ltac2 noop_logger m := ().
Ltac2 all_but_lia () :=
  handle_goal verbose_logger;
  unfold_w_whatever ();
  eliminate_word_ops verbose_logger;
  unfold_word_wrap ()
  (* TODO: simplify Z constants *)
.

Ltac2 Set solve_word as old :=
  fun () => all_but_lia ();
         ltac1:(zify; Z.div_mod_to_equations; lia).

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (sint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (sint.Z delta')) (W64 32).
Proof.
  intros. subst.
  unfold W64 in *. unfold w64 in *.
  Time unshelve ltac2:(Control.enter all_but_lia).
  zify. Z.div_mod_to_equations.
  lia.
  {
    unfold wrap in *. zify. Z.div_mod_to_equations. lia.
  }
  ltac2:(rewrite -> unsigned_slu' in H).

  ltac2:(let make_rw law := { Std.rew_orient := Some Std.LTR;
                              Std.rew_repeat := Std.RepeatPlus;
                              Std.rew_equatn := (fun () => (law, Std.NoBindings)) } in
         let make_cl h := Some { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                                 Std.on_concl := Std.NoOccurrences } in
         rewrite0 false [make_rw 'unsigned_of_Z] (make_cl @H)
           (Some (
                (no_side_condition verbose_logger) @H))
        ).

  ltac2:(let make_rw law := { Std.rew_orient := Some Std.LTR;
                              Std.rew_repeat := Std.RepeatPlus;
                              Std.rew_equatn := (fun () => (law, Std.NoBindings)) } in
         let make_cl h := Some { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                                 Std.on_concl := Std.NoOccurrences } in
         rewrite0 false [make_rw 'unsigned_of_Z] (make_cl @H)
           (Some ((fun h () => no_side_condition verbose_logger h) @H))).



Qed.

Lemma test

End word.

Lemma unsigned_U64 z : uint.Z (W64 z) = word.wrap (word:=w64_word_instance) z.
Proof.
  unfold W64; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U32 z : uint.Z (W32 z) = word.wrap (word:=w32_word_instance) z.
Proof.
  unfold W32; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U8 z : uint.Z (W8 z) = word.wrap (word:=w8_word_instance) z.
Proof.
  unfold W8; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma signed_U64 z : sint.Z (W64 z) = word.swrap (word:=w64_word_instance) z.
Proof.
  unfold W64; rewrite word.signed_of_Z; auto.
Qed.

Lemma signed_U32 z : sint.Z (W32 z) = word.swrap (word:=w32_word_instance) z.
Proof.
  unfold W32; rewrite word.signed_of_Z; auto.
Qed.

Lemma w64_val_f_equal (x y: w64) :
  x = y →
  uint.Z x = uint.Z y ∧ sint.Z x = sint.Z y.
Proof. by intros ->. Qed.

Lemma w32_val_f_equal (x y: w32) :
  x = y →
  uint.Z x = uint.Z y ∧ sint.Z x = sint.Z y.
Proof. by intros ->. Qed.

Lemma w64_val_neq (x y: w64) :
  x ≠ y →
  uint.Z x ≠ uint.Z y ∧ sint.Z x ≠ sint.Z y.
Proof.
  intros Hne.
  split; intros Heq; contradiction Hne.
  - apply (inj uint.Z); auto.
  - apply (inj sint.Z); auto.
Qed.

Lemma f_not_equal {A B} (f: A → B) (x y: A) :
  f x ≠ f y →
  x ≠ y.
Proof. congruence. Qed.

Lemma word_unsigned_ltu {width: Z} (word: Interface.word width) {Hok: word.ok word} (x y: word) :
  word.ltu x y = bool_decide (uint.Z x < uint.Z y).
Proof.
  rewrite word.unsigned_ltu.
  destruct (Z.ltb_spec0 (uint.Z x) (uint.Z y)).
  - rewrite bool_decide_eq_true_2; auto.
  - rewrite bool_decide_eq_false_2; auto.
Qed.

Definition w64_unsigned_ltu : ∀ (x y: w64), _ := word_unsigned_ltu w64_word_instance.

Lemma w32_val_neq (x y: w32) :
  x ≠ y →
  uint.Z x ≠ uint.Z y ∧ sint.Z x ≠ sint.Z y.
Proof.
  intros Hne.
  split; intros Heq; contradiction Hne.
  - apply (inj uint.Z); auto.
  - apply (inj sint.Z); auto.
Qed.

Create HintDb word.

Hint Rewrite unsigned_U64 unsigned_U32 unsigned_U8 : word.

Ltac simpl_word_constants :=
  repeat match goal with
         | [ H: context[word.unsigned (W64 ?x)] |- _ ] => change (uint.Z x) with x in H
         | [ |- context[word.unsigned (W64 ?x)] ] => change (uint.Z x) with x
         | [ H: context[word.unsigned (W32 ?x)] |- _ ] => change (uint.Z (W32 x)) with x in H
         | [ |- context[word.unsigned (W32 ?x)] ] => change (uint.Z (W32 x)) with x
         | [ H: context[word.unsigned (W8 ?x)] |- _ ] => change (uint.Z (W32 8)) with x in H
         | [ |- context[word.unsigned (W8 ?x)] ] => change (uint.Z (W8 x)) with x
        (* TODO: add sint versions *)
    end.

Ltac word_cleanup_core :=
  (* this is so that the following pattern succeeds when (for some reason)
  instead of w64 we have its unfolding *)
  fold w64 w32 w8 in *;
  repeat autounfold with word in *;
  try lazymatch goal with
      (* TODO: this isn't the right strategy if the numbers in the goal are used
      signed. [word] can try both via backtracking, but this can't be part of
      "cleanup".  *)
      | |- context [@eq word.rep _ _] => rewrite word.unsigned_inj_iff
      end;
  simpl_word_constants;
  (* can't replace some of these with [autorewrite], probably because typeclass inference
  isn't the same *)
  repeat (
      rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
        ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
        ?word.unsigned_mul,
        ?w64_unsigned_ltu
      || rewrite -> ?word.unsigned_of_Z, ?word.of_Z_unsigned in *
      || autorewrite with word in *
    );
  repeat match goal with
         | _ => progress simpl_word_constants
         | [ H: @eq w64 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_f_equal in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_f_equal in H as [H H']
         | [ H: not (@eq w64 _ _) |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_neq in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_neq in H as [H H']
         end;
  repeat match goal with
         | [ |- context[uint.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[uint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ |- context[sint.Z ?x] ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         | [ H: context[sint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite -> (@wrap_small _ word ok z) by lia
         | |- context[@word.swrap _ ?word ?ok ?z] =>
           rewrite -> (@swrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite -> (Z2Nat.id z) by lia
         end.

(* TODO: only for backwards compatibility.

[word_cleanup] should be be replaced with a new tactic
that does a subset of safe and useful rewrites *)
Ltac word_cleanup := word_cleanup_core; try lia.

Ltac word := first [
                 solve [
                     try iPureIntro;
                     word_cleanup_core;
                     unfold word.wrap in *;
                     (* NOTE: some inefficiency here because [lia] will do [zify]
                 again, but we can't rebind the zify hooks in Ltac *)
                     zify; Z.div_mod_to_equations; lia
                   ]
               | fail 1 "word could not solve goal"
               ].

Lemma test_nat_thru_w64_id (x : nat) :
  Z.of_nat x < 2^64 ->
  uint.nat (W64 (Z.of_nat x)) = x.
Proof. word. Qed.

(* TODO: these lemmas aren't really part of the automation, but are proven using
[word]. They should go somewhere else. *)

Theorem Z_u32 z :
  0 <= z < 2 ^ 32 ->
  uint.Z (W32 z) = z.
Proof. word. Qed.

Lemma u32_Z (x : u32) :
  W32 (uint.Z x) = x.
Proof. word. Qed.

Theorem Z_u64 z :
  0 <= z < 2 ^ 64 ->
  uint.Z (W64 z) = z.
Proof. word. Qed.

Lemma u64_Z (x : u64) :
  W64 (uint.Z x) = x.
Proof. word. Qed.

Lemma w64_to_nat_id (x : w64) :
  W64 (Z.of_nat (uint.nat x)) = x.
Proof. word. Qed.

Lemma seq_U64_NoDup (m len : Z) :
  (0 ≤ m)%Z →
  (m+len < 2^64)%Z →
  NoDup (W64 <$> seqZ m len).
Proof.
  intros Hlb Hub. apply NoDup_fmap_2_strong; cycle 1.
  { apply NoDup_seqZ. }
  Set Printing Coercions. (* This is impossible to work on otherwise... *)
  clear- Hlb Hub. intros x y Hx%elem_of_seqZ Hy%elem_of_seqZ Heq.
  rewrite <-(Z_u64 x), <-(Z_u64 y).
  - by rewrite Heq.
  - word.
  - word.
Qed.

Lemma u64_round_up_spec x div :
  uint.Z x + uint.Z div < 2^64 →
  uint.Z div > 0 →
  uint.Z (u64_round_up x div) `mod` (uint.Z div) = 0 ∧
  uint.Z x < uint.Z (u64_round_up x div) ∧
  uint.Z (u64_round_up x div) < 2^64.
Proof.
  intros. unfold u64_round_up.
  rewrite -> word.unsigned_mul_nowrap, word.unsigned_divu_nowrap by word.
  rewrite -> word.unsigned_add_nowrap by word.
  split.
  { rewrite Z.mul_comm. apply ZLib.Z.Z_mod_mult'. }
  word.
Qed.
