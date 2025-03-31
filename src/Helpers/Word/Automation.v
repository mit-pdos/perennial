From Ltac2 Require Import Ltac2.
From stdpp Require Import prelude.
From iris.proofmode Require Import proofmode.
From Coq Require Import ssreflect.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers.
Set Default Proof Mode "Classic".

(** User's guide to the [word] tactic.

    The [word] tactic tries to solve goals related to [w64, w32, w16, w8]
  arithmetic reasoning; if it can't fully solve it, it leaves the proof state
  unchanged. [word] is good at solving "linear word arithmetic": expressions
  that are other expressions multiplied by constants or the addition of other
  expressions together along with (in)equalities. E.g.  [word.mul (W32 4)
  (word.add x y)] is a "linear" expression.

    To have [word] automatically unfold definitions before trying to solve the
  goal, add a hint the the [word] HintDb, by doing [Hint Unfold foo : word.]

    [word] is likely to fail at handling non-linear expressions, e.g. [word.mul
  x y] where [x] and [y] are both non-constants. In some proofs, it is possible
  to handle non-linear reasoning first (e.g. by removing a common factor on both
  sides of an equality) and then successfully use [word] to finish the proof.
  [word] is also likely to fail at handling bitwise operations like [word.and],
  [word.or], etc.

  These word operations are entirely unsupported:
    [eqb ltu lts mulhss mulhsu mulhuu eqb ltu lts srs divs mods].
 *)


(** Developer's guide to the [word] tactic.

    At a high-level, [word] is rewrites everything it can to involve arithmetic
  in [Z] (as opposed to operations on [word]), then it invokes [lia]. In more detail,
  the steps [word] tactic takes are:
  - Unfold types like [w64] to expose the underlying [word.rep ...] type.
    The remaining steps work with arbitrary [word] types, rather than
    hard-coding [w64], [w32], etc.
  - Eliminate [word.signed] and [@eq (word.rep) a b]. The [Z] value [word.signed
    x] is rewritten into [word.swrap (word.unsigned x)]. [@eq (word.rep) a b] is
    replaced with the equivalent proposition [@eq Z (uint.Z a) (uint.Z b)].
  - Eliminate all word ops. This involves rewriting by the laws in [word.ok]
    with some alterations. Altered forms of the bit shifting laws are used in
    which [Z.shiftl] and [Z.shiftr] are replaced with multiplication/division by
    the appropriate power of 2.
  - Evaluate Z constants.
  - zify; Z.div_mod_to_equations.
  - lia.
 *)

Module word.

Import Interface.word.
Section lemmas.
(* Lemmas used in the word tactic tactics. *)
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

End lemmas.

Import Printf.

Ltac2 verbose_logger m := printf "word: %a" (fun () () => m) ().

(* Normalize the proof state so the goal is [False] and everything relevant is in
   the hypotheses. *)
Ltac2 handle_goal logger :=
  lazy_match! goal with
  | [ |- False ] => ()
  | [ |- _ ] => first [
          apply decision_assume_opposite; intros | (* if decidable, assume the opposite; *)
          logger (fprintf "eliminating goal and trying to prove false instead");
          apply False_ind
        ]
  end.

Create HintDb word.

Ltac2 unfold_w_whatever () :=
  ltac1:(autounfold with word in * );
  unfold W64, W32, (* W16, *) W8, w64, w32, (* w16, *) w8 in *.

(* Runs [t] and panics unrecoverably if it throws an exception. *)
Ltac2 handle_unsafe t :=
  match Control.case t with
  | Val (v, _) => v
  | Err (e) => Control.throw e (* TODO: wrap with a better error *)
  end.

Ltac2 normalize_to_word_unsigned () :=
  (* eliminate sint.Z *)
  handle_unsafe (fun () => rewrite -> ?word.signed_eq_swrap_unsigned in * );
  (* eliminate any (eq (word.)*)
  handle_unsafe (fun () => rewrite -> ?word_eq_iff_Z_eq in * ).

(* Notation to more easily write [fun () => open_constr:(t)]. Thunks are used in
   rewrite laws because there are evars in the word lemmas that only get
   instantiated when a rewrite is successful (evars such as the particular
   [width] to instantiate a law with). *)
Local Ltac2 Notation "delayed:(" t(thunk(open_constr)) ")" := t.

Local Ltac2 Notation "delayed:[" ts(list1(thunk(open_constr))) "]" := ts.

(* TODO: check for these and throw an error if found. *)
Ltac2 unsupported_ops () : (unit -> constr) list :=
  delayed:[eqb ltu lts mulhss mulhsu mulhuu eqb ltu lts srs divs mods].

(* These equalities have no sideconditions *)
Ltac2 word_op_laws_without_side_goal () : (unit -> constr) list :=
  delayed:[unsigned_add unsigned_sub unsigned_opp unsigned_or
             unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul].
    (* 'signed_mulhss; 'signed_mulhsu; 'unsigned_mulhuu; 'unsigned_eqb; *)
    (* 'unsigned_ltu; 'signed_lts *)

(* These equalities have 1 sidegoal, and the string is a description of what
   that sidegoal must prove. The string is used in error messages. *)
Ltac2 word_op_laws_with_side_goals () : ((unit -> constr) * string) list := [
    (delayed:(unsigned_slu'), "slu: the shift amount must be less than width");
    (delayed:(unsigned_sru'), "sru: the shift amount must be less than width");
    (* signed_srs *)
    (delayed:(word.unsigned_divu_nowrap), "divu: the divisor must be non-zero");
    (* signed_divs *)
    (delayed:(word.unsigned_modu_nowrap), "modu: the modulus must be non-zero")
      (* signed_mods *)
  ].

Ltac2 mutable solve_unsafe () := ().

Ltac2 Type exn ::= [Word_side_goal_failed (string, exn)].
Ltac2 Type exn ::= [Word_side_goal_not_expected (constr)].

(* safe *)
Ltac2 solve_side_goal logger (err : string) (parent_hyp : ident) :=
  logger (fprintf "side goal: begin (%s) on %t" err (Control.goal ()));
  let parent_expr := Constr.type (Control.hyp parent_hyp) in
  Std.clear [parent_hyp];
  orelse solve_unsafe
    (fun ex =>
       let m := (fprintf "side goal failed: %s from expression: %a %t" err (fun () () => Message.force_new_line) ()
                   parent_expr) in
       Control.throw (Word_side_goal_failed (Message.to_string m) ex));
  Control.enter
    (fun () =>
       Control.throw (Tactic_failure (Some (Message.of_string "fatal solve_side_goal: expected [solve_word] to succeed or throw an exception")))
    ).

(* safe, should not throw exceptions. *)
Ltac2 try_rewrite_anywhere logger dlaw side_goal_solver : bool :=
  let make_rw law := { Std.rew_orient := Some Std.LTR;
                       Std.rew_repeat := Std.RepeatPlus;
                       Std.rew_equatn := (fun () => (law, Std.NoBindings)) } in
  let make_cl h := Some { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                          Std.on_concl := Std.NoOccurrences } in
  let rec loop hyps :=
    (match hyps with
     | [] => false
     | (h, _, _) :: hyps =>
         orelse
           (fun () =>
              let law := dlaw () in
              logger (fprintf "trying rewrite %t in %I" law h);
              rewrite0 false [make_rw law] (make_cl h) (Some (fun () => side_goal_solver h));
              if (Int.equal (Control.numgoals ()) 1) then ()
              else Control.throw (Tactic_failure (Some (Message.of_string "word fatal: rewrite failed")));
              logger (fprintf "succeeded word law %t in hypothesis %I" law h);
              true)
           (fun _ => loop hyps) (* [rewrite0] didn't find anything to rewrite *)
     end) in
  loop (Control.hyps ()).

Ltac2 no_side_condition logger h :=
  logger (fprintf "fatal: unexpected side condition in %I" h);
  Control.throw (Word_side_goal_not_expected (Control.goal ()));
  ().

(** All terms of type [word.rep _] that are either fed into [uint.Z] or fed into
    a [word] operation, which is eventually fed into [uint.Z], are called
    "relevant".

   Postcondition: in all "relevant" terms: all sub-terms of type [word.rep _]
   are directly wrapped in a [uint.Z]. In other words, there are no more [word]
   operations, only [word.rep] values that cannot be broken down any further.

   An example of "irrelevant" terms are [word.rep]s showing up underneath a
   word-opaque term. E.g. if [x y : w64] and [f : w64 → w64] is some function
   that's not a standard word op, then [uint.Z [word.add (f x) y]] will turn
   into [wrap (Z.add uint.Z (f x) (uint.Z y)]], which has the [word.rep] x that
   is not getting passed into [uint.Z]. In this case, [f x] is treated as opaque
   and unrelated to [x]. Any relationships e.g. beween [f x] and [x] should be
   proven and added to the context before running [word].
 *)
Ltac2 eliminate_word_ops logger :=
  let try_rewrite_anywhere := try_rewrite_anywhere logger in
  let no_side_condition := no_side_condition logger in
  let rec loop f := if (f ()) then loop f else () in

  (* Eliminate word equality, which should following rewrites should never reintroduce. *)
  loop (fun () => try_rewrite_anywhere (delayed:(word_eq_iff_Z_eq)) no_side_condition);

  (* Eliminate [signed] in favor of [swrap ∘ unsigned]. *)
  loop (fun () => try_rewrite_anywhere (delayed:(word.signed_eq_swrap_unsigned)) no_side_condition);

  (* At this point, every relevant term of type [rep] is wrapped in either
     a word op or [unsigned]. *)
  (* Eliminate word ops (add, mul, etc.). *)
  let rws := List.map (fun law () => try_rewrite_anywhere law no_side_condition)
                (word_op_laws_without_side_goal ()) in
  let rws' := List.map (fun y () =>
                           let (law, err_str) := y in
                           try_rewrite_anywhere law (solve_side_goal logger err_str)
                 )
                (word_op_laws_with_side_goals ()) in
  let rws := List.append rws' rws in
  loop (fun () => List.exist (fun f => f ()) rws);

  (* At this point, every relevant term of type [rep] is wrapped in
     [unsigned]. *)
  (* Eliminate [of_Z]. *)
  loop (fun () => try_rewrite_anywhere (delayed:(unsigned_of_Z)) no_side_condition);
    (* NOTE: don't want to rewrite by [of_Z_unsigned], since it results in a term
       wrapped by [unsigned] becoming no longer wrapped. *)
  ().

Ltac2 unfold_word_wrap () :=
  unfold wrap, swrap in *.

Ltac2 noop_logger _ := ().

Ltac2 eval_Z_constants_in_hyp (h : ident) : unit :=
  (* FIXME: This is a little inefficient: it repeatedly calls Std.eval_vm bottom-up. *)
  let rec try_eval_aux (e : constr) : (bool * constr) :=
    let (should_eval, e) :=
      lazy_match! e with
      | Zpos _ => (true, e)
      | Zneg _ => (true, e)
      | ?op ?a ?b =>
          let ((sa, a), (sb, b)) := (try_eval_aux a, try_eval_aux b) in
          let should_eval :=
            lazy_match! op with
            | Z.add => true | Z.sub => true
            | Z.mul => true | Z.div => true
            | Z.pow => true | Z.modulo => true
            | _ => false
            end
          in (Bool.and should_eval (Bool.and sa sb), '($op $a $b))
      | ?a ?b => let ((_, a), (_, b)) := (try_eval_aux a, try_eval_aux b) in
                (false, '($a $b))
      | _ => (false, e)
      end
    in
    if should_eval then (true, Std.eval_vm None e) else (false, e)
  in

  let try_eval () :=
    let e := Constr.type (Control.hyp h) in
    let (_, e') := try_eval_aux e in
    Std.change None (fun _ => e')
      { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences }
  in
  repeat0 (fun () => Control.progress try_eval).

Ltac2 simplify_Z_constants () :=
  List.iter (fun h => let (h, _, _) := h in eval_Z_constants_in_hyp h) (Control.hyps ()).

Ltac2 set_all () :=
  List.iter
    (fun h =>
       let (h, _, _) := h in
       repeat (
           lazy_match! Constr.type (Control.hyp h) with
           | context[Zpos ?x] => set (Zpos $x) in *
           | context[Zneg ?x] => set (Zneg $x) in *
           end
    )) (Control.hyps ()).

Ltac2 subst_all () :=
  List.iter (fun h => let (h, _, _) := h in orelse (fun () => Std.subst [h]) (fun _ => ()))
            (Control.hyps ()).

(* XXX: using ltac1 because constrs can't be directly used in patterns.
   Example workaround to do it in ltac2: https://github.com/rocq-prover/rocq/issues/13962
 *)
Ltac2 add_range_facts () :=
  ltac1:(
           repeat match goal with
             | [ H: context[uint.Z ?x] |- _ ] =>
                 lazymatch goal with
                 | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
                 | _ => pose proof (word.unsigned_range x)
                 end
           end
  ).

Ltac2 nat_cleanup () := rewrite -> ?Nat2Z.id in *.

Ltac2 normalize tac :=
  handle_goal noop_logger;
  nat_cleanup ();
  unfold_w_whatever ();
  eliminate_word_ops noop_logger;
  add_range_facts ();
  tac ();
  unfold_word_wrap ();
  simplify_Z_constants () (* FIXME: should probably simplify Z constants after zify *)
.

Ltac2 Set solve_unsafe as old :=
  (fun () => normalize (fun () => ());
         set_all ();
         ltac1:(zify; Z.div_mod_to_equations);
         subst_all ();
         ltac1:(lia)).

Ltac2 solve_unsafe_with tac :=
  normalize tac;
  set_all ();
  ltac1:(zify; Z.div_mod_to_equations);
  subst_all ();
  ltac1:(lia).
(* Add a warning/error for nonlinear arithmetic? Sometimes it's hard to
   notice. *)

Local Lemma test_sum_overflow_check (x y: u64) :
  uint.Z (word.add x y) < uint.Z x <-> uint.Z x + uint.Z y >= 2^64.
Proof.
  Time ltac2:(word.solve_unsafe ()).
Qed.

Local Lemma test_from_wg (delta' : w32) (delta : w64) :
  delta' = (W32 (sint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (sint.Z delta')) (W64 32).
Proof.
  intros. ltac2:(solve_unsafe ()).
Qed.

End word.

Tactic Notation "word" :=
  try iPureIntro; ltac2:(Control.enter word.solve_unsafe).

Tactic Notation "word" "with" tactic(t) :=
  try iPureIntro;
  let w := ltac2:(t |- Control.enter (fun () => word.solve_unsafe_with (fun () => Ltac1.run t))) in
  w t.

Tactic Notation "nat_cleanup" := ltac2:(word.nat_cleanup ()).
