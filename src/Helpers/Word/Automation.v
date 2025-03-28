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

Ltac2 handle_unsafe t :=
  match Control.case t with
  | Val (v, _) => v
  | Err (e) => Control.throw e (* TODO: wrap with a better error *)
  end.

Ltac2 Notation "do:" t(thunk(tactic)) := handle_unsafe t.

Ltac2 normalize_to_word_unsigned () :=
  (* eliminate sint.Z *)
  do: rewrite -> ?word.signed_eq_swrap_unsigned in *;
  (* eliminate any (eq (word.)*)
  do: rewrite -> ?word_eq_iff_Z_eq in *.

(* FIXME: check for these and throw an error if found. *)

(* delayed open_constr *)
Local Ltac2 Notation "delayed:(" t(thunk(open_constr)) ")" := t.

Local Ltac2 Notation "delayed:[" ts(list1(thunk(open_constr))) "]" := ts.

Ltac2 unsupported_ops () : (unit -> constr) list :=
  delayed:[eqb ltu lts mulhss mulhsu mulhuu eqb ltu lts srs divs mods].

(* These equalities have no sideconditions, and should always be used to
   rewrite. *)
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

Ltac2 mutable solve_word_unsafe () := ().

Ltac2 Type exn ::= [Word_side_goal_failed (string, exn)].
Ltac2 Type exn ::= [Word_side_goal_not_expected (constr)].

(* safe *)
Ltac2 solve_side_goal logger (err : string) (parent_hyp : ident) :=
  logger (fprintf "side goal: begin (%s) on %t" err (Control.goal ()));
  let parent_expr := Constr.type (Control.hyp parent_hyp) in
  Std.clear [parent_hyp];
  orelse solve_word_unsafe
    (fun ex =>
       let m := (fprintf "side goal failed: %s from expression: %a %t" err (fun () () => Message.force_new_line) ()
                   parent_expr) in
       Control.throw (Word_side_goal_failed (Message.to_string m) ex));
  Control.enter
    (fun () =>
       Control.throw (Tactic_failure (Some (Message.of_string "fatal solve_side_goal: expected [solve_word] to succeed or throw an exception")))
    ).

(* safe *)
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
           Std.set false (fun () => (None, '(Zpos _)))
             { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
               Std.on_concl := Std.NoOccurrences }
    ))
    (Control.hyps ()).

Ltac2 subst_all () :=
  List.iter (fun h => let (h, _, _) := h in orelse (fun () => Std.subst [h]) (fun _ => ()))
            (Control.hyps ()).

Ltac2 all_but_lia () :=
  handle_goal noop_logger;
  unfold_w_whatever ();
  eliminate_word_ops noop_logger;
  unfold_word_wrap ();
  simplify_Z_constants () (* FIXME: should probably simplify Z constants after zify *)
.

Ltac2 Set solve_word_unsafe as old :=
  (fun () => all_but_lia ();
         set_all ();
         ltac1:(zify; Z.div_mod_to_equations);
         subst_all ();
         ltac1:(lia)).

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (sint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (sint.Z delta')) (W64 32).
Proof.
  intros. subst.
  Time ltac2:(solve_word_unsafe ()).
Qed.

End word.

Tactic Notation "word" :=
  try iPureIntro; ltac2:(word.solve_word_unsafe ()).
