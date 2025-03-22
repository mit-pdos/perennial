From iris.proofmode Require Import environments string_ident.
From New.proof Require Import proof_prelude.
From stdpp Require Import base.
Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 is_glob_identifier_char (x : char) : bool :=
  let n := Char.to_int x in
  let alpha_upper := Bool.and (Int.le n 90) (Int.le 65 n) in
  let alpha_lower := Bool.and (Int.le n 122) (Int.le 97 n) in
  let num := Bool.and (Int.le n 57) (Int.le 48 n) in
  if (Bool.or (Bool.or alpha_lower alpha_upper) num) then true
  else match (String.make 1 x) with
       | "_" => true | "'" => true | "*" => true | _ => false
       end.

Ltac2 is_glob_char (x : char) : bool := Int.equal 42 (Char.to_int x).

Ltac2 glob (handle_glob : string -> string -> string) (x : string) : string :=
  let word_start := Ref.ref 0 in
  let glob_pos : int option Ref.ref := Ref.ref None in

  let end_of_word i : string :=
    if (Int.lt (Ref.get word_start) i) then
      let gs := (String.sub x (Ref.get word_start) (Int.sub i (Ref.get word_start))) in
      match (Ref.get glob_pos) with
      | None => gs
      | Some p => (* and if it has a glob in it, then handle it. *)
          let gp := (Int.sub p (Ref.get word_start)) in
          let pref := (String.sub gs 0 gp) in
          let suff := (String.sub gs (Int.add gp 1) (Int.sub (String.length gs) (Int.add gp 1))) in
          handle_glob pref suff
      end
    else ""
  in

  let rec loop i :=
    if (Int.le (String.length x) i) then end_of_word i
    else (if is_glob_char (String.get x i) then (Ref.set glob_pos (Some i)) else ();
          if (is_glob_identifier_char (String.get x i)) then
            loop (Int.add i 1)
          else
            let s := end_of_word i in
            Ref.set word_start (Int.add i 1);
            Ref.set glob_pos None;
            String.app (String.app s (String.make 1 (String.get x i))) (loop (Int.add i 1)))
  in loop 0.

Ltac2 get_matching_hyps (check : string -> bool) : string list :=
  orelse (fun () =>
            lazy_match! goal with
            | [ |- envs_entails (Envs _ ?es _) _ ] =>
                let rec loop es :=
                  match! es with
                  | Esnoc ?es (base.ident.INamed ?n) _ =>
                      let s := StringToIdent.coq_string_to_string n in
                      if check s then s :: (loop es)
                      else loop es
                  | _ => []
                  end in
                loop es
            | [ |- ?g ] =>
                Message.print (Message.of_constr g);
                Control.enter (fun () => Message.print (Message.of_constr (Control.goal ())));
                Control.backtrack_tactic_failure "get_matching_hyps: was not run with Iris context"
            end)
    (fun _ => Control.throw (Tactic_failure (Some (Message.of_string "get_matching_hyps: oreslse failed")))).

Module String.
Ltac2 is_prefix pref s :=
  if Int.lt (String.length pref) (String.length s) then
    let pref' := (String.sub s 0 (String.length pref)) in
    String.equal pref pref'
  else false.

Ltac2 is_suffix suff s :=
  if Int.lt (String.length suff) (String.length s) then
    let suff' := (String.sub s (Int.sub (String.length s) (String.length suff)) (String.length suff)) in
    String.equal suff suff'
  else false.
End String.

Ltac2 handle_ipm_glob pref suff :=
  let minlen := Int.add (String.length pref) (String.length suff) in
  String.concat " "
    (get_matching_hyps
       (fun s => if (Int.ge (String.length s) minlen) then (* for overlapping [pref] and [suff] *)
                if String.is_prefix pref s then String.is_suffix suff s else false
              else false)).

Ltac2 glob_ipm s :=
  IdentToString.string_to_coq_string (glob handle_ipm_glob s).

Ltac2 iCombineNamed_tac2 (pat : string) (out : string) :=
  ltac1:(hyps out |- iAssert (_) with hyps as out; [iNamedAccu|])
          (Ltac1.of_constr ((glob_ipm (String.concat "" [ "["; pat; "]"]))))
          (Ltac1.of_constr (IdentToString.string_to_coq_string out)).

Ltac iCombineNamed_tac1 pat out :=
  let f := ltac2val:
      (pat |- Ltac1.of_constr ((glob_ipm (String.concat ""
                                           [ "["; (StringToIdent.coq_string_to_string (Option.get (Ltac1.to_constr pat))); "]"])))) in
  let hyps := f pat in
  iAssert (_) with hyps as out; [iNamedAccu|].

Tactic Notation "iCombineNamed" constr(ipat) "as" constr(out) :=
  iCombineNamed_tac1 ipat out.

Section test.
Context `{PROP : bi}.

Lemma test (P Q : PROP) :
  P -∗ P -∗ P -∗ P -∗ Q ∗ Q.
Proof.
  iIntros "H1 H2 P1 P2".
  (* NOTE: have not found a way to layer "glob" on top of exising Iris tactics.
     E.g. the `Tactic Notation` for `iSplitL` expects its argument to be a `constr`.
     When that constr is built up by embedding ltac2 as `ltac2:(glob_ipm
     whatever)`, that ltac2 actually gets run in a new proofview/goal just for
     constructing the constr. So, the goal is `?T` (to construct some constr,
     whose type is not even known).
     However, `glob_ipm` must be run against the actual IPM goal so it can see
     the named hypotheses.

     This implies that there's no way to use ltac to expand a glob in the constr
     arguments to existing Iris tactics.

     One solution: do glob expansion in something at the level of `envs_split_go`.
     Another possible solution: if tactics (like iSplitL) took e.g. ltac2
     strings as input, then computing the string ought to be run in the current
     proofview; the proofview changes when there are quotations/antiquotations.
   *)
  Time iCombineNamed "H*" as "Hout".
  iNamedSuffix "Hout" "_wg".
  iCombineNamed "*_wg" as "Hout".
Abort.

End test.

From iris.proofmode Require Import string_ident.
From iris.proofmode Require Import tactics environments intro_patterns monpred.

Local Ltac iNameReplace i name name' :=
  eapply (tac_name_replace i name name');
  [ first [ reduction.pm_reflexivity
          | fail 1 "iNamed: could not find" i ]
  | reduction.pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "iNamed: name not fresh" i
    | _ => idtac
    end
  ].

Local Ltac iNameIntuitionistic i i' :=
  eapply (tac_name_intuitionistic _ i i');
  [ first [ reduction.pm_reflexivity
          | fail 1 "iNamed: could not find" i ]
  | tc_solve
  | simpl; tc_solve
  | reduction.pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "iNamed: name not fresh" i
    | _ => idtac
    end
  ].

Local Ltac iNamePure i name :=
  string_to_ident_cps name ltac:(fun id =>
    let id := fresh id in
    iPure i as id
  ).

(* iNameHyp implements naming a hypothesis of the form [H: name ∷ P].

   The complete tactic is mutually recursive with iNamed_go for * patterns; this
   self-contained version takes iNamed_go as a parameter *)
Local Ltac iNameHyp_go_rx namef H iNamed_go :=
  let i := to_pm_ident H in
  lazymatch goal with
  | |- context[Esnoc _ i (named ?name ?P)] =>
    (* we check for some simple special-cases: *)
    let pat := intro_pat.parse_one name in
    lazymatch pat with
    | IIdent (INamed ?name) =>
      (* just rename one hypothesis *)
      let name' := eval compute in (namef name) in
      iNameReplace i name name'
    | IIntuitionistic (IIdent ?i') =>
      let name' := eval compute in (namef i') in
      iNameIntuitionistic i name'
    (* pure intros need to be freshened (otherwise they block using iNamed) *)
    | IPure (IGallinaNamed ?name) =>
      let name' := eval compute in (namef name) in
      iNamePure i name'
    (* the token "*" causes iNamed to recurse *)
    | IForall => change (Esnoc ?Δ i (named name P)) with (Esnoc Δ i P); iNamed_go namef i
    | _ =>
       (* we now do this only for backwards compatibility, which is a completely
       safe but inefficient sequence that handles persistent/non-persistent
       things correctly (most likely few patterns not covered above should even
       be supported) *)
       let Htmp := iFresh in
       iRename i into Htmp;
       iDestruct (from_named with Htmp) as pat;
       try iClear Htmp
    end
  | |- context[Esnoc _ i _] =>
    fail "iNameHyp: hypothesis" H "is not a named"
  | _ => fail 1 "iNameHyp: hypothesis" H "not found"
  end.

(* The core of iNamed is destructing a spine of separating conjuncts and naming
  each conjunct with iNameHyp; the implementation currently just calls iDestruct
  and then attempts to name the new anonymous hypotheses, but it would be better
  to parametrize the splitting and naming into a typeclass.
  We pass namef as a param because it's hard to curry mutually recursive ltacs. *)
Ltac iNamedDestruct_go_rx namef H iNameHyp :=
  (* we track the original name H0 here so that at the very end we can name the
  last conjunct if it isn't named (this is what PropRestore runs into - it can
  be destructed until a final Restore hypothesis) *)
  let rec go H0 H :=
      first [ iNameHyp namef H
            | lazymatch iTypeOf H with
              | Some (_, ?P) => tc_is_inhabited (IsSplittable P)
              | None => fail 1 "iNamed: hypothesis" H "not found"
              end;
              let Htmp1 := iFresh in
              let Htmp2 := iFresh in
              let pat := constr:(IList [[IIdent Htmp1; IIdent Htmp2]]) in
              iDestruct H as pat;
              iNameHyp namef Htmp1; go H0 Htmp2
            | (* reaching here means the last conjunct could not be named with
              iNameHyp; rather than leave it anonymous, restore the original
              name (note this could fail if that name was used by one of the
              inner names, which we don't handle here) *)
              iRename H into H0 ] in
  go H H.

(* this declaration defines iNamed by tying together all the mutual recursion *)
Local Ltac iNamed_go namef H :=
  lazymatch H with
  | 1%Z => let i := iFresh in iIntros i; iNamed_go namef i
  | 1%nat => let i := iFresh in iIntros i; iNamed_go namef i
  | _ =>
    (* first destruct the existentials, then split the conjuncts (but
    importantly only these two levels; the user must explicitly opt-in to
    destructing more existentials for conjuncts) *)
    try iDeexHyp H;
    iNamedDestruct_go namef H
  end with
  (* Ltac *)
  iNameHyp_go namef H := iNameHyp_go_rx namef H iNamed_go with
  (* Ltac *)
  iNamedDestruct_go namef H := iNamedDestruct_go_rx namef H iNameHyp_go.

Tactic Notation "iNamedDestruct" constr(H) := iNamedDestruct_go id H.
Tactic Notation "iNamed" constr(H) := iNamed_go (@id string) H.
Tactic Notation "iNamedPrefix" constr(H) constr(prefix) := iNamed_go (String.app prefix) H.
Tactic Notation "iNamedSuffix" constr(H) constr(suffix) := iNamed_go (λ x, String.app x suffix) H.

Section test.
Context `{PROP : bi}.
Lemma test (P Q : PROP) :
  P -∗ P -∗ P -∗ P -∗ Q ∗ Q.
Proof.
  iIntros "H1 H2 P1 P2".
  (* NOTE: have not found a way to layer "glob" on top of exising Iris tactics.
     E.g. the `Tactic Notation` for `iSplitL` expects its argument to be a `constr`.
     When that constr is built up by embedding ltac2 as `ltac2:(glob_ipm
     whatever)`, that ltac2 actually gets run in a new proofview/goal just for
     constructing the constr. So, the goal is `?T` (to construct some constr,
     whose type is not even known).
     However, `glob_ipm` must be run against the actual IPM goal so it can see
     the named hypotheses.

     This implies that there's no way to use ltac to expand a glob in the constr
     arguments to existing Iris tactics.

     One solution: do glob expansion in something at the level of `envs_split_go`.
     Another possible solution: if tactics (like iSplitL) took e.g. ltac2
     strings as input, then computing the string ought to be run in the current
     proofview; the proofview changes when there are quotations/antiquotations.
   *)
  iCombineNamed "H*" as "Hout".
  iNamedPrefix "Hout" "wg_".
  iCombineNamed "wg_*" as "Hout".
  iNamedSuffix "Hout" "_wg".
Abort.

End test.
