From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export
     lang notation array typing struct
     tactics lifting proofmode.
From Perennial.goose_lang Require Import slice.
Import uPred.

Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Definition ArbitraryIntUpto: val :=
  λ: "bound",
  let: "z" := ArbitraryInt in
  if: Var "z" < Var "bound" then Var "z" else Var "bound".

Lemma wp_ArbitraryIntUpto stk E (max: u64) :
  {{{ True }}}
    ArbitraryIntUpto #max @ stk; E
  {{{ (x:u64), RET #x; ⌜int.val x <= int.val max⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  wp_pures.
  wp_if_destruct.
  - iApply "HΦ".
    iPureIntro.
    word.
  - iApply "HΦ".
    iPureIntro.
    word.
Qed.

End heap.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc].
     If that fails, it tries to use the lemma [tac_wp_allocN] for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [val_ty
        |iSolveTC
        |finish ()]
    in process_single ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".
