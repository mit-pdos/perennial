From New.proof Require Import grove_prelude.

Section proof.
Context `{!heapGS Σ}.

Definition test (l : loc) : expr :=
  do: #l <-[uint64T] #0 ;;;
  do: #l <-[uint64T] #1 ;;;
  do: #l <-[uint64T] #2 ;;;
  do: #l <-[uint64T] #3 ;;;
  do: #l <-[uint64T] #4 ;;;
  do: #l <-[uint64T] #5 ;;;
  do: #l <-[uint64T] #6 ;;;
  do: #l <-[uint64T] #7 ;;;
  do: #l <-[uint64T] #8 ;;;
  do: #l <-[uint64T] #9
.

Axiom own_something : iProp Σ.

Definition big_context l : iProp Σ :=
  "Hown" ∷ l ↦[uint64T] #0 ∗
  "H0" ∷ own_something ∗
  "H1" ∷ own_something ∗
  "H2" ∷ own_something ∗
  "H3" ∷ own_something ∗
  "H4" ∷ own_something ∗
  "H5" ∷ own_something ∗
  "H6" ∷ own_something ∗
  "H7" ∷ own_something ∗
  "H8" ∷ own_something ∗
  "H9" ∷ own_something
.

Lemma x (l : loc) :
  {{{ big_context l }}}
    (test l)
  {{{ RET execute_val; True }}}.
Proof.
  iIntros (?) "H HΦ".
  unfold test.
  iNamed "H".
  time (do 10 wp_store).
  wp_pures.
  by iApply "HΦ".
Time Qed.
(* Finished transaction in 2.695 secs (2.356u,0.s) (successful) *)


Lemma tac_wp_store_ty_bad K Δ Δ''
                          Δ1 Δ2 Δ3 Δ4 Δ5 Δ6 Δ7 Δ8 Δ9 Δ10
                          Δ11 Δ12 Δ13 Δ14 Δ15 Δ16 Δ17 Δ18 Δ19 Δ20
                          Δ21 Δ22 Δ23 Δ24 Δ25 Δ26 Δ27
  stk E i l t v v' Φ :
  (Δ = Δ1 ∧
   Δ = Δ2 ∧
   Δ = Δ3 ∧
   Δ = Δ4 ∧
   Δ = Δ5 ∧
   Δ = Δ6 ∧
   Δ = Δ7 ∧
   Δ = Δ8 ∧
   Δ = Δ9 ∧
   Δ = Δ10 ∧
   Δ = Δ11 ∧
   Δ = Δ12 ∧
   Δ = Δ13 ∧
   Δ = Δ14 ∧
   Δ = Δ15 ∧
   Δ = Δ16 ∧
   Δ = Δ17 ∧
   Δ = Δ18 ∧
   Δ = Δ19 ∧
   Δ = Δ20 ∧
   Δ = Δ21 ∧
   Δ = Δ22 ∧
   Δ = Δ23 ∧
   Δ = Δ24 ∧
   Δ = Δ25 ∧
   Δ = Δ26 ∧
   Δ = Δ27
  ) →
  has_go_type v' t ->
  envs_lookup i Δ = Some (false, l ↦[t] v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
  envs_entails Δ (WP fill K (store_ty t (PairV (LitV l) v')) @ stk; E {{ Φ }}).
Proof.
Admitted.

Tactic Notation "wp_store_bad" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_] _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store_ty_bad K))
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [done
    |(repeat econstructor || fail "could not establish [has_go_type]") (* solve [has_go_type v' t] *)
    |solve_pointsto ()
    |reduction.pm_reflexivity
    |first [wp_pure_filter (Rec BAnon BAnon _)|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Lemma x_bad (l : loc) :
  {{{ big_context l }}}
    (test l)
  {{{ RET execute_val; True }}}.
Proof.
  iIntros (?) "H HΦ".
  unfold test.
  iNamed "H".
  wp_pures.
  time (do 10 wp_store_bad).
  wp_pures.
  by iApply "HΦ".
  Optimize Proof.
  Optimize Heap.
Time Qed.

(* with 9 Δs: Finished transaction in 1.342 secs (1.336u,0.s) (successful) *)
(* with 27 Δs: Finished transaction in 5.794 secs (5.785u,0.003s) (successful) *)
Print x_bad.

End proof.
