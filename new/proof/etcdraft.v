From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.raftpb.
From New.proof Require Import grove_prelude.

Section proof.
Context `{!heapGS Σ}.

(* FIXME: move to builtin *)
Instance wp_int_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Instance wp_int_lt (l r : w64) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. Admitted.

(* TODO: automatically generate these instances? *)
Instance countable_connem : Countable connem.t.
Admitted.

(*
Lemma test :
  ∀ nw_ptr nw, True -∗
        nw_ptr ↦ nw ∗
        nw.(network.ignorem) ↦$ (∅ : gmap w32 bool)
. *)

Lemma wp_newNetworkWithConfigInit (peers : list interface.t) peers_sl :
  {{{
        peers_sl ↦* peers
  }}}
    newNetworkWithConfigInit #func.nil #peers_sl
  {{{
        (peersMap : gmap w64 interface.t) nw_ptr (nw : network.t), RET #nw_ptr;
        nw_ptr ↦ nw ∗
        nw.(network.peers) ↦$□ peersMap ∗
        nw.(network.dropm64) ↦$ (∅ : gmap connem.t w64) ∗
        nw.(network.ignorem) ↦$ (∅ : gmap w32 bool) ∗
        ⌜ ∀ (i : nat) peer, peers !! i = Some peer →
           if decide (peer = interface.nil) then
             ∃ raftPeer mset, peersMap !! (W64 i) = Some (interface.mk raftPeer mset)
           else
             peersMap !! (W64 i) = Some peer ⌝
        (* FIXME: Coq takes essentially forever if either the `i : nat`
           annotation is removed or if the explicit `W64 i` is removed. *)
  }}}.
Proof.
Admitted.

Lemma wp_entsWithConfig terms_sl (terms : list u64) :
  {{{
        terms_sl ↦* terms
  }}}
    entsWithConfig #func.nil #terms_sl
  {{{ (r : loc), RET #r; True }}}
.
Proof.
Admitted.

(*
Lemma wp_irrelevant e e' Φ Ψ :
  WP e {{ _, Ψ }} -∗
  (Ψ -∗ WP e' {{ Φ }}) -∗
  WP e ;;; e' {{ Φ }}.
Proof.
  iIntros "HΨ HΦ".
Qed. *)

(*
Lemma wp_network__send nw msgs_sl dq (n : network.t) (msgs : list Message.t) :
  {{{
        "Hmsg" ∷ msgs_sl ↦*{dq} msgs ∗
        "Hnw" ∷ nw ↦ n ∗
        "Hn_peers" ∷ (∃ (peersMap : gmap w64 interface.t), n.(network.peers) ↦$□ peersMap) ∗
        "Hpeer" ∷ ∃ peer msg, peersMap !! msg.(Message.To) = Some peer ∧
                              peer.(interface.mset)
  }}}
    network__send #nw #msgs_sl
  {{{ RET #(); True }}}
.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_call.
  wp_alloc nw_ptr as "?".
  wp_pures.
  wp_alloc msgs_ptr as "?".
  wp_pures.
  wp_for.
  wp_pures.
  wp_load.
  wp_pures.
  case_bool_decide as Hlt.
  - rewrite decide_True //. (* Case: more messages to send *)
    wp_pures.
    rewrite -!default_val_eq_zero_val.
    wp_alloc m as "Hm".
    wp_pures.
    iDestruct (own_slice_len with "Hmsg") as %Hsz.
    destruct msgs as [|msg msgs].
    { exfalso. simpl in *. rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt. word. }
    iDestruct (own_slice_elem_acc 0 with "Hmsg") as "[Helem Hmsg]".
    { done. }
    ltac2:(wp_load ()).
    wp_pure.
    {
      (* FIXME(word): handle sint.Z *)
      rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt.
      word.
    }
    wp_load.
    wp_pures.
    iDestruct ("Hmsg" with "[$]") as "Hmsg".
    rewrite list_insert_id; last done.
    wp_store.
    wp_pures.
    wp_alloc p as "?".
    wp_pures.
    wp_load.
    wp_load.
    wp_pures.
    wp_load.
    iDestruct "Hn_peers" as (?) "Hn_peers".
    wp_apply (wp_map_get with "[$]").
    iIntros "_".
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_pures.

    wp_load.
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #()%V ⌝ ∗ _)%I with "[-]").
    {
      case_bool_decide.
      - wp_pures. iSplitR; first done. iNamedAccu.
      - wp_pures. wp_load.
        wp_pures. (* FIXME: wp_DescribeMessage. *)
        admit.
    }
    iIntros (vunused) "[% H]". subst. iNamed "H".
    wp_pures.
    wp_bind (App (Val _) _).
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    destruct (peersMap !! msg.(Message.To)) as [peer|] eqn:Hpeer; rewrite Hpeer.
    2:{ admit. } (* FIXME: require that Message.To ∈ peersMap *)
    wp_pures.
    (* FIXME: deal with stateMachine interface [Step] function *)
    admit.
  - rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    wp_pures. by iApply "HΦ".
Admitted. *)

Ltac wp_steps :=
  wp_pures; try ((wp_load; wp_steps) || (wp_store; wp_steps)).

Axiom falso : False.

Lemma wp_test :
    (base.negb (bool_decide (sint.Z (W64 0) < sint.Z (W64 3%nat))%Z)) = false.
Proof. vm_compute. done.
Qed.

About wp'.
Check @goose_irisGS.

Axiom s: ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_sem : ffi_semantics ext ffi) (ffi_interp0 :
             ffi_interp ffi)
           (Σ : gFunctors), gooseGlobalGS Σ → irisGS goose_lang Σ. (* := @goose_irisGS. *)
Opaque s.
Print goose_irisGS.

Program Definition g :=
λ (ext : ffi_syntax) (ffi : ffi_model) (ffi_sem : ffi_semantics ext ffi) (ffi_interp0 : ffi_interp ffi)
  (Σ : gFunctors) (G : gooseGlobalGS Σ),
  {|
    iris_invGS := G.(goose_invGS);
    global_state_interp :=
      λ (g : goose_lang.(language.global_state)) (ns : nat) (mj : fracR) (D : coPset)
        (κs : list goose_lang.(language.observation)),
        (ffi_interp0.(ffi_global_ctx) G.(goose_ffiGlobalGS) g.(global_world));
    fork_post := λ _ : goose_lang.(language.val), True%I;
    num_laters_per_step := λ n : nat, (3 ^ (n + 1))%nat;
    step_count_next := λ n : nat, (10 * (n + 1))%nat;
  |}
.
Next Obligation. Admitted.
Final Obligation. Admitted.

(* Derived from bisecting down to [grove_interp.(ffi_global_ctx)]. *)
(* FIXME: seal up [grove_interp]. *)
Definition x_def : Prop := (2 ^ 64 = 2 ^ 64)%nat.
Program Definition x := unseal (_:seal (@x_def)). Obligation 1. by eexists. Qed.
Definition x_unseal : x = _ := seal_eq _.
Lemma test :
  Nat.add O O = Nat.add O O →
  x = x.
Proof using Type*.
  vm_compute Nat.add.
  done.
  Show Proof.
Time Qed.


((fun _ : @eq bool true true =>
  @eq_refl
    (forall (Σ : gFunctors) (_ : @gooseGlobalGS grove_op grove_model grove_interp Σ),
     irisGS (@goose_lang grove_op grove_model grove_semantics) Σ)
    (s grove_op grove_model grove_semantics grove_interp))
 <:
 forall _ : @eq bool (@bool_decide True True_dec) (@bool_decide True True_dec),
 @eq
   (forall (Σ : gFunctors) (_ : @gooseGlobalGS grove_op grove_model grove_interp Σ),
    irisGS (@goose_lang grove_op grove_model grove_semantics) Σ)
   (s grove_op grove_model grove_semantics grove_interp)
   (s grove_op grove_model grove_semantics grove_interp))


Proof.
  vm_compute bool_decide.
  intros. reflexivity.
  Validate Proof.
  Set Printing All.
  Show Proof.
Admitted.

Check ((fun _ : @eq bool true true => O))
  @eq_refl
    (forall (Σ : gFunctors) (_ : @gooseGlobalGS grove_op grove_model grove_interp Σ),
     irisGS (@goose_lang grove_op grove_model grove_semantics) Σ)
    (@goose_irisGS grove_op grove_model grove_semantics grove_interp))
 :
 forall _ : @eq bool (@bool_decide True True_dec) (@bool_decide True True_dec),
 @eq
   (forall (Σ : gFunctors) (_ : @gooseGlobalGS grove_op grove_model grove_interp Σ),
    irisGS (@goose_lang grove_op grove_model grove_semantics) Σ)
   (@goose_irisGS grove_op grove_model grove_semantics grove_interp)
   (@goose_irisGS grove_op grove_model grove_semantics grove_interp))
.

Time Qed.

Lemma test2 :
  wp = wp.
Proof. vm_compute bool_decide. refine eq_refl. Show Proof. Qed.

Check (eq_refl wp <: eq wp wp).

Check ((let f : False := falso in
  match
    f
    return
      (forall _ : @eq bool true true,
       @eq
         (forall (_ : stuckness) (_ : coPset)
            (_ : language.expr (@goose_lang grove_op grove_model grove_semantics))
            (_ : forall _ : language.val (@goose_lang grove_op grove_model grove_semantics), uPred (iResUR Σ)),
          uPred (iResUR Σ))
         (@wp (uPred (iResUR Σ)) (language.expr (@goose_lang grove_op grove_model grove_semantics))
            (language.val (@goose_lang grove_op grove_model grove_semantics)) stuckness
            (@wp' (@goose_lang grove_op grove_model grove_semantics) Σ
               (@goose_irisGS grove_op grove_model grove_semantics grove_interp Σ
                  (@goose_globalGS _ _ _ _ heapGS0))
               (@goose_generationGS grove_op grove_model grove_semantics grove_interp Σ
                  (@goose_localGS _ _ _ _ heapGS0))))
         (@wp (uPred (iResUR Σ)) (language.expr (@goose_lang grove_op grove_model grove_semantics))
            (language.val (@goose_lang grove_op grove_model grove_semantics)) stuckness
            (@wp' (@goose_lang grove_op grove_model grove_semantics) Σ
               (@goose_irisGS grove_op grove_model grove_semantics grove_interp Σ
                  (@goose_globalGS _ _ _ _ heapGS0))
               (@goose_generationGS grove_op grove_model grove_semantics grove_interp Σ
                  (@goose_localGS _ _ _ _ heapGS0)))))
  with
  end)
 :>
 forall _ : @eq bool (@bool_decide True True_dec) true,
 @eq
   (forall (_ : stuckness) (_ : coPset) (_ : language.expr (@goose_lang grove_op grove_model grove_semantics))
      (_ : forall _ : language.val (@goose_lang grove_op grove_model grove_semantics), uPred (iResUR Σ)),
    uPred (iResUR Σ))
   (@wp (uPred (iResUR Σ)) (language.expr (@goose_lang grove_op grove_model grove_semantics))
      (language.val (@goose_lang grove_op grove_model grove_semantics)) stuckness
      (@wp' (@goose_lang grove_op grove_model grove_semantics) Σ
         (@goose_irisGS grove_op grove_model grove_semantics grove_interp Σ (@goose_globalGS _ _ _ _ heapGS0))
         (@goose_generationGS grove_op grove_model grove_semantics grove_interp Σ
            (@goose_localGS _ _ _ _ heapGS0))))
   (@wp (uPred (iResUR Σ)) (language.expr (@goose_lang grove_op grove_model grove_semantics))
      (language.val (@goose_lang grove_op grove_model grove_semantics)) stuckness
      (@wp' (@goose_lang grove_op grove_model grove_semantics) Σ
         (@goose_irisGS grove_op grove_model grove_semantics grove_interp Σ (@goose_globalGS _ _ _ _ heapGS0))
         (@goose_generationGS grove_op grove_model grove_semantics grove_interp Σ
            (@goose_localGS _ _ _ _ heapGS0))))).

Check
(let f : False := falso in
  match
    f
    return
      (true = true
       → ⊢ ∀ (s : stuckness) (E : coPset) (e : expr) (Φ : val → iPropI Σ), WP e @ s; E {{ v, Φ v }})
  with
  end).

Check ((let f : False := falso in
  match
    f
    return
      (true = true
       → ⊢ ∀ (s : stuckness) (E : coPset) (e : goose_lang.(language.expr)) (Φ : goose_lang.(language.val)
                                                                                →
                                                                                iPropI Σ),
             WP e @ s; E {{ v, Φ v }})
  with
  end) : true = true
       → ⊢ ∀ (s : stuckness) (E : coPset) (e : expr) (Φ : val → iPropI Σ), WP e @ s; E {{ v, Φ v }}
      ).

Lemma wp_testLeaderElection2_symbolic_execute :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  Ltac wp_progress := (first [progress (rewrite -!default_val_eq_zero_val)|
                               progress wp_pures |
                               wp_load |
                               wp_store |
                               let x := fresh "ptr" in wp_alloc x as "?" |
                               (unshelve wp_apply wp_slice_literal; first apply _; iIntros (?) "Hsl") |
                               (unshelve wp_apply wp_slice_make2; [| | apply _ | ];
                                iIntros (?) "[Hsl ?]") |
                               (let Hlen:=fresh "Hlen" in
                                iDestruct (own_slice_len with "Hsl") as %Hlen; iDestruct "Hsl" as "?";
                                apply (f_equal (λ x, W64 (Z.of_nat x))) in Hlen;
                                rewrite w64_to_nat_id in Hlen; simpl in Hlen;
                                let x := fresh in rename Hlen into x) |
                               wp_pure; [word|] |
                               rewrite do_for_unseal |

                               (* for storing to a slice.elem_ref_f *)
                               wp_bind (store_ty _ _ _);
                               unshelve (eapply (tac_wp_store_ty []);
                                         [ eapply points_to_access_slice_elem_ref; shelve |
                                           iAssumptionCore |
                                           reduction.pm_reflexivity |
                                           simpl fill
                                 ]); try tc_solve |

                               (* for loading from a slice.elem_ref_f *)
                               wp_bind (load_ty _ _);
                               unshelve (eapply (tac_wp_load_ty []);
                                         [ eapply points_to_access_slice_elem_ref; shelve |
                                           iAssumptionCore |
                                           simpl fill
                                 ]); try tc_solve |

                               (* for making progress inside body of for loop control-flow handler *)
                               rewrite [in (Fst (execute_val _))]execute_val_unseal |
                               unshelve (wp_apply wp_map_make; [done| iIntros (?) "?"]); try tc_solve |
                               wp_call
                      ]).
  Time repeat wp_progress.
  rewrite -H in H0 |- *.
  rewrite length_replicate w64_to_nat_id in H0.
  Disable Notation "?=" (all).
  Set Printing Depth 100000.
  Set Printing All.
  vm_compute (bool_decide _).
  all: destruct falso.
Time Qed.

  2:{ vm_compute bool_decide. done. }
  vm_compute bool_decide.
  all: destruct falso.
Time Qed.
  -
  wp_bind (bool_decide.
  vm_compute bool_decide.
  all: destruct falso.
  Time Validate Proof.
  Time Guarded.
Time Qed.
  Check Proof.
  (* do 68 wp_progress. *)
(*
   61 -> 2.159
   62 -> 2.258
   68 -> 2.398
 *)

  Time repeat wp_progress.
  rewrite -H in H0 |- *.
  rewrite length_replicate w64_to_nat_id in H0.
  vm_compute bool_decide.
  all: destruct falso.
Time Qed.
  (* do 10 wp_progress. *)
  all: destruct falso.
Time Qed.

  iDestruct select (sl ↦* _) as "Hsl".
  (* FIXME: want to match syntax of expr first, then solve goal. *)
  wp_apply (wp_slice_for_range with "[$Hsl]").
  simpl.
  Time repeat wp_progress.
  wp_pure.
  (* FIXME: need to make interfaceT comparable *)
  Show Ltac Profile.
  all: destruct falso.
Time Qed.

Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  wp_call.
  wp_alloc preVote as "?".
  wp_pures.
  wp_alloc t_ptr as "?".
  wp_steps.
  rewrite -!default_val_eq_zero_val.
  wp_alloc cfg as "Hcfg".
  wp_pures.
  wp_alloc candState as "HcandState".
  wp_steps.
  wp_alloc candTerm as "HcandTerm".
  wp_pures.
  wp_store.
  wp_pures.

  wp_steps.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  wp_steps.
  wp_alloc tests as "Htests".
  wp_steps.

  (* FIXME: find a way to avoid shelved typeclass goal. Not sure why [_] is
     needed to avoid the shelved goal. *)
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".

  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw1".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw2".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  (* Time wp_apply (wp_newNetworkWithConfigInit with "[$]"). *)
  Time wp_bind (newNetworkWithConfigInit _ _); iApply (wp_newNetworkWithConfigInit with "[$]"); iModIntro.
  iIntros "* Hnw3".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw4".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw5".

  wp_steps.

  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_pures.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw6".
  wp_pures.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "Hsl".
  wp_steps.

  wp_apply wp_slice_for_range.
Admitted.
(*
  iFrame "Hsl".
  simpl foldr.
  (* Entire for loop is unfolded here. TODO: is there a way to unfold one iteration at a time? *)
  wp_pures.
  wp_alloc i as "?".
  wp_pures.
  wp_alloc tt as "Htt".
  wp_pures.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "Hsl".

  wp_pures.
  wp_load.
  Show Ltac Profile.
Admitted.
*)

End proof.
