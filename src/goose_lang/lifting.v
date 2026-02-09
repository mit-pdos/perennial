From stdpp Require Import fin_maps.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import lib.frac_auth auth numbers gmap excl dfrac_agree.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From Perennial.iris_lib Require Import dfractional.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import ectx_lifting.
From Perennial.Helpers Require Import Transitions.
From Perennial.Helpers Require Export NamedProps.
From Perennial.base_logic Require Export proph_map frac_coPset.
From Perennial.algebra Require Export na_heap.
From Perennial.goose_lang Require Export lang.
From Perennial Require Import base.
Set Default Proof Using "Type".

Notation nonAtomic T := (naMode * T)%type.

Section definitions.
  Context `{ext:ffi_syntax}.
  Context `{hG: na_heapGS loc val Σ}.
  Definition heap_pointsto_def l q v : iProp Σ :=
    ⌜l ≠ null⌝ ∗ na_heap_pointsto (L:=loc) (V:=val) l q v.
  Definition heap_pointsto_aux : seal (@heap_pointsto_def). by eexists. Qed.
  Definition heap_pointsto := unseal heap_pointsto_aux.
  Definition heap_pointsto_eq : @heap_pointsto = @heap_pointsto_def :=
    seal_eq heap_pointsto_aux.

  Global Instance heap_pointsto_persistent l v : Persistent (heap_pointsto l DfracDiscarded v).
  Proof. rewrite heap_pointsto_eq. apply _. Qed.

  Lemma heap_pointsto_persist l dq v:
    heap_pointsto l dq v ==∗ heap_pointsto l DfracDiscarded v.
  Proof.
    rewrite heap_pointsto_eq.
    iIntros "[%Ha Hb]".
    iMod (na_heap_pointsto_persist with "Hb") as "Hb".
    iModIntro.
    iFrame. done.
  Qed.

  Global Instance heap_pointsto_dfractional l v: DFractional (λ dq, heap_pointsto l dq v).
  Proof.
    split; intros.
    - rewrite heap_pointsto_eq /heap_pointsto_def.
      rewrite (dfractional (DFractional:=na_heap_pointsto_dfractional _ _)).
      iSplit.
      + by iIntros "(%&$&$)".
      + by iIntros "[[% $] [% $]]".
    - apply _.
    - iIntros "H". iMod (heap_pointsto_persist with "H") as "$". done.
  Qed.
  Global Instance heap_pointsto_as_dfractional l dq v: AsDFractional (heap_pointsto l dq v) (λ dq, heap_pointsto l dq v) dq.
  Proof. auto. Qed.

  Global Instance heap_pointsto_fractional l v: Fractional (λ q, heap_pointsto l (DfracOwn q) v)%I.
  Proof.
    apply (fractional_of_dfractional (λ dq, heap_pointsto l dq v)).
  Qed.
  Global Instance heap_pointsto_as_fractional l q v:
    AsFractional (heap_pointsto l (DfracOwn q) v) (λ q, heap_pointsto l (DfracOwn q) v)%I q.
  Proof. constructor; [ done | apply _ ]. Qed.
  Global Instance heap_pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (heap_pointsto l dq1 v1)%I (heap_pointsto l dq2 v2)%I ⌜ ✓(dq1 ⋅ dq2) ∧ v1 = v2 ⌝%I.
  Proof. rewrite heap_pointsto_eq /CombineSepGives. iIntros "[[?H1] [?H2]]".
         iCombine "H1 H2" gives %?. iModIntro. iPureIntro. done. Qed.

  Lemma heap_pointsto_agree l q1 q2 v1 v2 : heap_pointsto l q1 v1 ∗ heap_pointsto l q2 v2 -∗ ⌜v1 = v2⌝.
  Proof. iIntros "[H1 H2]". iCombine "H1 H2" gives %[? ?]. done. Qed.

  Theorem na_pointsto_to_heap l q v :
    l ≠ null ->
    na_heap_pointsto l q v -∗ heap_pointsto l q v.
  Proof.
    rewrite heap_pointsto_eq /heap_pointsto_def.
    iIntros (?) "$ //".
  Qed.

  Theorem heap_pointsto_na_acc l q v :
    heap_pointsto l q v -∗
    na_heap_pointsto l q v ∗ (∀ v', na_heap_pointsto l q v' -∗ heap_pointsto l q v').
  Proof.
    rewrite heap_pointsto_eq /heap_pointsto_def.
    iIntros "[% $]".
    iIntros (v') "Hl".
    by iFrame.
  Qed.

  Theorem heap_pointsto_valid l dq v:
     heap_pointsto l dq v -∗ ⌜✓dq⌝.
  Proof.
    iIntros "H".
    iDestruct (heap_pointsto_na_acc with "H") as "(Hna&_)".
    iDestruct (na_heap_pointsto_valid with "Hna") as %Hvalid.
    done.
  Qed.

  Theorem heap_pointsto_frac_valid l q v:
     heap_pointsto l (DfracOwn q) v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    iIntros "H".
    iDestruct (heap_pointsto_na_acc with "H") as "(Hna&_)".
    iApply (na_heap_pointsto_frac_valid with "Hna").
  Qed.

  Global Instance heap_pointsto_timeless l q v : Timeless (heap_pointsto l q v).
  Proof. rewrite heap_pointsto_eq. apply _. Qed.

  Theorem heap_pointsto_non_null l q v : heap_pointsto l q v -∗ ⌜l ≠ null⌝.
  Proof.
    rewrite heap_pointsto_eq /heap_pointsto_def.
    iIntros "[% _] //".
  Qed.

End definitions.

(** Override the notations so that scopes and coercions work out *)
Local Notation "l ↦ dq v" := (heap_pointsto l dq v%V)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Local Notation "l ↦ dq -" := (∃ v, l ↦{dq} v)%I
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  -") : bi_scope.


Section go_state_definitions.
Context `{ext:ffi_syntax}.

Class go_stateGS Σ : Set := GoStateGS {
  #[global] package_inited_inG :: ghost_varG Σ (gmap go_string bool);
  package_inited_name : gname ;
}.

Class go_state_preG (Σ: gFunctors) : Set := {
  #[global] package_inited_preG_inG :: ghost_varG Σ (gmap go_string bool);
}.

Definition go_stateΣ : gFunctors :=
  #[ghost_varΣ (gmap go_string bool)].

Global Instance subG_globalsG {Σ} : subG go_stateΣ Σ → go_state_preG Σ.
Proof. solve_inG. Qed.

Definition go_stateGS_update_pre (Σ: gFunctors) (hT: go_state_preG Σ)
  (new_packageInited_name: gname) :=
  {| package_inited_inG := package_inited_preG_inG; package_inited_name := new_packageInited_name |}.

Definition go_stateGS_update (Σ: gFunctors) (hT: go_stateGS Σ) (new_package_inited_name: gname) :=
  {| package_inited_inG := package_inited_inG; package_inited_name := new_package_inited_name |}.

Definition own_go_state_ctx `{hG : go_stateGS Σ} (package_inited : gmap go_string bool) :=
  ghost_var package_inited_name (1/2) package_inited.

Definition own_go_state_def `{hG : go_stateGS Σ} (package_inited : gmap go_string bool) :=
  ghost_var package_inited_name (1/2) package_inited.
Program Definition own_go_state := sealed @own_go_state_def.
Definition own_go_state_unseal : own_go_state = _ := seal_eq _.
Global Arguments own_go_state {Σ hG}.

Global Instance own_go_state_ctx_combine_sep_gives v1 v2 `{hG : go_stateGS Σ} :
  CombineSepGives (own_go_state_ctx v1)%I (own_go_state v2)%I ⌜ v1 = v2 ⌝%I.
Proof.
  rewrite own_go_state_unseal /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H2 H1" gives %?. iModIntro. iPureIntro. naive_solver.
Qed.

Global Instance own_go_state_timeless v `{hG : go_stateGS Σ} : Timeless (own_go_state v).
Proof. rewrite own_go_state_unseal. apply _. Qed.

Lemma own_go_state_update `{hG: go_stateGS Σ} v v' v'' :
  own_go_state v -∗ own_go_state_ctx v' ==∗
  own_go_state v'' ∗ own_go_state_ctx v''.
Proof.
  iIntros "H1 H2".
  iCombine "H2 H1" gives %H. subst.
  rewrite own_go_state_unseal.
  iDestruct (ghost_var_update_2 with "[$] [$]") as "$".
  compute_done.
Qed.

Lemma go_state_init `(hT: go_state_preG Σ) package_inited :
  ⊢ |==> ∃ new_package_inited_name : gname,
    let _ := go_stateGS_update_pre Σ hT new_package_inited_name in
    own_go_state_ctx package_inited ∗ own_go_state package_inited.
Proof.
  iMod (ghost_var_alloc package_inited) as "[% [? ?]]".
  rewrite own_go_state_unseal. by iFrame.
Qed.

Lemma go_state_reinit `(hT: go_stateGS Σ) package_inited :
  ⊢ |==> ∃ new_globals_name : gname, let _ := go_stateGS_update Σ hT new_globals_name in
     own_go_state_ctx package_inited ∗ own_go_state package_inited.
Proof.
  iMod (ghost_var_alloc package_inited) as "[% [? ?]]".
  rewrite own_go_state_unseal. by iFrame.
Qed.

End go_state_definitions.

(* An FFI layer will use certain CMRAs for its primitive rules.
   Besides needing to know that these CMRAs are included in Σ, there may
   be some implicit ghost names that are used to identify instances
   of these algebras. (For example, na_heap has an implicit name used for
   the ghost heap). These are bundled together in ffiLocalGS and ffiGlobalGS.

   On a crash, a new "generation" might use fresh names for these instances.
   Thus, an FFI needs to tell the framework how to unbundle ffiLocalGS and swap in a
   new set of names.
*)

Class ffi_interp (ffi: ffi_model) :=
  { ffiLocalGS: gFunctors -> Set;
    ffiGlobalGS: gFunctors -> Set;
    ffi_global_ctx: ∀ `{ffiGlobalGS Σ}, ffi_global_state -> iProp Σ;
    ffi_local_ctx: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;
    ffi_global_start: ∀ `{ffiGlobalGS Σ}, ffi_global_state -> iProp Σ;
    ffi_local_start: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;
    (* ffi_restart is provided to the client in idempotence_wpr *)
    ffi_restart: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;
    ffi_crash_rel: ∀ Σ, ffiLocalGS Σ → ffi_state → ffiLocalGS Σ → ffi_state → iProp Σ;
  }.

Arguments ffi_local_ctx {ffi FfiInterp Σ} : rename.
Arguments ffi_global_ctx {ffi FfiInterp Σ} : rename.
Arguments ffi_local_start {ffi FfiInterp Σ} : rename.
Arguments ffi_global_start {ffi FfiInterp Σ} : rename.
Arguments ffi_restart {ffi FfiInterp Σ} : rename.

Section goose_lang.
Context `{ffi_sem: ffi_semantics} {go_gctx : GoGlobalContext}.
Context `{!ffi_interp ffi}.

Record cr_names : Set := {
  credit_name : gname;
  coPset_name : gname;
}.

Class credit_preG (Σ: gFunctors) : Set := {
  #[global] credit_preG_inG :: inG Σ (authR natUR);
  #[global] frac_coPset_preG_inG :: inG Σ (frac_coPsetR);
}.

Class creditGS (Σ: gFunctors) : Set := {
  #[global] credit_inG :: inG Σ (authR natUR);
  #[global] frac_coPset_inG :: inG Σ (frac_coPsetR);
  credit_cr_names : cr_names;
}.

Definition creditGS_update (Σ: gFunctors) (hC: creditGS Σ) (names: cr_names) :=
  {| credit_inG := credit_inG; frac_coPset_inG := frac_coPset_inG; credit_cr_names := names |}.

Definition creditGS_update_pre (Σ: gFunctors) (hT: credit_preG Σ) (names: cr_names) :=
  {| credit_inG := credit_preG_inG; frac_coPset_inG := frac_coPset_preG_inG; credit_cr_names := names |}.

Definition creditΣ : gFunctors :=
  #[GFunctor (authR natUR);
      GFunctor frac_coPsetR].

Global Instance subG_creditG {Σ} : subG creditΣ Σ → credit_preG Σ.
Proof. solve_inG. Qed.

Section creditGS_defs.
Context `{creditGS Σ}.

Definition cred_frag (n : nat) : iProp Σ := (own (credit_name (credit_cr_names)) (◯ n)).

Definition cred_auth (ns : nat) : iProp Σ :=
  (own (credit_name (credit_cr_names)) (● ns)).

Definition pinv_tok_inf q E := ownfCP_inf (coPset_name (credit_cr_names)) q E.
Definition pinv_tok q E := ownfCP (coPset_name (credit_cr_names)) q E.

Lemma cred_auth_frag_incr (ns n: nat) :
  cred_auth ns ∗ cred_frag n ==∗
  cred_auth (S ns) ∗ cred_frag (S n).
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ (S ns) (S n)); lia. }
  iFrame. eauto.
Qed.

Lemma cred_auth_frag_incr_k (ns n k: nat) :
  cred_auth ns ∗ cred_frag n ==∗
  cred_auth (ns + k) ∗ cred_frag (n + k).
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ (ns + k) (n + k)); lia. }
  iFrame. eauto.
Qed.

Lemma cred_auth_frag_decr (ns n: nat) :
  cred_auth ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_auth ns' ∗ cred_frag n.
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iDestruct (own_valid_2 with "Hγ Hγf") as % Hval.
  apply auth_both_valid_discrete in Hval as (Hincl%nat_included&_).
  destruct ns as [| ns']; first lia.
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ ns' n); lia. }
  iExists _. iFrame. iModIntro. eauto.
Qed.

Lemma cred_auth_frag_invert (ns n: nat) :
  cred_auth ns ∗ cred_frag n -∗ ∃ ns', ⌜ (ns = n + ns')%nat ⌝.
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct (own_valid_2 with "Hγ Hγf") as % Hval.
  apply auth_both_valid_discrete in Hval as (Hincl%nat_included&_).
  iExists (ns - n)%nat. iFrame. iPureIntro; lia.
Qed.

Definition cred_interp ns : iProp Σ :=
  cred_auth ns ∗ cred_frag 0.

Lemma cred_frag_split ns1 ns2 :
  cred_frag (ns1 + ns2) ⊢@{_} cred_frag ns1 ∗ cred_frag ns2.
Proof.
  iIntros "H".
  rewrite /cred_frag auth_frag_op.
  iDestruct "H" as "(H1&H2)".
  iFrame.
Qed.

Lemma cred_frag_join ns1 ns2 :
  cred_frag ns1 ∗ cred_frag ns2 ⊢@{_} cred_frag (ns1 + ns2).
Proof.
  iIntros "(H1&H2)".
  iCombine "H1 H2" as "H".
  iFrame.
Qed.

Lemma cred_interp_incr ns :
  cred_interp ns ==∗ cred_interp (S ns) ∗ cred_frag 1.
Proof.
  iIntros "H".
  iMod (cred_auth_frag_incr with "H") as "(?&H)".
  iEval (replace 1%nat with (1 + 0)%nat by lia) in "H".
  iDestruct (cred_frag_split with "H") as "($&$)".
  eauto.
Qed.

Lemma cred_interp_incr_k ns k :
  cred_interp ns ==∗ cred_interp (ns + k) ∗ cred_frag k.
Proof.
  iIntros "H".
  iMod (cred_auth_frag_incr_k _ _ k with "H") as "(?&H)".
  iDestruct (cred_frag_split with "H") as "($&$)".
  eauto.
Qed.

Lemma cred_interp_decr ns n :
  cred_interp ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_interp ns' ∗ cred_frag n.
Proof.
  iIntros "((H&?)&Hfrag)".
  iMod (cred_auth_frag_decr with "[$H $Hfrag]") as (ns' Heq) "(?&H)". subst.
  iExists ns'. iModIntro. iSplit; eauto.
  iFrame.
Qed.

Lemma cred_interp_invert ns k :
  cred_interp ns ∗ cred_frag k -∗ ∃ ns', ⌜ ns = (k + ns')%nat ⌝.
Proof.
  iIntros "((H&?)&Hfrag)".
  iDestruct (cred_auth_frag_invert with "[$H $Hfrag]") as %[ns' Heq]; eauto.
Qed.

End creditGS_defs.

Lemma credit_name_init `{hC: credit_preG Σ} k :
  ⊢ |==> ∃ name : cr_names, let _ := creditGS_update_pre _ _ name in
                           cred_interp k ∗ cred_frag k ∗ pinv_tok 1 ∅.
Proof.
  iMod (own_alloc (● k ⋅ ◯ k)) as (γ) "[H1 H2]".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iMod (ownfCP_init_empty γ) as "Hemp".
  iModIntro. iExists {| credit_name := γ; coPset_name := γ |}.
  rewrite -{2}(Nat.add_0_l k).
  iDestruct (cred_frag_split with "[H2]") as "($&$)".
  { rewrite /cred_frag//=. }
  iFrame.
Qed.

(** Global ghost state for GooseLang. *)
Class gooseGlobalGS Σ := GooseGlobalGS {
  goose_invGS : invGS Σ;
  #[global] goose_prophGS :: proph_mapGS proph_id val Σ;
  #[global] goose_creditGS :: creditGS Σ;
  goose_ffiGlobalGS : ffiGlobalGS Σ;
}.
(* Per-generation / "local" ghost state.

TODO: in program_logic we use the term "generation", in GooseLang we say "local".
Would be good to align terminology. *)
Class gooseLocalGS Σ := GooseLocalGS {
  goose_crashGS : crashGS Σ;
  goose_ffiLocalGS : ffiLocalGS Σ;
  #[global] goose_go_local_context :: GoLocalContext;
  #[global] goose_na_heapGS :: na_heapGS loc val Σ;
  #[global] goose_go_stateGS :: go_stateGS Σ;
}.

(* For convenience we also have a class that bundles both the
   global and per-generation parameters.
   For historic reasons, this is called heapGS
   TODO: rename to gooseGS, or remove. *)
Local Set Primitive Projections.
Class heapGS Σ := HeapGS {
  goose_globalGS : gooseGlobalGS Σ;
  goose_localGS : gooseLocalGS Σ;
}.
Local Unset Primitive Projections.
(* Hints are set up at the bottom of the file, outside the section. *)

Definition tls (na: naMode) : lock_state :=
  match na with
  | Writing => WSt
  | Reading n => RSt n
  end.

Definition borrowN := nroot.@"borrow".
Definition crash_borrow_ginv_number : nat := 6%nat.
Definition crash_borrow_ginv `{!invGS Σ} `{creditGS Σ}
  := (inv borrowN (cred_frag crash_borrow_ginv_number)).

Global Program Instance goose_irisGS `{G: !gooseGlobalGS Σ}:
  irisGS goose_lang Σ := {
  iris_invGS := goose_invGS;
  num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  step_count_next := (λ n, 10 * (n + 1))%nat;
  global_state_interp g ns mj D κs :=
    (ffi_global_ctx goose_ffiGlobalGS g.(global_world) ∗
     proph_map_interp κs g.(used_proph_id) ∗
     @crash_borrow_ginv _ goose_invGS _ ∗
     cred_interp ns ∗
     ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗
     pinv_tok mj D
    )%I;
  fork_post _ := True%I;
}.
Next Obligation.
  iIntros (Σ ? g ns q D κs) "($&$&$&Hcred&Htok)".
  iFrame. iMod (cred_interp_incr with "Hcred") as "($&_)". eauto.
Qed.
Next Obligation. intros => //=. lia. Qed.

Global Program Instance goose_generationGS {go_gctx : GoGlobalContext} `{L: !gooseLocalGS Σ}:
  generationGS goose_lang Σ := {
  iris_crashGS := goose_crashGS;
  state_interp σ nt :=
    (
      "Hσ" ∷ na_heap_ctx tls σ.(heap) ∗
      "Hffi" ∷ ffi_local_ctx goose_ffiLocalGS σ.(world) ∗
      "Hg_auth" ∷ own_go_state_ctx σ.(go_state).(package_state) ∗
      "%Hlctx_eq" ∷ ⌜ σ.(go_state).(go_lctx) = goose_go_local_context ⌝
    )%I;
}.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
    rewrite /base_step /= in H;
    monad_inv; repeat (simpl in H; monad_inv)
  end.

Local Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (base_step _ _ _ _ _ _ _ _) => rewrite /base_step /= : core.
Local Hint Extern 1 (relation.bind _ _ _ _ _) => monad_simpl; simpl : core.
Local Hint Extern 1 (relation.runF _ _ _ _) => monad_simpl; simpl : core.
Local Hint Resolve to_of_val : core.

Theorem heap_base_atomic e :
  (forall σ κ e' σ' efs,
      relation.denote (base_trans e) σ σ' (κ, e', efs) -> is_Some (to_val e')) ->
  base_atomic StronglyAtomic e.
Proof.
  intros Hdenote.
  hnf; intros * H.
  apply Hdenote in H. auto.
Qed.

Theorem atomically_is_val Σ (tr: transition Σ val) σ σ' κ e' efs :
  relation.denote (atomically tr) σ σ' (κ, e', efs) ->
  is_Some (to_val e').
Proof.
  intros.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H; subst.
  eexists; eauto.
Qed.

Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Global Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
Proof.
  solve_atomic.
Qed.

(* PrepareWrite and FinishStore are individually atomic, but the two need to be
combined to actually write to the heap and that is not atomic. *)
Global Instance prepare_write_atomic s v : Atomic s (PrepareWrite (Val v)).
Proof. solve_atomic. Qed.
Global Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Global Instance finish_store_atomic s v1 v2 : Atomic s (FinishStore (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance start_read_atomic s v : Atomic s (StartRead (Val v)).
Proof. solve_atomic. Qed.
Global Instance finish_read_atomic s v1 : Atomic s (FinishRead (Val v1)).
Proof. solve_atomic. Qed.
Global Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. monad_inv. eauto. Qed.
(*
Global Instance ext_atomic s op v : Atomic s (ExternalOp op (Val v)).
Proof. solve_atomic. Qed.
 *)
Global Instance resolve_atomic s p w : Atomic s (ResolveProph (Val p) (Val w)).
Proof. solve_atomic. simpl in *. monad_inv. eauto. Qed.

Section lifting.
(* TODO: measure perf impact of parameterizing over heapGS
vs gooseGS+gooseLocalGS *)
Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wpc_borrow_inv s E e Φ Φc :
  (crash_borrow_ginv -∗ WPC e @ s; E {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H".
  rewrite wpc_unfold.
  iIntros (mj). rewrite /wpc_pre.
  iSplit; last first.
  { iIntros (????) "Hg HC".
    iAssert (crash_borrow_ginv) with "[Hg]" as "#Hinv".
    { iDestruct "Hg" as "(_&_&#Hinv&_)". eauto. }
    iDestruct ("H" with "[$]") as "H".
    iDestruct ("H" $! _) as "(_&H)".
    iApply ("H" with "[$]"); eauto. }
  destruct (language.to_val _).
  - iIntros (?????) "Hg HNC".
    iAssert (crash_borrow_ginv) with "[Hg]" as "#Hinv".
    { iDestruct "Hg" as "(_&_&#Hinv&_)". eauto. }
    iDestruct ("H" with "[$]") as "H".
    iDestruct ("H" $! _) as "(H&_)".
    iApply ("H" with "[$]"); eauto.
  - iIntros (????????) "Hσ Hg HNC".
    iAssert (crash_borrow_ginv) with "[Hg]" as "#Hinv".
    { iDestruct "Hg" as "(_&_&#Hinv&_)". eauto. }
    iDestruct ("H" with "[$]") as "H".
    iDestruct ("H" $! _) as "(H&_)".
    iApply ("H" with "[$] [$]"); eauto.
Qed.

Lemma wp_panic s msg E Φ :
  ▷ False -∗ WP Panic msg @ s; E {{ Φ }}.
Proof.
  iIntros ">[] HΦ".
Qed.

Lemma wp_ArbitraryInt stk E :
  {{{ True }}}
    ArbitraryInt @ stk; E
  {{{ (x:u64), RET #x; True }}}.
Proof.
  iIntros (Φ) "Htr HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 g1 ns mj D κ κs n) "(Hσ&?&?&?) Hg !>"; iSplit.
  { iPureIntro. unshelve (repeat econstructor). refine inhabitant. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step; iFrame.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. by iApply "HΦ".
Qed.

(** WP for go instructions  *)
Lemma wp_GoInstruction K op arg {stk E} Φ :
  (∀ s, ∃ e' s', is_go_step op arg e' s s') →
  ▷ (∀ e' s s', ⌜ is_go_step op arg e' s s' ⌝ →
                (£ 1 -∗ own_go_state_ctx s ={E}=∗
                 own_go_state_ctx s' ∗
                 WP fill K e' @ stk ; E {{ Φ }})) -∗
  WP fill K (GoInstruction op arg) @ stk ; E {{ Φ }}.
Proof.
  iIntros (Hok) "HΦ".
  iApply wp_lift_step; [apply fill_not_val; done|].
  iIntros (σ1 g1 ns mj D κ κs nt) "H Hg".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask".
  iNamed "H".
  assert (Hred : base_reducible (GoInstruction op arg) σ1 g1).
  { epose proof (Hok _) as Hok. destruct Hok as (e' & s' & Hok).
    repeat eexists.
    { simpl. instantiate (1:=pair _ _). rewrite Hlctx_eq //. }
    simpl. monad_simpl. }
  iSplit.
  { iPureIntro. destruct stk; try done. apply base_prim_fill_reducible. done. }
  iIntros (v2 σ2 g2 efs Hstep).
  rewrite /= in Hstep.
  inversion Hstep; subst.
  eapply base_redex_unique in H; first last.
  { by repeat eexists _. }
  { done. }
  destruct H as [<- <-]. inv_base_step. destruct pat0.
  simpl in *. monad_inv.
  iNext. iMod "Hmask" as "_".
  iIntros "Hlc". inv_base_step.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  rewrite -Hlctx_eq. iSpecialize ("HΦ" $! _ _ _ ltac:(done)).
  iDestruct "Hlc" as "[Hlc _]".
  iMod ("HΦ" with "[$] [$]") as "[Hg_auth HΦ]".
  iModIntro. iFrame "∗#%".
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ #() -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 g1 mj D ns κ κs n) "Hσ Hg !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step. iFrame.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  done.
Qed.

(** Heap *)
(** The "proper" [allocN] are derived in [array]. *)

Lemma heap_array_to_seq_pointsto l vs (P: loc → val → iProp Σ) :
  ([∗ map] l' ↦ vm ∈ heap_array l vs, P l' vm) -∗
  [∗ list] j ↦ v ∈ vs, P (l +ₗ j) v.
Proof.
  iIntros "Hvs". iInduction vs as [|vs] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite addr_plus_plus -{1}[l']addr_plus_off_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0.
  setoid_rewrite Nat2Z.inj_succ.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]".
  setoid_rewrite loc_add_comm.
  by iApply ("IH" with "[Hvs]").
Qed.

Lemma seq_pointsto_to_heap_array l vs (P: loc → val → iProp Σ) :
  ([∗ list] j ↦ v ∈ vs, P (l +ₗ j) v) -∗
  ([∗ map] l' ↦ vm ∈ heap_array l vs, P l' vm).
Proof.
  iIntros "Hvs". iInduction vs as [|vs] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite addr_plus_plus -{1}[l']addr_plus_off_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0.
  setoid_rewrite Nat2Z.inj_succ.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]".
  setoid_rewrite loc_add_comm.
  by iApply ("IH" with "[Hvs]").
Qed.

Theorem big_opL_add (M: ofe) (o: M -> M -> M) `{!monoid.Monoid o u} f start off k n :
  big_opL o (fun i x => f (k + i)%nat x) (seq (start + off) n) ≡
  big_opL o (fun i x => f (k + i)%nat (x + off)%nat) (seq start n).
Proof.
  intros.
  revert start k off.
  induction n; simpl; auto; intros.
  apply monoid_proper; first done.
  setoid_rewrite Nat.add_succ_r.
  rewrite -(IHn (S start) (S k)).
  simpl; auto.
Qed.

Theorem big_sepL_offset {b:bi} f off n :
  big_opL (@bi_sep b) (fun i x => f i x) (seq off n) ≡
  big_opL bi_sep (fun i x => f i (x + off)%nat) (seq 0%nat n).
Proof.
  apply (big_opL_add _ _ _ 0%nat _ 0%nat).
Qed.

Lemma Zmul_nat_add1_r (x k:nat) :
  (x + 1)%nat * k = k + x * k.
Proof. lia. Qed.

(* Lemma heap_seq_replicate_to_nested_pointsto l vs (n : nat) (P: loc → val → iProp Σ) : *)
(*   ([∗ list] j ↦ v ∈ concat_replicate n vs, P (l +ₗ j) v )-∗ *)
(*   [∗ list] i ∈ seq 0 n, [∗ list] j ↦ v ∈ vs, P (l +ₗ ((i : nat) * Z.of_nat (length vs)) +ₗ j)%nat v. *)
(* Proof. *)
(*   iIntros "Hvs". *)
(*   iInduction n as [|n] "IH" forall (l); simpl. *)
(*   { done. } *)
(*   rewrite concat_replicate_S. *)
(*   iDestruct (big_sepL_app with "Hvs") as "[Hvs Hconcat]". *)
(*   iSplitL "Hvs". *)
(*   - rewrite loc_add_0. *)
(*     iFrame. *)
(*   - setoid_rewrite Nat2Z.inj_add. *)
(*     setoid_rewrite <- loc_add_assoc. *)
(*     iDestruct ("IH" with "Hconcat") as "Hseq". *)
(*     rewrite (big_sepL_offset _ 1%nat). *)
(*     setoid_rewrite Zmul_nat_add1_r. *)
(*     setoid_rewrite <- loc_add_assoc. *)
(*     iExact "Hseq". *)
(* Qed. *)

(* Lemma alloc_list_loc_not_null: *)
(*   ∀ v (n : u64) σg1 l, *)
(*     isFresh σg1 l *)
(*     → ∀ l0 (x : val), *)
(*       heap_array l (concat_replicate (uint.nat n) (flatten_struct v)) !! l0 = Some x *)
(*       → l0 ≠ null. *)
(* Proof. *)
(*   intros v n σg1 l H l0 x Heq. *)
(*   apply heap_array_lookup in Heq. *)
(*   destruct Heq as [l' (?&->&Heq)]. *)
(*   apply H; eauto. *)
(* Qed. *)

(* Lemma allocN_loc_not_null: *)
(*   ∀ v (n : u64) σg1 l, *)
(*     isFresh σg1 l *)
(*     → ∀ l0 (x : val), *)
(*       heap_array l (concat_replicate (uint.nat n) (flatten_struct v)) !! l0 = Some x *)
(*       → l0 ≠ null. *)
(* Proof. *)
(*   intros v n σg1 l H l0 x Heq. *)
(*   apply heap_array_lookup in Heq. *)
(*   destruct Heq as [l' (?&->&Heq)]. *)
(*   apply H; eauto. *)
(* Qed. *)

Definition pointsto_vals l q vs : iProp Σ :=
  ([∗ list] j↦vj ∈ vs, (l +ₗ j) ↦{q} vj)%I.

Definition pointsto_vals_toks l q vs : iProp Σ :=
  ([∗ list] j↦vj ∈ vs, (l +ₗ j) ↦{q} vj ∗ meta_token (l +ₗ j) ⊤)%I.

Lemma pointsto_vals_valid l vs q (σ : gmap _ _) :
  na_heap.na_heap_ctx tls σ -∗ pointsto_vals l q vs -∗
  ⌜ (forall (i:Z), (0 <= i)%Z -> (i < length vs)%Z ->
              match σ !! (l +ₗ i) with
           | Some (Reading _, v) => vs !! Z.to_nat i = Some v
           | _ => False
              end) ⌝.
Proof.
  iIntros "Hσ Hm".
  iIntros (i Hbound1 Hbound2).
  destruct (lookup_lt_is_Some_2 vs (Z.to_nat i)) as [v Hv].
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id //. }
  rewrite /pointsto_vals. rewrite big_sepL_lookup; last exact: Hv.
  rewrite Z2Nat.id //.
  iDestruct (heap_pointsto_na_acc with "Hm") as "[Hi Hi_rest]".
  iDestruct (@na_heap.na_heap_read with "Hσ Hi") as %(lk&?&Hlookup&Hlock).
  destruct lk; inversion Hlock; subst. rewrite Hlookup //.
Qed.

Lemma wp_allocN_seq_sized_meta s E v :
  {{{ True }}} Alloc (Val v) @ s; E
  {{{ l, RET #l; ⌜ l ≠ null ∧ addr_offset l = 0%Z ⌝ ∗
                              na_block_size l 1 ∗
                              (pointsto_vals_toks l (DfracOwn 1) [v])
                              }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs k) "[Hσ ?] Hg !>"; iSplit.
  { iPureIntro. do 8 eexists.
    { apply fresh_locs_isFresh. }
    all: repeat eexists. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (na_heap_alloc_list tls (heap σ1) l
                           ([v])
                           (Reading O) with "Hσ")
    as "(Hσ & Hblock & Hl)".
  { simpl. lia. }
  { intros. destruct H as (?&?). eauto. }
  { destruct H as (H'&?); eauto. eapply H'. }
  { destruct H as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
    by rewrite (loc_add_0) in Hfresh.
  }
  { eauto. }
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro; iSplit; first done. unfold state_init_heap. simpl.
  rewrite /RecordSet.set /= right_id. iFrame.
  iApply "HΦ".
  unfold pointsto_vals. iFrame. rewrite /pointsto_vals_toks. simpl.
  iDestruct "Hl" as "((? & ?) & _)".
  iFrame. iDestruct (na_pointsto_to_heap with "[$]") as "$".
  { destruct H as (H'&?). eapply H'. }
  iPureIntro; split; eauto using isFresh_not_null. destruct H. naive_solver.
Qed.

(* Most proofs of program correctness do not need the block size information,
   so they can use this lemma, which removes the assumption about the struct being non zero
   sized *)
Lemma wp_allocN_seq s E v :
  {{{ True }}} Alloc (Val v) @ s; E
  {{{ l, RET #l; pointsto_vals l (DfracOwn 1) [v] }}}.
Proof.
  iIntros (?) "_ HΦ".
  iApply wp_allocN_seq_sized_meta; auto.
  iNext. iIntros (?) "(_&_&H)". iApply "HΦ".
  iApply (big_sepL_mono with "H"); intros. rewrite /pointsto_vals_toks/pointsto_vals.
  iIntros "(?&?)". iFrame.
Qed.

Lemma wp_alloc_untyped stk E v :
  {{{ True }}} Alloc (Val v) @ stk; E
  {{{ l, RET #l; l ↦ v }}}.
Proof.
  iIntros (?) "_ HΦ". iApply wp_allocN_seq; auto.
  iNext. iIntros (?) "H". iApply "HΦ".
  rewrite /pointsto_vals big_sepL_singleton //=.
  replace (1% nat * 0%nat)%Z with 0 by lia.
  rewrite !loc_add_0. iFrame.
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load #l @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg !>".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iDestruct (na_heap_read with "Hσ Hl") as %([|]&?&Heq&Hlock).
  { simpl in Hlock. congruence. }
  iSplit. { iPureIntro. repeat econstructor; [rewrite Heq //|]; repeat econstructor. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  simpl in *. inv Hstep. progress monad_inv.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro; iSplit=> //. iFrame. iApply "HΦ".
  iApply ("Hl_rest" with "Hl").
Qed.

Theorem is_Writing_Some A (mna: option (nonAtomic A)) a :
  mna = Some (Writing, a) ->
  is_Writing mna.
Proof.
  rewrite /is_Writing; eauto.
Qed.

Hint Resolve is_Writing_Some : core.

Lemma wp_prepare_write s E l v :
  {{{ ▷ l ↦ v }}}
    PrepareWrite (Val #l) @ s; E
  {{{ RET #(); na_heap_pointsto_st WSt l (DfracOwn 1) v ∗ (∀ v', na_heap_pointsto l (DfracOwn 1) v' -∗ l ↦ v') }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iMod (na_heap_write_prepare _ _ _ _ Writing with "Hσ Hl") as (lk1 (Hlookup&Hlock)) "(?&?)"; first done.
  destruct lk1; inversion Hlock; subst. iModIntro.
  iSplit. { iPureIntro. repeat econstructor; [rewrite Hlookup //|]; repeat econstructor. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  simpl in *. inv Hstep. progress monad_inv. simpl in *.
  simpl in *. inv H0. progress monad_inv. simpl in *.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ"; by iFrame.
Qed.

Lemma wp_finish_store s E l v v' :
  {{{ ▷ na_heap_pointsto_st WSt l (DfracOwn 1) v' ∗ (∀ v', na_heap_pointsto l (DfracOwn 1) v' -∗ l ↦ v') }}}
    FinishStore #l (Val v) @ s; E
  {{{ RET #(); l ↦ v }}}.
Proof.
  iIntros (Φ) "[>Hl Hl_rest] HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iMod (na_heap_write_finish_vs _ _ _ _ (Reading 0) with "Hl Hσ") as (lkw (?&Hlock)) "(Hσ&Hl)"; first done.
  destruct lkw; inversion Hlock; subst. iModIntro.
  iSplit. { iPureIntro. repeat econstructor; [rewrite H //|]; repeat econstructor. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  simpl in *. inv Hstep. progress monad_inv. simpl in *.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ".
  iApply ("Hl_rest" with "Hl").
Qed.

Lemma wp_start_read s E l q v :
  {{{ ▷ l ↦{q} v }}} StartRead #l @ s; E
  {{{ RET v; na_heap_pointsto_st (RSt 1) l q v ∗ (∀ v', na_heap_pointsto l q v' -∗ l ↦{q} v') }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iMod (na_heap_read_prepare _ (fun m => match m with | Reading n => Reading (S n) | _ => m end) with "Hσ Hl") as (lk1 n1 (Hlookup&Hlock)) "[Hσ Hl]".
  1: {
    intros lk lkn Hlk. destruct lk; inversion Hlk; subst.
    rewrite /= //.
  }
  destruct lk1; inversion Hlock; subst. iModIntro.
  iSplit. { iPureIntro. repeat econstructor; [rewrite Hlookup //|]; repeat econstructor. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  simpl in *. inv Hstep. progress monad_inv. simpl in *.
  simpl in *. inv H0. progress monad_inv. simpl in *.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ"; by iFrame.
Qed.

Lemma wp_finish_read s E l q v :
  {{{ ▷ na_heap_pointsto_st (RSt 1) l q v ∗ (∀ v', na_heap_pointsto l q v' -∗ l ↦{q} v') }}}
    FinishRead #l @ s; E
  {{{ RET #(); l ↦{q} v }}}.
Proof.
  iIntros (Φ) "[>Hl Hl_rest] HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iMod (na_heap_read_finish_vs _ (fun m => match m with | Reading (S n) => Reading n | _ => m end) with "Hl Hσ") as (lk1 n1 (Hlookup&Hlock)) "[Hσ Hl]".
  1: {
    intros lk lkn Hlk. destruct lk; inversion Hlk; subst.
    rewrite /= //.
  }
  destruct lk1; inversion Hlock; subst. iModIntro.
  iSplit. { iPureIntro. repeat econstructor; [rewrite Hlookup //|]; repeat econstructor. }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  simpl in *. inv Hstep. progress monad_inv. simpl in *.
  simpl in *. inv H0. progress monad_inv. simpl in *.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". iApply "Hl_rest". iApply "Hl".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET #p; proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg".
  iModIntro.
  iSplit.
  { iPureIntro. repeat econstructor. instantiate (1:=(fresh g1.(used_proph_id))).
    apply is_fresh. }
  iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le with "[$]") as "($ & Hproph & $)".
  { rewrite /step_count_next/=. lia. }
  iMod (proph_map_new_proph with "Hproph") as "[$ Hp]"; first done.
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". done.
Qed.

Lemma wp_resolve_proph s E (p : proph_id) (pvs : list val) v :
  {{{ proph p pvs }}}
    ResolveProph #p (Val v) @ s; E
  {{{ pvs', RET #(); ⌜pvs = v::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg".
  iModIntro.
  iSplit. { iPureIntro. repeat econstructor. }
  iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le with "[$]") as "($ & Hproph & $)".
  { rewrite /step_count_next/=. lia. }
  iMod (proph_map_resolve_proph with "[$Hproph $Hp]") as (vs' ->) "[$ Hp]".
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". eauto.
Qed.

End lifting.
End goose_lang.

(*
(* We want [heapGS] to be enough to get [gooseGlobalGS] and [gooseGlobalGS],
*and vice versa*, so we have to be careful to avoid loops. *)
Global Existing Instances goose_globalGS goose_localGS HeapGS.
Hint Cut [ ( _* ) HeapGS ( _* ) (goose_localGS | goose_globalGS)] : typeclass_instances.
Hint Cut [ ( _* ) (goose_localGS | goose_globalGS) ( _* ) HeapGS] : typeclass_instances.
*)
Global Existing Instances goose_globalGS goose_localGS.

Arguments goose_ffiLocalGS {_ _ _ _ hL}: rename.
