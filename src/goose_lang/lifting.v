From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import lib.frac_auth auth numbers gmap excl.
From iris.bi Require Import fractional.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import ectx_lifting.
From Perennial.Helpers Require Import Transitions.
From Perennial.base_logic Require Export proph_map frac_coPset.
From Perennial.algebra Require Export na_heap.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Export notation.
Set Default Proof Using "Type".

Notation nonAtomic T := (naMode * T)%type.

Ltac solve_exec_safe := intros; subst; do 4 eexists; constructor 1; cbn; repeat (monad_simpl; simpl).
Ltac solve_exec_puredet :=
  inversion 1; subst; unfold base_step in *; intros; repeat (monad_inv; simpl in * ); eauto.
Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Section definitions.
  Context `{ext:ffi_syntax}.
  Context `{hG: na_heapGS loc val Σ}.
  Definition heap_pointsto_def l q v : iProp Σ :=
    ⌜l ≠ null⌝ ∗ na_heap_pointsto (L:=loc) (V:=val) l q v.
  Definition heap_pointsto_aux : seal (@heap_pointsto_def). by eexists. Qed.
  Definition heap_pointsto := unseal heap_pointsto_aux.
  Definition heap_pointsto_eq : @heap_pointsto = @heap_pointsto_def :=
    seal_eq heap_pointsto_aux.

  Global Instance heap_pointsto_fractional l v: Fractional (λ q, heap_pointsto l (DfracOwn q) v)%I.
  Proof.
    intros p q.
    rewrite heap_pointsto_eq /heap_pointsto_def.
    rewrite na_heap_pointsto_fractional.
    iSplit.
    - by iIntros "(%&$&$)".
    - by iIntros "[[% $] [% $]]".
  Qed.
  Global Instance heap_pointsto_as_fractional l q v:
    AsFractional (heap_pointsto l (DfracOwn q) v) (λ q, heap_pointsto l (DfracOwn q) v)%I q.
  Proof. rewrite heap_pointsto_eq /heap_pointsto_def.
         econstructor; eauto.
         apply _.
  Qed.
  Global Instance heap_pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (heap_pointsto l dq1 v1)%I (heap_pointsto l dq2 v2)%I ⌜ ✓(dq1 ⋅ dq2) ∧ v1 = v2 ⌝%I.
  Proof. rewrite heap_pointsto_eq /CombineSepGives. iIntros "[[?H1] [?H2]]".
         iCombine "H1 H2" gives %?. iModIntro. iPureIntro. done. Qed.

  Lemma heap_pointsto_agree l q1 q2 v1 v2 : heap_pointsto l q1 v1 ∗ heap_pointsto l q2 v2 -∗ ⌜v1 = v2⌝.
  Proof. iIntros "[H1 H2]". iCombine "H1 H2" gives %[? ?]. done. Qed.

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
Notation "l ↦{# q } v" := (heap_pointsto l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦□ v" := (heap_pointsto l DfracDiscarded v%V)
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{ q } v" := (heap_pointsto l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (heap_pointsto l (DfracOwn 1) v%V)
  (at level 20, v at next level) : bi_scope.

Notation "l ↦{# q } -" := (∃ v, l ↦{#q} v)%I
  (at level 20, q at level 50, format "l  ↦{# q }  -") : bi_scope.
Notation "l ↦□ -" := (∃ v, l ↦□ v)%I
  (at level 20, format "l  ↦□  -") : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{#1} -)%I (at level 20) : bi_scope.

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
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Definition traceO := leibnizO (list event).
Definition OracleO := leibnizO (Oracle).

Record tr_names : Set := {
  trace_name : gname;
  oracle_name : gname;
}.

Class traceGS (Σ: gFunctors) : Set := {
  #[global] trace_inG :: inG Σ (authR (optionUR (exclR traceO)));
  #[global] oracle_inG :: inG Σ (authR (optionUR (exclR OracleO)));
  trace_tr_names : tr_names;
}.

Class trace_preG (Σ: gFunctors) : Set := {
  #[global] trace_preG_inG :: inG Σ (authR (optionUR (exclR traceO)));
  #[global] oracle_preG_inG :: inG Σ (authR (optionUR (exclR OracleO)));
}.

Definition traceGS_update (Σ: gFunctors) (hT: traceGS Σ) (names: tr_names) :=
  {| trace_inG := trace_inG; oracle_inG := oracle_inG; trace_tr_names := names |}.

Definition traceGS_update_pre (Σ: gFunctors) (hT: trace_preG Σ) (names: tr_names) :=
  {| trace_inG := trace_preG_inG; oracle_inG := oracle_preG_inG; trace_tr_names := names |}.

Definition traceΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR traceO)));
      GFunctor (authR (optionUR (exclR OracleO)))].

Global Instance subG_crashG {Σ} : subG traceΣ Σ → trace_preG Σ.
Proof. solve_inG. Qed.

Definition trace_auth `{hT: traceGS Σ} (l: Trace) :=
  own (trace_name (trace_tr_names)) (● (Excl' (l: traceO))).
Definition trace_frag `{hT: traceGS Σ} (l: Trace) :=
  own (trace_name (trace_tr_names)) (◯ (Excl' (l: traceO))).
Definition oracle_auth `{hT: traceGS Σ} (o: Oracle) :=
  own (oracle_name (trace_tr_names)) (● (Excl' (o: OracleO))).
Definition oracle_frag `{hT: traceGS Σ} (o: Oracle) :=
  own (oracle_name (trace_tr_names)) (◯ (Excl' (o: OracleO))).

Lemma trace_init `{hT: trace_preG Σ} (l: list event) (o: Oracle):
  ⊢ |==> ∃ H : traceGS Σ, trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o .
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iModIntro. iExists {| trace_tr_names := {| trace_name := γ; oracle_name := γ' |} |}. iFrame.
Qed.

Lemma trace_name_init `{hT: trace_preG Σ} (l: list event) (o: Oracle):
  ⊢ |==> ∃ name : tr_names, let _ := traceGS_update_pre _ _ name in
                           trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o.
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iModIntro. iExists {| trace_name := γ; oracle_name := γ' |}. iFrame.
Qed.

Lemma trace_reinit `(hT: traceGS Σ) (l: list event) (o: Oracle):
  ⊢ |==> ∃ names : tr_names, let _ := traceGS_update Σ hT names in
     trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o.
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iModIntro. iExists {| trace_name := γ; oracle_name := γ' |}. iFrame.
Qed.

Lemma trace_update `{hT: traceGS Σ} (l: Trace) (x: event):
  trace_auth l -∗ trace_frag l ==∗ trace_auth (add_event x l) ∗ trace_frag (add_event x l).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' _ ⋅ ◯ Excl' _) with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

Lemma trace_agree `{hT: traceGS Σ} (l l': list event):
  trace_auth l -∗ trace_frag l' -∗ ⌜ l = l' ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  done.
Qed.

Lemma oracle_agree `{hT: traceGS Σ} (o o': Oracle):
  oracle_auth o -∗ oracle_frag o' -∗ ⌜ o = o' ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  done.
Qed.

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
Class gooseGlobalGS Σ : Set := GooseGlobalGS {
  goose_invGS : invGS Σ;
  #[global] goose_prophGS :: proph_mapGS proph_id val Σ;
  #[global] goose_creditGS :: creditGS Σ;
  goose_ffiGlobalGS : ffiGlobalGS Σ;
}.
(* Per-generation / "local" ghost state.

TODO: in program_logic we use the term "generation", in GooseLang we say "local".
Would be good to align terminology. *)
Class gooseLocalGS Σ : Set := GooseLocalGS {
  goose_crashGS : crashGS Σ;
  goose_ffiLocalGS : ffiLocalGS Σ;
  #[global] goose_na_heapGS :: na_heapGS loc val Σ;
  #[global] goose_traceGS :: traceGS Σ;
}.

(* For convenience we also have a class that bundles both the
   global and per-generation parameters.
   For historic reasons, this is called heapGS
   TODO: rename to gooseGS, or remove. *)
Local Set Primitive Projections.
Class heapGS Σ : Set := HeapGS {
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
     pinv_tok mj D)%I;
  fork_post _ := True%I;
}.
Next Obligation.
  iIntros (Σ ? g ns q D κs) "($&$&$&Hcred&Htok)".
  iFrame. iMod (cred_interp_incr with "Hcred") as "($&_)". eauto.
Qed.
Next Obligation. intros => //=. lia. Qed.

Global Program Instance goose_generationGS `{L: !gooseLocalGS Σ}:
  generationGS goose_lang Σ := {
  iris_crashGS := goose_crashGS;
  state_interp σ nt :=
    (na_heap_ctx tls σ.(heap) ∗ ffi_local_ctx goose_ffiLocalGS σ.(world)
      ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I;
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
  | H : base_step_atomic ?e _ _ _ _ _ _ _ |- _ =>
    apply base_step_atomic_inv in H; [ | solve [ inversion 1 ] ]
  | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
    rewrite /base_step /= in H;
    monad_inv; repeat (simpl in H; monad_inv)
  end.

Local Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (base_step_atomic _ _ _ _ _ _ _ _) => apply base_step_trans : core.
Local Hint Extern 1 (base_step _ _ _ _ _ _ _ _) => rewrite /base_step /= : core.
Local Hint Extern 1 (relation.bind _ _ _ _ _) => monad_simpl; simpl : core.
Local Hint Extern 1 (relation.runF _ _ _ _) => monad_simpl; simpl : core.
(* Local Hint Extern 0 (base_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core. *)
Local Hint Extern 0 (base_step_atomic (AllocN _ _) _ _ _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (base_step_atomic (NewProph) _ _ _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Extern 0 (base_step_atomic (ArbitraryInt) _ _ _ _ _ _ _) => apply arbitrary_int_step : core.
Local Hint Resolve to_of_val : core.

Theorem heap_base_atomic e :
  (forall σ κ e' σ' efs,
      relation.denote (base_trans e) σ σ' (κ, e', efs) -> is_Some (to_val e')) ->
  base_atomic StronglyAtomic e.
Proof.
  intros Hdenote.
  hnf; intros * H.
  inversion H; subst; clear H.
  - apply Hdenote in H0; auto.
  - eauto.
  - eauto.
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

Global Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
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
Global Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. monad_inv. eauto. Qed.
Global Instance skip_atomic s  : Atomic s Skip.
Proof. solve_atomic. simpl in H; monad_inv. eauto. Qed.
Global Instance linearize_atomic s : Atomic s Linearize.
Proof. rewrite /Linearize. apply _. Qed.
Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
(*
Global Instance ext_atomic s op v : Atomic s (ExternalOp op (Val v)).
Proof. solve_atomic. Qed.
 *)
Global Instance input_atomic s v : Atomic s (Input (Val v)).
Proof. solve_atomic. Qed.
Global Instance output_atomic s v : Atomic s (Output (Val v)).
Proof. solve_atomic. Qed.
Global Instance resolve_atomic s p w : Atomic s (ResolveProph (Val (LitV (LitProphecy p))) (Val w)).
Proof. solve_atomic. monad_inv. eauto. Qed.

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] reduces lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] does reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) : Set :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Global Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Global Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Global Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Global Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Global Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instances for EqOp. *)
Global Instance pure_eqop v1 v2 :
  PureExec (is_comparable v1 ∧ is_comparable v2) 1
           (BinOp EqOp (Val v1) (Val v2))
           (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /bin_op_eval_eq /= //.
  rewrite decide_True //.
Qed.

Global Instance pure_eqop_lit l1 l2 :
  PureExec True 1
    (BinOp EqOp (Val (LitV l1)) (Val (LitV l2)))
    (Val $ LitV $ LitBool $ bool_decide (LitV l1 = LitV l2)) | 1.
Proof.
  intros Hcompare.
  apply pure_eqop; auto.
Qed.

Global Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Global Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Global Instance pure_total_le v1 v2 :
  PureExec True 1 (TotalLe (Val v1) (Val v2)) (Val $ LitV $ LitBool $ val_le v1 v2).
Proof. solve_pure_exec. Qed.

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
  iIntros (σ1 g1 ns mj D κ κs n) "(Hσ&?&?&?) Hg !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step; iFrame.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_output s E tr lit :
  {{{ trace_frag tr }}}
     Output (LitV lit) @ s; E
  {{{ RET (LitV LitUnit); trace_frag (add_event (Out_ev lit) tr)}}}.
Proof.
  iIntros (Φ) "Htr HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 g1 ns mj D κ κs n) "(Hσ&?&Htr_auth&?) Hg !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step. iFrame.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iMod (trace_update with "[$] [$]") as "(?&?)".
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iFrame; iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_input s E tr (sel: u64) Or :
  {{{ trace_frag tr ∗ oracle_frag Or }}}
     Input (LitV (LitInt sel)) @ s; E
  {{{ RET (LitV (LitInt (Or tr sel))); trace_frag (add_event (In_ev sel (LitInt (Or tr sel))) tr) ∗ oracle_frag Or}}}.
Proof.
  iIntros (Φ) "(Htr&Hor) HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 g1 ns mj D κ κs n) "(Hσ&?&Htr_auth&Hor_auth) Hg !>"; iSplit.
  { iPureIntro. unshelve (by eauto); apply (W64 0). }
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iDestruct (oracle_agree with "[$] [$]") as %?; subst.
  iFrame. iMod (trace_update with "[$] [$]") as "(?&?)".
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iFrame; iSplitL; last done. iApply ("HΦ" with "[$]").
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
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

Theorem concat_replicate_S A n (vs: list A) :
  concat_replicate (S n) vs = vs ++ concat_replicate n vs.
Proof.
  reflexivity.
Qed.

Theorem concat_replicate_length A n (vs: list A) :
  length (concat_replicate n vs) = (n * length vs)%nat.
Proof.
  induction n; simpl; auto.
  rewrite concat_replicate_S length_app IHn //.
Qed.

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

Definition big_opL_add_spec (M: ofe) (o: M -> M -> M) {mon:monoid.Monoid o} f start off k n :=
  Proper (equiv ==> equiv ==> equiv) o ->
  big_opL o (fun i x => f (i + k)%nat x) (seq (start + off) n) ≡
  big_opL o (fun i x => f i (x + off)%nat) (seq (start + k)%nat n).

(*
Eval compute in (fun M o {mon:monoid.Monoid o} f off => big_opL_add_spec M o f 2%nat off 4%nat).
*)

Theorem big_opL_add (M: ofe) (o: M -> M -> M) {mon:monoid.Monoid o} f start off k n :
  Proper (equiv ==> equiv ==> equiv) o ->
  big_opL o (fun i x => f (k + i)%nat x) (seq (start + off) n) ≡
  big_opL o (fun i x => f (k + i)%nat (x + off)%nat) (seq start n).
Proof.
  intros.
  revert start k off.
  induction n; simpl; auto; intros.
  apply H; auto.
  setoid_rewrite Nat.add_succ_r.
  rewrite <- (IHn (S start) (S k)).
  simpl; auto.
Qed.

Theorem big_sepL_offset {b:bi} f off n :
  big_opL (@bi_sep b) (fun i x => f i x) (seq off n) ≡
  big_opL bi_sep (fun i x => f i (x + off)%nat) (seq 0%nat n).
Proof.
  apply (big_opL_add _ _ _ 0%nat _ 0%nat _ _).
Qed.

Lemma Zmul_nat_add1_r (x k:nat) :
  (x + 1)%nat * k = k + x * k.
Proof. lia. Qed.

Lemma heap_seq_replicate_to_nested_pointsto l vs (n : nat) (P: loc → val → iProp Σ) :
  ([∗ list] j ↦ v ∈ concat_replicate n vs, P (l +ₗ j) v )-∗
  [∗ list] i ∈ seq 0 n, [∗ list] j ↦ v ∈ vs, P (l +ₗ ((i : nat) * Z.of_nat (length vs)) +ₗ j)%nat v.
Proof.
  iIntros "Hvs".
  iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite concat_replicate_S.
  iDestruct (big_sepL_app with "Hvs") as "[Hvs Hconcat]".
  iSplitL "Hvs".
  - rewrite loc_add_0.
    iFrame.
  - setoid_rewrite Nat2Z.inj_add.
    setoid_rewrite <- loc_add_assoc.
    iDestruct ("IH" with "Hconcat") as "Hseq".
    rewrite (big_sepL_offset _ 1%nat).
    setoid_rewrite Zmul_nat_add1_r.
    setoid_rewrite <- loc_add_assoc.
    iExact "Hseq".
Qed.

Lemma alloc_list_loc_not_null:
  ∀ v (n : u64) σg1 l,
    isFresh σg1 l
    → ∀ l0 (x : val),
      heap_array l (concat_replicate (uint.nat n) (flatten_struct v)) !! l0 = Some x
      → l0 ≠ null.
Proof.
  intros v n σg1 l H l0 x Heq.
  apply heap_array_lookup in Heq.
  destruct Heq as [l' (?&->&Heq)].
  apply H; eauto.
Qed.

Lemma allocN_loc_not_null:
  ∀ v (n : u64) σg1 l,
    isFresh σg1 l
    → ∀ l0 (x : val),
      heap_array l (concat_replicate (uint.nat n) (flatten_struct v)) !! l0 = Some x
      → l0 ≠ null.
Proof.
  intros v n σg1 l H l0 x Heq.
  apply heap_array_lookup in Heq.
  destruct Heq as [l' (?&->&Heq)].
  apply H; eauto.
Qed.

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

Lemma wp_allocN_seq_sized_meta s E v (n: u64) :
  (0 < length (flatten_struct v))%nat →
  (0 < uint.Z n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); ⌜ l ≠ null ∧ addr_offset l = 0%Z ⌝ ∗
                              na_block_size l (uint.nat n * length (flatten_struct v))%nat ∗
                              [∗ list] i ∈ seq 0 (uint.nat n),
                              (pointsto_vals_toks (l +ₗ (length (flatten_struct v) * Z.of_nat i)) (DfracOwn 1)
                                                (flatten_struct v))
                              }}}.
Proof.
  iIntros (Hlen Hn Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs k) "[Hσ ?] Hg !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (na_heap_alloc_list tls (heap σ1) l
                           (concat_replicate (uint.nat n) (flatten_struct v))
                           (Reading O) with "Hσ")
    as "(Hσ & Hblock & Hl)".
  { rewrite concat_replicate_length. cut (0 < uint.nat n)%nat; first by lia.
    word. }
  { destruct H as (?&?); eauto. }
  { destruct H as (H'&?); eauto. eapply H'. }
  { destruct H as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
    by rewrite (loc_add_0) in Hfresh.
  }
  { eauto. }
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro; iSplit; first done.
  iFrame.
  iApply "HΦ".
  unfold pointsto_vals.
  rewrite concat_replicate_length. iFrame.
  iDestruct (heap_seq_replicate_to_nested_pointsto l (flatten_struct v) (uint.nat n)
                                                 (λ l v, l ↦ v ∗ meta_token l ⊤)%I
               with "[Hl]") as "Hl".
  {
    iApply (big_sepL_mono with "Hl").
    iIntros (l0 x Heq) "(Hli&$)".
    iApply (na_pointsto_to_heap with "Hli").
    destruct H as (H'&?). eapply H'.
  }
  iSplitL "".
  { iPureIntro; split; eauto using isFresh_not_null, isFresh_offset0. }
  iApply (big_sepL_mono with "Hl").
  iIntros (k0 j _) "H".
  setoid_rewrite Z.mul_comm at 1.
  setoid_rewrite Z.mul_comm at 2.
  rewrite /pointsto_vals_toks. eauto.
Qed.

Lemma wp_allocN_seq0 s E v (n: u64) :
  length (flatten_struct v) = 0%nat →
  (0 < uint.Z n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); True }}}.
Proof.
  iIntros (Hlen Hn Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs k) "[Hσ ?] Hg !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  rewrite /state_interp/=.
  assert (concat_replicate (uint.nat n) (flatten_struct v) = []) as ->.
  { apply nil_length_inv. rewrite concat_replicate_length. lia. }
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  rewrite fmap_nil //= left_id. iFrame. iSplitL ""; eauto. by iApply "HΦ".
Qed.

(* Most proofs of program correctness do not need the block size information,
   so they can use this lemma, which removes the assumption about the struct being non zero
   sized *)
Lemma wp_allocN_seq s E v (n: u64) :
  (0 < uint.Z n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (uint.nat n),
                              (pointsto_vals (l +ₗ (length (flatten_struct v) * Z.of_nat i)) (DfracOwn 1) (flatten_struct v)) }}}.
Proof.
  iIntros (??) "_ HΦ".
  destruct (length (flatten_struct v)) eqn:Hlen.
  - iApply wp_allocN_seq0; auto. iNext. iIntros (l) "_". iApply "HΦ".
    apply nil_length_inv in Hlen. rewrite Hlen //=.
    rewrite /pointsto_vals. setoid_rewrite big_sepL_nil.
    iInduction (seq 0 (uint.nat n)) as [| ??] "IH"; eauto => //=.
  - iApply wp_allocN_seq_sized_meta; auto.
    { lia. }
    iNext. iIntros (?) "(_&_&H)". iApply "HΦ".
    iApply (big_sepL_mono with "H"); intros. rewrite /pointsto_vals_toks/pointsto_vals.
    iApply (big_sepL_mono); intros. iIntros "(?&?)". rewrite -Hlen. iFrame.
Qed.

Lemma wp_alloc_untyped stk E v v0 :
  flatten_struct v = [v0] ->
  {{{ True }}} ref (Val v) @ stk; E
  {{{ l, RET LitV (LitLoc l); l ↦ v0 }}}.
Proof.
  assert (0 < uint.Z (W64 1)) by (change (uint.Z 1) with 1; lia).
  iIntros (Hflat ?) "_ HΦ". iApply wp_allocN_seq; auto.
  iNext. iIntros (?) "H". iApply "HΦ".
  change (uint.nat 1) with 1%nat; simpl.
  rewrite /pointsto_vals Hflat big_sepL_singleton //=.
  replace (1% nat * 0%nat)%Z with 0 by lia.
  rewrite !loc_add_0 right_id. eauto.
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg !>".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iDestruct (na_heap_read with "Hσ Hl") as %([|]&?&Heq&Hlock).
  { simpl in Hlock. congruence. }
  iSplit; first by eauto 8.
  iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
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
  {{{ ▷ l ↦ v }}} PrepareWrite (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET #(); na_heap_pointsto_st WSt l (DfracOwn 1) v ∗ (∀ v', na_heap_pointsto l (DfracOwn 1) v' -∗ l ↦ v') }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iMod (na_heap_write_prepare _ _ _ _ Writing with "Hσ Hl") as (lk1 (Hlookup&Hlock)) "(?&?)"; first done.
  destruct lk1; inversion Hlock; subst. iModIntro.
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ"; by iFrame.
Qed.

Lemma wp_finish_store s E l v v' :
  {{{ ▷ na_heap_pointsto_st WSt l (DfracOwn 1) v' ∗ (∀ v', na_heap_pointsto l (DfracOwn 1) v' -∗ l ↦ v') }}} FinishStore (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) "[>Hl Hl_rest] HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iMod (na_heap_write_finish_vs _ _ _ _ (Reading 0) with "Hl Hσ") as (lkw (?&Hlock)) "(Hσ&Hl)"; first done.
  destruct lkw; inversion Hlock; subst. iModIntro.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ".
  iApply ("Hl_rest" with "Hl").
Qed.

Lemma wp_start_read s E l q v :
  {{{ ▷ l ↦{q} v }}} StartRead (Val $ LitV (LitLoc l)) @ s; E
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
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ"; by iFrame.
Qed.

Lemma wp_finish_read s E l q v :
  {{{ ▷ na_heap_pointsto_st (RSt 1) l q v ∗ (∀ v', na_heap_pointsto l q v' -∗ l ↦{q} v') }}}
    FinishRead (Val $ LitV (LitLoc l)) @ s; E
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
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". iApply "Hl_rest". iApply "Hl".
Qed.

Lemma na_heap_valid_map (σ: gmap _ _) l q vs :
  na_heap_ctx tls σ -∗
              ([∗ map] l↦v ∈ heap_array l vs, l ↦{q} v) -∗
              ⌜forall i, (i < (length vs))%nat -> is_Some (σ !! (l +ₗ i))⌝.
Proof.
  iIntros "Hctx Hmap".
  iIntros (i Hi).
  apply lookup_lt_is_Some_2 in Hi.
  destruct Hi as [v ?].
  assert (heap_array l vs !! (l +ₗ i) = Some v).
  { apply heap_array_lookup.
    exists (Z.of_nat i).
    rewrite Nat2Z.id; intuition eauto.
    lia. }
  iDestruct (big_sepM_lookup _ _ _ _ H0 with "Hmap") as "H".
  iDestruct (na_heap_read with "Hctx [H]") as %(?&?&?&?).
  { iDestruct (heap_pointsto_na_acc with "H") as "[$ _]". }
  eauto.
Qed.

Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg !>".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iDestruct (@na_heap_read with "Hσ Hl") as %(lk&?&?&?Hlock).
  destruct lk; inversion Hlock; subst.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro; iSplit=> //. iFrame. iApply "HΦ".
  iApply ("Hl_rest" with "Hl").
Qed.

Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "[Hσ ?] Hg".
  iDestruct (heap_pointsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iDestruct (@na_heap_read_1 with "Hσ Hl") as %(lk&?&?Hlock).
  destruct lk; inversion Hlock; subst.
  iMod (na_heap_write _ _ _ (Reading 0) with "Hσ Hl") as "(?&?)"; first done.
  iModIntro.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  rewrite bool_decide_true //.
  iMod (global_state_interp_le _ _ _ _ _ κs with "[$]") as "$".
  { rewrite /step_count_next/=. lia. }
  iModIntro. iSplit=>//. iFrame. iApply "HΦ".
  iApply ("Hl_rest" with "[$]").
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg".
  iModIntro. iSplit; first by eauto 10.
  iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le with "[$]") as "($ & Hproph & $)".
  { rewrite /step_count_next/=. lia. }
  iMod (proph_map_new_proph with "Hproph") as "[$ Hp]"; first done.
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". done.
Qed.

Lemma wp_resolve_proph s E (p : proph_id) (pvs : list val) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = v::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg".
  iModIntro. iSplit; first by eauto 10.
  iNext; iIntros (v2' σ2 g2 efs Hstep); inv_base_step.
  iMod (global_state_interp_le with "[$]") as "($ & Hproph & $)".
  { rewrite /step_count_next/=. lia. }
  iMod (proph_map_resolve_proph with "[$Hproph $Hp]") as (vs' ->) "[$ Hp]".
  iModIntro. iSplit=>//. iFrame. iApply "HΦ". eauto.
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

(*
Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply Ectx_step with (K:=[]); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl.
  constructor.
  rewrite /base_step /=.
  econstructor.
  - by apply prim_step_to_val_is_base_step.
  - simpl.
    econstructor; auto.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  base_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst.
    inv_base_step. repeat inv_undefined.
    inversion_clear step. repeat inv_undefined.
    simpl in H0; monad_inv.
    rewrite /base_step /=.
    econstructor; eauto; simpl.
    econstructor; auto.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - assert (fill_item K (fill Ks e1') = fill (Ks ++ [K]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item K (fill Ks e2') = fill (Ks ++ [K]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [K]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply Ectx_step with (K0 := Ks ++ [K]); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - assert (to_val (fill Ks e1') = Some vp); first by rewrite -H1 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /base_step /= in step; monad_inv.
    - assert (to_val (fill Ks e1') = Some vt); first by rewrite -H2 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /base_step /= in step; monad_inv.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (q σ1 ns κ κs n) "(Hσ&Hκ&Hw) HNC". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! q σ1 ns [] κs n with "[$Hσ $Hκ $Hw] [$]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    rewrite /base_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    match goal with H: [] = ?κs ++ [_] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! q σ1 ns _ _ n with "[$Hσ $Hκ $Hw] [$]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    rewrite /base_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    simplify_list_eq.
    rename v0 into w', s2 into σ2, l into efs.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ (Hκ&Hw)] WPe]".
    iMod (proph_map_resolve_proph p (w',v) κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iFrame. iIntros.
    iMod ("HΦ" with "[$]") as "(HΦ&?)". iModIntro. iFrame. by iApply "HΦ".
Qed.

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply wp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.
*)

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

#[global]
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Arguments goose_ffiLocalGS {_ _ _ _ hL}: rename.
