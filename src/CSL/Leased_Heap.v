From iris.algebra Require Import auth gmap frac agree namespace_map excl.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import gen_heap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class leased_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := LeasedHeapG {
  leased_heap_heapG :> gen_heapG L V Σ;
  leased_heap_exclG :> inG Σ (authR (optionUR (exclR (leibnizO V))));
  leased_heap_gen : namespace;
}.
Arguments leased_heap_heapG {_ _ _ _ _} _ : assert.
Arguments leased_heap_exclG {_ _ _ _ _} _ : assert.
Arguments leased_heap_gen {_ _ _ _ _} _ : assert.

Class leased_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  leased_heap_heapPreG :> gen_heapPreG L V Σ;
  leased_heap_exclPreG :> inG Σ (authR (optionUR (exclR (leibnizO V))));
}.

Definition leased_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  gen_heapΣ L V; GFunctor (authR (optionUR (exclR (leibnizO V))))
].

Instance subG_leased_heapPreG {Σ L V} `{Countable L} :
  subG (leased_heapΣ L V) Σ → leased_heapPreG L V Σ.
Proof. solve_inG. Qed.

Definition current_gen (N: namespace) := ndot N 0.
Definition next_gen (N: namespace) := ndot N 1.

Lemma split_gen_disj N : current_gen N ## next_gen N.
Proof. solve_ndisj. Qed.

Definition next_leased_heapG `{hG: leased_heapG L V Σ} :=
  LeasedHeapG _ _ _ _ _ (@leased_heap_heapG _ _ _ _ _ hG)
                        (@leased_heap_exclG _ _ _ _ _ hG)
                        (next_gen (leased_heap_gen hG)).

Section definitions.
  Context {L V} `{Countable L, hG: !leased_heapG L V Σ}.

  Definition lease (l: L) (v : V) :=
    (∃ γ : gname, meta l (current_gen (leased_heap_gen hG)) γ
                  ∗ own γ (◯ (Excl' (v: leibnizO V))))%I.

  (* TODO: alternate name possibilities: 'deed' or 'title'? *)
  Definition master (l: L) (v: V) :=
    (∃ γ : gname, meta l (current_gen (leased_heap_gen hG)) γ
                  ∗ meta_token l (↑ next_gen (leased_heap_gen hG))
                  ∗ own γ (● (Excl' (v: leibnizO V))))%I.
End definitions.

Local Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Definition next_lease `{hG: leased_heapG L V Σ} (l: L) (v : V) :=
  lease (hG := next_leased_heapG) l v.

Definition next_master `{hG: leased_heapG L V Σ} (l: L) (v : V) :=
  master (hG := next_leased_heapG) l v.


Section lease_heap.
  Context {L V} `{Countable L, hG: !leased_heapG L V Σ}.

  Implicit Types P Q : iPropO Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of leases and masters *)
  Global Instance lease_timeless l v : Timeless (lease l v).
  Proof. apply _. Qed.
  Global Instance master_timeless l v : Timeless (master l v).
  Proof. apply _. Qed.

  Lemma master_lease_agree l (v1 v2 : V) :
    master l v1 -∗ lease l v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iDestruct 1 as (γm1) "(Hγ1&_&Hown1)"; iDestruct 1 as (γm2) "(Hγ2&Hown2)".
    iDestruct (meta_agree with "Hγ1 Hγ2") as %->.
    iDestruct (own_valid_2 with "Hown1 Hown2") as "H".
    iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
    done.
  Qed.

  Lemma meta_lease_init N l (γ: gname):
    meta_token l (↑N) ==∗ meta l (current_gen N) γ ∗ meta_token l (↑ next_gen N).
  Proof.
    rewrite (union_difference_L (↑ next_gen N) (↑N)); last by solve_ndisj.
    iIntros "H".
    iDestruct (meta_token_union with "H") as "($&?)"; first set_solver.
    by iMod (meta_set _ _ γ (current_gen N) with "[$]") as "$"; first solve_ndisj.
  Qed.

  Lemma master_next l v :
    master l v ==∗ next_master l v ∗ next_lease l v.
  Proof.
    iDestruct 1 as (γ) "(Hγ&Hrest&Hown)".
    iMod (own_alloc (● (Excl' (v: leibnizO V)) ⋅ ◯ (Excl' (v: leibnizO V)))) as (γ') "[H1 H2]".
    { apply auth_both_valid; split; eauto. econstructor. }
    iMod (meta_lease_init _ _ γ' with "Hrest") as "(#Hset&Hrest)".
    iModIntro. iSplitL "Hrest H1"; by iExists _; iFrame.
  Qed.

  Lemma master_lease_alloc l v :
    meta_token l ⊤ ==∗ master l v ∗ lease l v.
  Proof.
    iIntros "H".
    iMod (own_alloc (● (Excl' (v: leibnizO V)) ⋅ ◯ (Excl' (v: leibnizO V)))) as (γ) "[H1 H2]".
    { apply auth_both_valid; split; eauto. econstructor. }
    rewrite (union_difference_L (↑ leased_heap_gen hG) ⊤); last by solve_ndisj.
    iDestruct (meta_token_union with "H") as "(H&_)"; first set_solver.
    iMod (meta_lease_init _ _ γ with "H") as "(#Hset&Hrest)".
    iModIntro. iSplitL "Hrest H1"; by iExists _; iFrame.
  Qed.

  Lemma big_sepM_master_lease_alloc σ :
    ([∗ map] l↦v ∈ σ, meta_token l ⊤) ==∗ ([∗ map] l↦v ∈ σ, master l v ∗ lease l v).
  Proof.
    iIntros "H".
    iApply (big_opM_forall (λ P Q, P ==∗ Q)); auto using bupd_intro.
    { intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -bupd_sep. }
    iApply big_sepM_mono; last by eauto.
    intros; by iApply master_lease_alloc.
  Qed.

  Lemma master_lease_update l v v0 v':
    master l v -∗ lease l v0 ==∗ master l v' ∗ lease l v'.
  Proof.
    iDestruct 1 as (γm1) "(Hγ1&Hrest&Hown1)"; iDestruct 1 as (γm2) "(Hγ2&Hown2)".
    iDestruct (meta_agree with "Hγ1 Hγ2") as %->.
    iMod (own_update_2 _ _ _ (● Excl' (v': leibnizO V) ⋅ ◯ Excl' (v': leibnizO V))
            with "Hown1 Hown2") as "[Hown1 Hown2]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iModIntro.
    iSplitL "Hγ1 Hrest Hown1"; iExists _; iFrame.
  Qed.

  Lemma leased_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v ∗ master l v ∗ lease l v.
  Proof.
    iIntros (Hσl) "H".
    iMod (gen_heap_alloc σ l v with "H") as "($&$&H)"; first done.
    by iApply master_lease_alloc.
  Qed.

End lease_heap.

Lemma heap_init_to_bigOp `{hG: leased_heapG L V Σ} (σ: gmap L V):
  own (i := @gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
      (gen_heap_name (leased_heap_heapG hG))
      (◯ to_gen_heap σ)
      -∗
  [∗ map] i↦v ∈ σ,  i ↦ v .
Proof.
  induction σ as [| ???? IH] using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (i := @gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
                 (gen_heap_name (leased_heap_heapG hG))
                 (◯ to_gen_heap m) ∗
                 (i ↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IH.
Qed.

Lemma leased_heap_strong_init `{H: leased_heapPreG L V Σ} σ :
  (|==> ∃ (H0 : leased_heapG L V Σ)
          (Hpf: @gen_heap_inG _ _ _ _ _ (leased_heap_heapG H0) =
                gen_heap_preG_inG), gen_heap_ctx σ
                ∗ ([∗ map] i↦v ∈ σ, i ↦ v ∗ master i v ∗ lease i v))%I.
Proof.
  iMod (own_alloc (● to_gen_heap ∅)) as (γ) "Hg".
  { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
  iMod (own_alloc (● to_gen_meta ∅)) as (γm) "Hm".
  { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
  set (hG := (GenHeapG L V Σ _ _ _ _ _ γ γm)).
  set (hL := (LeasedHeapG L V Σ _ _ hG _ (1%positive :: nil))).
  iAssert (gen_heap_ctx (hG := hG) ∅) with "[-]" as "H".
  { iExists ∅. iFrame. eauto. }
  iMod (gen_heap_alloc_gen ∅ σ with "H") as "(Hctx&Hheap&Hmeta)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L.
  iMod (big_sepM_master_lease_alloc σ with "[$Hmeta]").
  iModIntro.
  iExists hL, eq_refl.
  iFrame. iApply big_sepM_sep. iFrame.
Qed.
