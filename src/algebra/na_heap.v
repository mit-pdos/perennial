From Coq Require Import Min.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

(* Heap that supports non-atomic operations. Very mildly adapted from
   lambda-rust by Jung et al., and generalized to support arbitrary
   domains/ranges of values, as opposed to lambda-rust locs and values. *)

Definition lock_stateR : cmraT :=
  csumR (exclR unitO) natR.

Definition na_heapUR (L V: Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR (prodR fracR lock_stateR) (agreeR (leibnizO V))).

Class na_heapG (L V: Type) Σ `{Countable L} := Na_HeapG {
  na_heap_inG :> inG Σ (authR (na_heapUR L V));
  na_heap_name : gname;
}.

Arguments na_heap_name {_ _ _ _ _} _ : assert.

Class na_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  na_heap_preG_inG :> inG Σ (authR (na_heapUR L V));
}.

Definition na_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (authR (na_heapUR L V))
].

Instance subG_na_heapPreG {Σ L V} `{Countable L} :
  subG (na_heapΣ L V) Σ → na_heapPreG L V Σ.
Proof. solve_inG. Qed.

Inductive lock_state :=
  | WSt : lock_state
  | RSt: nat → lock_state.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.

Definition to_na_heap {L V LK} `{Countable L} (tls : LK → lock_state) :
  gmap L (LK * V) → na_heapUR L V :=
  fmap (λ v, (1%Qp, to_lock_stateR (tls (v.1)), to_agree (v.2))).

Section definitions.
  Context `{Countable L, hG : !na_heapG L V Σ}.
  Context `{LK} (tls: LK → lock_state).

  Definition na_heap_mapsto_st (st : lock_state)
             (l : L) (q : Qp) (v: V) : iProp Σ :=
    own (na_heap_name hG) (◯ {[ l := (q, to_lock_stateR st, to_agree v) ]}).

  Definition na_heap_mapsto_def (l : L) (q : Qp) (v: V) : iProp Σ :=
    na_heap_mapsto_st (RSt 0) l q v.
  Definition na_heap_mapsto_aux : seal (@na_heap_mapsto_def). by eexists. Qed.
  Definition na_heap_mapsto := unseal na_heap_mapsto_aux.
  Definition na_heap_mapsto_eq : @na_heap_mapsto = @na_heap_mapsto_def :=
    seal_eq na_heap_mapsto_aux.

  Definition na_heap_ctx (σ:gmap L (LK * V)) : iProp Σ :=
     own (na_heap_name hG) (● to_na_heap tls σ).
End definitions.

Typeclasses Opaque na_heap_mapsto.
Instance: Params (@na_heap_mapsto) 4 := {}.

Notation "l ↦{ q } v" := (na_heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (na_heap_mapsto l 1 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section to_na_heap.
  Context (L V LK : Type) `{Countable L}.
  Implicit Types σ : gmap L (LK * V).
  Implicit Types m : gmap L gname.

  Lemma to_na_heap_valid tls σ : ✓ to_na_heap tls σ.
  Proof.
    intros l. rewrite lookup_fmap.
    case (σ !! l) =>//=. intros (lk&v) => //=. destruct (tls lk) => //=.
  Qed.

  Lemma lookup_to_na_heap_None tls σ l : σ !! l = None → to_na_heap tls σ !! l = None.
  Proof. by rewrite /to_na_heap lookup_fmap=> ->. Qed.

  Lemma to_na_heap_insert tls σ l x v :
    to_na_heap tls (<[l:=(x, v)]> σ)
    = <[l:=(1%Qp, to_lock_stateR (tls x), to_agree v)]> (to_na_heap tls σ).
  Proof. by rewrite /to_na_heap fmap_insert. Qed.

  Lemma to_na_heap_delete tls σ l : to_na_heap tls (delete l σ) = delete l (to_na_heap tls σ).
  Proof. by rewrite /to_na_heap fmap_delete. Qed.
End to_na_heap.

Lemma na_heap_init `{Countable L, !na_heapPreG L V Σ} {LK} (tls: LK → lock_state) σ :
  ⊢ |==> ∃ _ : na_heapG L V Σ, na_heap_ctx tls σ.
Proof.
  iMod (own_alloc (● to_na_heap tls σ)) as (γh) "Hh".
  { rewrite auth_auth_valid. exact: to_na_heap_valid. }
  iModIntro. iExists (Na_HeapG L V Σ _ _ _ γh).
  iFrame "Hh".
Qed.

Section na_heap.
  Context {L V} {LK: Type} `{Countable L, hG: !na_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L (LK * V).
  Implicit Types h g : na_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.
  Implicit Types E : coPset.

  (** General properties of mapsto and freeable *)
  Global Instance na_heap_mapsto_timeless l q v : Timeless (l↦{q}v).
  Proof. rewrite na_heap_mapsto_eq /na_heap_mapsto_def. apply _. Qed.

  Global Instance na_heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q.
    by rewrite na_heap_mapsto_eq -own_op -auth_frag_op op_singleton -pair_op agree_idemp.
  Qed.
  Global Instance na_heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma na_heap_mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite na_heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite op_singleton -pair_op singleton_valid=> -[? /agree_op_invL'->]; eauto.
  Qed.

  Lemma na_heap_alloc tls σ l v lk :
    σ !! l = None →
    tls lk = RSt 0 →
    na_heap_ctx tls σ ==∗ na_heap_ctx tls (<[l:=(lk, v)]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl Hread). rewrite /na_heap_ctx.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, Cinr 0%nat, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_na_heap_None. }
    iModIntro. rewrite na_heap_mapsto_eq/na_heap_mapsto_def. iFrame "Hl".
    rewrite to_na_heap_insert Hread //=.
  Qed.

  Lemma na_heap_alloc_gen tls σ σ' :
    σ' ##ₘ σ →
    (∀ l lkv, σ' !! l = Some lkv → tls (lkv.1) = RSt 0) →
    na_heap_ctx tls σ ==∗
    na_heap_ctx tls (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v.2).
  Proof.
    revert σ; induction σ' as [| l lkv σ' Hl IH] using map_ind; iIntros (σ Hdisj Hread) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    { intros l' lkv' ?. apply (Hread l').
      rewrite lookup_insert_ne //= => ?. subst. congruence.
    }
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    iMod (na_heap_alloc _ _ l _ (fst lkv) with "Hσ'σ") as "(? & ?)";
      first by apply lookup_union_None.
    { eapply (Hread l). rewrite lookup_insert //=. }
    { by destruct lkv; iFrame. }
  Qed.

  Lemma na_heap_mapsto_lookup tls σ l lk (q: Qp) v :
    own (na_heap_name hG) (● to_na_heap tls σ) -∗
    own (na_heap_name hG) (◯ {[ l := (q, to_lock_stateR lk, to_agree v) ]}) -∗
    ⌜∃ ls' (n' : nat),
                σ !! l = Some (ls', v) ∧
                tls ls' = match lk with
                          | RSt n => RSt (n+n')
                          | WSt => WSt
                          end⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid.
    iPureIntro. move: Hl=> /singleton_included [[[q' ls'] dv]].
    rewrite /to_na_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct lk as [|n] eqn:Hls, (tls ls'') as [|n''] eqn:Hls',
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    { by exists ls'', O. }
    { by exists ls'', n'. }
    { by exists ls'', O; rewrite Nat.add_0_r. }
  Qed.

  Lemma na_heap_mapsto_lookup_1 tls σ l lk v :
    own (na_heap_name hG) (● to_na_heap tls σ) -∗
    own (na_heap_name hG) (◯ {[ l := (1%Qp, to_lock_stateR lk, to_agree v) ]}) -∗
    ⌜∃ ls', σ !! l = Some (ls', v) ∧ tls ls' = lk⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid.
    iPureIntro. move: Hl=> /singleton_included [[[q' ls'] dv]].
    rewrite /to_na_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct (tls ls'') eqn:Hls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    exists ls''. destruct lk, (tls ls''); rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma na_heap_read_vs tls σ n1 n2 nf l q v lk lk':
    σ !! l = Some (lk, v) →
    tls lk = RSt (n1 + nf) →
    tls lk' = RSt (n2 + nf) →
    own (na_heap_name hG) (● to_na_heap tls σ) -∗ na_heap_mapsto_st (RSt n1) l q v
    ==∗ own (na_heap_name hG) (● to_na_heap tls (<[l:=(lk', v)]> σ))
        ∗ na_heap_mapsto_st (RSt n2) l q v.
  Proof.
    intros Hσv Hr1 Hr2. apply wand_intro_r. rewrite -!own_op to_na_heap_insert.
    eapply own_update, auth_update. apply: singleton_local_update.
    { by rewrite /to_na_heap lookup_fmap Hσv. }
    rewrite Hr1 Hr2 => //=.
    unshelve (apply: prod_local_update_1).
    unshelve (apply: prod_local_update_2).
    apply csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma na_heap_read tls σ l q v :
    na_heap_ctx tls σ -∗ l ↦{q} v -∗ ∃ lk n, ⌜σ !! l = Some (lk, v) ∧ tls lk = RSt n⌝.
  Proof.
    iIntros "Hσ". iIntros "Hmt".
    rewrite na_heap_mapsto_eq.
    iDestruct (na_heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma na_heap_read_1 tls σ l v :
    na_heap_ctx tls σ -∗ l ↦ v -∗ ⌜∃ lk, σ !! l = Some (lk, v) ∧ tls lk = RSt O⌝.
  Proof.
    iIntros "Hσ Hmt".
    rewrite na_heap_mapsto_eq.
    iDestruct (na_heap_mapsto_lookup_1 with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.


  (* States whether the rl function has the effect of updating a lk
     to a lk with an additional reader *)
  Definition is_read_lock tls (rl: LK → LK) :=
    (∀ lk n, tls lk = RSt n → tls (rl lk) = RSt (S n)).

  Definition is_read_unlock tls (url: LK → LK) :=
    (∀ lk n, tls lk = RSt (S n) → tls (url lk) = RSt n).

  Lemma na_heap_read_na tls rl url σ l q v :
    is_read_lock tls rl →
    is_read_unlock tls url →
    na_heap_ctx tls σ -∗ l ↦{q} v ==∗ ∃ lk n,
      ⌜σ !! l = Some (lk, v) ∧ tls lk = RSt n⌝ ∗
      na_heap_ctx tls (<[l:=(rl lk, v)]> σ) ∗
      (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n2,
             ⌜σ2 !! l = Some (lk, v) ∧ tls lk = RSt (S n2) ⌝ ∗
             na_heap_ctx tls (<[l:=(url lk, v)]> σ2) ∗ l ↦{q} v).
  Proof.
    iIntros (Hrl Hurl) "Hσ Hmt".
    rewrite na_heap_mapsto_eq.
    iDestruct (na_heap_mapsto_lookup with "Hσ Hmt") as %[lk [n [Hσl Hlkeq]]]; eauto.
    iMod (na_heap_read_vs _ _ 0 1 with "Hσ Hmt") as "[Hσ Hmt]"; [ done | done | by eapply Hrl | ].
    iModIntro. iExists lk, n; iSplit; [done|]. iFrame "Hσ".
    clear dependent lk n σ. iIntros (σ2). iIntros "Hσ".
    iDestruct (na_heap_mapsto_lookup with "Hσ Hmt") as %[lk [n [Hσl Hlkeq]]]; eauto.
    iMod (na_heap_read_vs _ _ 1 0 with "Hσ Hmt") as "[Hσ Hmt]"; [ done | done | by eapply Hurl | ].
    iExists lk, n; iModIntro; iSplit; [done|]. iFrame.
  Qed.

  Lemma na_heap_write_vs tls σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own (na_heap_name hG) (● to_na_heap tls σ) -∗ na_heap_mapsto_st (tls st1) l 1%Qp v
    ==∗ own (na_heap_name hG) (● to_na_heap tls (<[l:=(st2, v')]> σ))
        ∗ na_heap_mapsto_st (tls st2) l 1%Qp v'.
  Proof.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_na_heap_insert.
    eapply own_update, auth_update. apply: singleton_local_update.
    { by rewrite /to_na_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct (tls st2).
  Qed.

  Lemma na_heap_write tls σ l lk v v' :
    tls lk = RSt 0 →
    na_heap_ctx tls σ -∗ l ↦ v ==∗ na_heap_ctx tls (<[l:=(lk, v')]> σ) ∗ l ↦ v'.
  Proof.
    iIntros (Hread_lk) "Hσ Hmt".
    rewrite na_heap_mapsto_eq.
    iDestruct (na_heap_mapsto_lookup_1 with "Hσ Hmt") as %(?&?&Hread); auto.
    iMod (na_heap_write_vs with "Hσ [Hmt]") as "[Hσ ?]"; first done.
    { by rewrite /na_heap_mapsto_def Hread. }
    iFrame. rewrite /na_heap_mapsto_def Hread_lk. by iFrame.
  Qed.

  Definition tls_write_unique (tls: LK → _) :=
    ∀ lk1 lk2, tls lk1 = WSt → tls lk2 = WSt → lk1 = lk2.

  Lemma na_heap_write_prepare tls σ l v lkw :
    tls lkw = WSt →
    na_heap_ctx tls σ -∗ l ↦ v ==∗
      ∃ lk1,
      ⌜ σ !! l = Some (lk1, v) ∧ tls lk1 = RSt 0 ⌝ ∗
      na_heap_ctx tls (<[l:=(lkw, v)]> σ) ∗
      na_heap_mapsto_st WSt l 1%Qp v.
  Proof.
    iIntros (Hwrite) "Hσ Hmt".
    rewrite na_heap_mapsto_eq.
    iDestruct (na_heap_mapsto_lookup_1 with "Hσ Hmt") as %(lkr&?&Hread); eauto.
    iMod (na_heap_write_vs with "Hσ [Hmt]") as "[Hσ Hmt]"; first done.
    { by rewrite /na_heap_mapsto_def Hread. }
    iModIntro. iExists lkr. iSplit; [done|]. iFrame. rewrite Hwrite //.
  Qed.

  Lemma na_heap_write_finish_vs tls l v v' lk' :
    tls lk' = RSt 0 →
    na_heap_mapsto_st WSt l 1%Qp v -∗
    (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lkw, ⌜σ2 !! l = Some (lkw, v) ∧ tls lkw = WSt⌝ ∗
        na_heap_ctx tls (<[l:=(lk', v')]> σ2) ∗ l ↦ v').
  Proof.
    iIntros (Hread) "Hmt". iIntros (σ) "Hσ".
    iDestruct (na_heap_mapsto_lookup with "Hσ Hmt") as %(lk2&n&Hσl&Hlk'); eauto.
    iMod (na_heap_write_vs _ _ _ lk' with "Hσ [Hmt]") as "[Hσ Hmt]"; first done.
    { by rewrite Hlk'. }
    iExists lk2. iFrame. iModIntro; iSplit; [done|].
    { by rewrite na_heap_mapsto_eq /na_heap_mapsto_def Hread. }
  Qed.

  Lemma na_heap_write_na tls σ l v v' lkw :
    tls_write_unique tls →
    tls lkw = WSt →
    na_heap_ctx tls σ -∗ l ↦ v ==∗
      ∃ lk1,
      ⌜ σ !! l = Some (lk1, v) ∧ tls lk1 = RSt 0 ⌝ ∗
      na_heap_ctx tls (<[l:=(lkw, v)]> σ) ∗
      ∀ σ2, na_heap_ctx tls σ2 ==∗ ⌜σ2 !! l = Some (lkw, v)⌝ ∗
        na_heap_ctx tls (<[l:=(lk1, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iIntros (Huniq Hwrite) "Hσ Hmt".
    iMod (na_heap_write_prepare with "Hσ Hmt") as (lkr (?&Hread)) "[Hσ Hmt]"; eauto.
    iPoseProof (na_heap_write_finish_vs with "Hmt") as "Hmt"; eauto.
    iModIntro. iExists _. iFrame.
    iSplit; [done|]. iIntros. iMod ("Hmt" with "[$]") as (? (->&?)) "[Hσ Hmt]". iFrame.
    iPureIntro; repeat f_equal. eapply Huniq; eauto.
  Qed.
End na_heap.

Section na_heap_defs.
  Context {L V : Type} `{Countable L}.

  Record na_heap_names :=
    {
      na_heap_heap_name : gname;
    }.

  Definition na_heapG_update {Σ} (hG: na_heapG L V Σ) (names: na_heap_names) :=
    Na_HeapG _ _ _ _ _
             (@na_heap_inG _ _ _ _ _ hG)
             (na_heap_heap_name names).

  Definition na_heapG_update_pre {Σ} (hG: na_heapPreG L V Σ) (names: na_heap_names) :=
    Na_HeapG _ _ _ _ _
             (@na_heap_preG_inG _ _ _ _ _ hG)
             (na_heap_heap_name names).

  Definition na_heapG_get_names {Σ} (hG: na_heapG L V Σ) : na_heap_names :=
    {| na_heap_heap_name := na_heap_name hG; |}.

  Lemma na_heapG_get_update {Σ} (hG: na_heapG L V Σ) :
    na_heapG_update hG (na_heapG_get_names hG) = hG.
  Proof. destruct hG => //=. Qed.

  Lemma na_heapG_update_pre_get {Σ} (hG: na_heapPreG L V Σ) names:
    (na_heapG_get_names (na_heapG_update_pre hG names)) = names.
  Proof. destruct hG, names => //=. Qed.

  Lemma na_heap_name_init `{!na_heapPreG L V Σ} {LK} (tls: LK → _) σ :
    ⊢ |==> ∃ names : na_heap_names, na_heap_ctx (hG := na_heapG_update_pre _ names) tls σ.
  Proof.
    iMod (own_alloc (● to_na_heap tls σ)) as (γh) "Hh".
    { rewrite auth_auth_valid. exact: to_na_heap_valid. }
    iModIntro. iExists {| na_heap_heap_name := γh |}.
    iFrame "Hh".
  Qed.

  Lemma na_heap_reinit {Σ} (hG: na_heapG L V Σ) {LK} (tls: LK → _) σ :
    ⊢ |==> ∃ names : na_heap_names, na_heap_ctx (hG := na_heapG_update hG names) tls σ.
  Proof.
    iMod (own_alloc (● to_na_heap tls σ)) as (γh) "Hh".
    { rewrite auth_auth_valid. exact: to_na_heap_valid. }
    iModIntro. iExists {| na_heap_heap_name := γh |}.
    iFrame "Hh".
  Qed.

End na_heap_defs.
