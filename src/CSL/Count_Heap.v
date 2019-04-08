(* This is a modification of the Iris 'gen_heap'.v file to using counting
   permissions and arbitrary function maps instead of fractional permissions and gmaps
   a very common pattern for Armada examples. *)

From iris.algebra Require Import auth agree functions csum.
From RecoveryRefinement.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Export RecoveryRefinement.Spec.LockDefs.

Set Default Proof Using "Type".
Import uPred.
From Classes Require Import EqualDec.
Import EqualDecNotation.

Global Instance partial_fn_insert (A T : Type) `{EqualDec A} : Insert A T (A → option T) :=
  λ (a : A) (t : T) (f : A → option T) (b : A),
    if b == a then Some t else f b.
Global Instance partial_fn_delete (A T : Type) `{EqualDec A} : Delete A (A → option T) :=
  λ (a : A) (f : A → option T) (b : A),
    if b == a then None else f b.

Definition lockR :=
  csumR natR (agreeR unitC).

Definition to_lock (s: LockStatus) : lockR :=
  match s with
  | Locked => Cinr (to_agree tt)
  | ReadLocked n => Cinl (S n)
  | Unlocked => Cinl O
  end.

Definition gen_heapUR (L V: Type) `{EqualDec L}: ucmraT :=
  ofe_funUR (fun (a: L) => optionUR (prodR countingR (prodR lockR (agreeR (leibnizC V))))).
Definition to_gen_heap {L V} `{EqualDec L} (f: L → option (LockStatus * V))
  : gen_heapUR L V :=
  λ k, match (f k) with
       | None => None
       | Some (s, v) => Some (Count 0, (to_lock s, to_agree (v: leibnizC V)))
       end.

(** The CMRA we need. *)
Class gen_heapG (L V : Type) (Σ : gFunctors) `{EqualDec L} := GenHeapG {
  gen_heap_inG :> inG Σ (authR (@gen_heapUR L V _));
  gen_heap_name : gname
}.
Arguments gen_heap_name {_ _ _ _} _ : assert.

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{EqualDec L} :=
  { gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V)) }.

Definition gen_heapΣ (L V : Type) `{EqualDec L} : gFunctors :=
  #[GFunctor (authR (gen_heapUR L V))].

Instance subG_gen_heapPreG {Σ L V} `{EqualDec L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_heapG L V Σ}.

  Definition gen_heap_ctx (σ : L → option (LockStatus * V)) : iProp Σ :=
    own (gen_heap_name hG) (● (to_gen_heap σ)).

  Definition mapsto_def (l : L) (n: Z) (s: LockStatus) (v: V) : iProp Σ :=
    own (gen_heap_name hG)
        (◯ (fun l' =>
              if l' == l then
                Some (Count (n: Z), (to_lock s, to_agree (v : leibnizC V)))
              else
                ε)).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Definition read_mapsto l s v := mapsto l (-1) s v.
End definitions.

Local Notation "l ↦{ q } v" := (mapsto l q Unlocked v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 0 Unlocked v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{0} -)%I (at level 20) : bi_scope.

Local Notation "l r↦ v" := (read_mapsto l Unlocked v) (at level 20, format "l  r↦  v") : bi_scope.

Local Notation "l r↦ -" := (∃ v, l r↦ v)%I
  (at level 20, format "l  r↦ -") : bi_scope.

Section to_gen_heap.
  Context (L V : Type) `{EqualDec L}.
  Implicit Types σ : L → option (LockStatus * V).

  (** Conversion to heaps and back *)
  Lemma to_gen_heap_valid σ : ✓ to_gen_heap σ.
  Proof. rewrite /to_gen_heap => l. case (σ l) as [([]&?)|];
         by (econstructor; simpl; eauto).
  Qed.
  Lemma lookup_to_gen_heap_None σ l : σ l = None → to_gen_heap σ l = None.
  Proof. rewrite /to_gen_heap. by case (σ l). Qed.
  Lemma gen_heap_singleton_included σ l q s v :
    ((fun l' => if l' == l then
                  Some (Count q, (to_lock s, to_agree (v : leibnizC V)))
                else
                  ε) : gen_heapUR L V) ≼ to_gen_heap σ → ∃ s', σ l = Some (s', v) ∧
                                                               to_lock s ≼ to_lock s'.
  Proof.
    intros Hincl. apply (ofe_fun_included_spec_1 _ _ l) in Hincl.
    move: Hincl. rewrite /to_gen_heap.
    destruct (l == l); last congruence.
    destruct (σ l) as [(s'&v')|].
    - move/Some_pair_included=> [_ Hincl].
      apply Some_pair_included in Hincl as [Hincl1 Hincl2].
      move /Some_included_total/to_agree_included/leibniz_equiv_iff in Hincl2; subst.
      exists s'; split; auto.
      apply Some_included in Hincl1 as [->|?]; auto.
      destruct s' => //=; apply csum_included; intuition eauto.
    - rewrite option_included. intros [?|Hcase].
      * congruence.
      * repeat destruct Hcase as [? Hcase]. congruence.
  Qed.

  Lemma to_lock_inj s s': to_lock s ≡ to_lock s' → s = s'.
    destruct s, s'; inversion 1; auto; congruence.
  Qed.

  Lemma gen_heap_singleton_full_included σ l s v :
    ((fun l' => if l' == l then
                  Some (Count 0, (to_lock s, to_agree (v : leibnizC V)))
                else
                  ε) : gen_heapUR L V) ≼ to_gen_heap σ → σ l = Some (s, v).
  Proof.
    intros Hincl. apply (ofe_fun_included_spec_1 _ _ l) in Hincl.
    move: Hincl. rewrite /to_gen_heap.
    destruct (l == l); last congruence.
    destruct (σ l) as [(s'&v')|].
    - move /Some_included_exclusive => Hequiv.
      feed pose proof (Hequiv) as Hequiv'; clear Hequiv.
      { repeat econstructor =>//=. destruct s'; econstructor. }
      destruct Hequiv' as [? [Heq1 Heq2]].
      move/to_lock_inj in Heq1;
      move/to_agree_inj/leibniz_equiv_iff in Heq2; subst; auto.
    - rewrite option_included. intros [?|Hcase].
      * congruence.
      * repeat destruct Hcase as [? Hcase]. congruence.
  Qed.
  Lemma to_gen_heap_insert l s v σ :
    to_gen_heap (<[l:=(s, v)]> σ)
                ≡ <[l:=(Count 0, (to_lock s, to_agree (v:leibnizC V)))]> (to_gen_heap σ).
  Proof.
    rewrite /to_gen_heap=> k//=.
    rewrite /insert/partial_fn_insert.
    destruct ((k == l)) => //=.
  Qed.
  Lemma to_gen_heap_delete l σ :
    to_gen_heap (delete l σ) ≡ delete l (to_gen_heap σ).
  Proof.
    rewrite /to_gen_heap=> k//=.
    rewrite /delete/partial_fn_delete.
    destruct ((k == l)) => //=.
  Qed.
End to_gen_heap.

Lemma gen_heap_init `{gen_heapPreG L V Σ} σ :
  (|==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ)%I.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. by iExists (GenHeapG L V Σ _ _ γ).
Qed.

Lemma gen_heap_strong_init `{H: gen_heapPreG L V Σ} σs :
  (|==> ∃ (H0 : gen_heapG L V Σ) (Hpf: gen_heap_inG = gen_heap_preG_inG), gen_heap_ctx σs ∗
    own (gen_heap_name _) (◯ (to_gen_heap σs)))%I.
Proof.
  iMod (own_alloc (● to_gen_heap σs ⋅ ◯ to_gen_heap σs)) as (γ) "(?&?)".
  { apply auth_valid_discrete_2; split; auto. exact: to_gen_heap_valid. }
  iModIntro. unshelve (iExists (GenHeapG L V Σ _ _ γ), _); auto. iFrame.
Qed.

Section gen_heap.
  Context `{hG: gen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : L → option (LockStatus * V).
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l q m v : Timeless (mapsto l q m v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance read_mapsto_timeless l v : Timeless (l r↦ v).
  Proof. apply _. Qed.

  (* This is an odd special lemma *)
  Lemma gen_heap_init_to_bigOp `{Countable L} (σ: gmap L (LockStatus * V)):
    (∀ s x, σ !! s = Some x → fst x = Unlocked) →
    own (gen_heap_name hG) (◯ to_gen_heap (λ s, σ !! s))
        -∗ [∗ map] i↦x ∈ σ, i ↦ snd x.
  Proof.
    induction σ using map_ind.
    - iIntros. rewrite //=.
    - iIntros (Hunlocked) "Hown".
      rewrite big_opM_insert //.
      iAssert (own (gen_heap_name hG) (◯ to_gen_heap (λ s, m !! s)) ∗ (i ↦ snd x))%I
        with "[Hown]" as "[Hrest $]".
      {
        rewrite mapsto_eq /mapsto_def //.
        iAssert (own (gen_heap_name hG) (◯ to_gen_heap (<[i:=x]>(λ s : L,  m !! s))))
                with "[Hown]" as "Hown'".
        { iApply (own_proper with "Hown"). f_equiv.
          intros k. rewrite /to_gen_heap/insert/partial_fn_insert//=.
          destruct (equal).
          * subst. rewrite lookup_insert //=.
          * rewrite lookup_insert_ne //=.
        }
        assert (fst x = Unlocked) as Heq_unlocked.
        { eapply (Hunlocked i). by rewrite lookup_insert. }
        destruct x as (l&v).
        rewrite to_gen_heap_insert.
        rewrite -own_op.
        iApply (own_proper with "Hown'").
        rewrite -auth_frag_op. f_equiv. intros k.
        rewrite ofe_fun_lookup_op.
        rewrite /insert/partial_fn_insert//=.
        destruct (k == i).
        - subst. rewrite lookup_to_gen_heap_None //.
          rewrite left_id. simpl in Heq_unlocked. by rewrite Heq_unlocked.
        - by rewrite right_id.
      }
      iApply IHσ.
      * intros. eapply (Hunlocked s). rewrite lookup_insert_ne; eauto.
        intros Heq. congruence.
      * eauto.
  Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=.
    intros Hval. move: (Hval l). rewrite ofe_fun_lookup_op.
    destruct ((l == l)); last by congruence.
    rewrite -Some_op pair_op.
    by intros [_ [_ ?%agree_op_invL']].
  Qed.

  Lemma mapsto_valid l q1 q2 v1 v2 : q1 >= 0 → q2 >= 0 → l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ False.
  Proof.
    intros ??.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=.
    intros Hval. move: (Hval l). rewrite ofe_fun_lookup_op.
    destruct ((l == l)); last by congruence.
    rewrite -Some_op pair_op.
    intros [Hcount ?].
    rewrite counting_op' //= in Hcount.
    repeat destruct decide => //=. lia.
  Qed.

  Lemma mapsto_valid' l v1 v2: l ↦{0} v1 -∗ l ↦{-1} v2 -∗ False.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=.
    intros Hval. move: (Hval l). rewrite ofe_fun_lookup_op.
    destruct ((l == l)); last by congruence.
    rewrite -Some_op pair_op.
    intros [Hcount ?].
    rewrite counting_op' //= in Hcount.
  Qed.

  Lemma read_split_join1 l (q: nat) n v :
    mapsto l q (ReadLocked n) v ⊣⊢
           mapsto l (S q) Unlocked v ∗ mapsto l (-1) (ReadLocked n) v.
  Proof.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op.
    f_equiv. split => //= l'. rewrite ofe_fun_lookup_op.
    destruct ((l' == l)) => //=.
    rewrite -Some_op ?pair_op.
    rewrite counting_op' //= Cinl_op.
    replace (S q + (-1))%Z with (q : Z) by lia.
    assert (0 ⋅ S n = (S n)) as Hop by auto.
    replace (S q + (-1))%Z with (q : Z) by lia.
    repeat (destruct (decide)); try lia.
    rewrite Hop.
    rewrite agree_idemp //=.
  Qed.

  Lemma read_split_join2 l (q: nat) n v :
    mapsto l q (ReadLocked n) v ⊣⊢
           mapsto l (S q) (ReadLocked n) v ∗ mapsto l (-1) Unlocked v.
  Proof.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op.
    f_equiv. split => //= l'. rewrite ofe_fun_lookup_op.
    destruct ((l' == l)) => //=.
    rewrite -Some_op ?pair_op.
    rewrite counting_op' //= Cinl_op.
    replace (S q + (-1))%Z with (q : Z) by lia.
    assert (S n ⋅ 0 = (S n)) as Hop by auto.
    replace (S q + (-1))%Z with (q : Z) by lia.
    repeat (destruct (decide)); try lia.
    rewrite Hop.
    rewrite agree_idemp //=.
  Qed.

  Lemma read_split_join3 l (q: nat) v :
    mapsto l q Locked v ⊣⊢
           mapsto l (S q) Locked v ∗ mapsto l (-1) Locked v.
  Proof.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op.
    f_equiv. split => //= l'. rewrite ofe_fun_lookup_op.
    destruct ((l' == l)) => //=.
    rewrite -Some_op ?pair_op.
    rewrite counting_op' //= Cinr_op.
    replace (S q + (-1))%Z with (q : Z) by lia.
    repeat (destruct (decide)); try lia.
    rewrite ?agree_idemp //=.
  Qed.

  Lemma read_split_join l (q: nat) v : l ↦{q} v ⊣⊢ (l ↦{S q} v ∗ l r↦ v).
  Proof.
    rewrite /read_mapsto mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op.
    f_equiv. split => //= l'. rewrite ofe_fun_lookup_op.
    destruct ((l' == l)) => //=.
    rewrite -Some_op ?pair_op.
    rewrite counting_op' //= Cinl_op.
    replace (S q + (-1))%Z with (q : Z) by lia.
    repeat (destruct (decide)); try lia.
    rewrite agree_idemp //=.
  Qed.

  (* TODO move *)
  Lemma ofe_fun_local_update `{EqualDec A} {B: A → ucmraT} f1 f2 f1' f2' :
    (∀ x, (f1 x, f2 x) ~l~> (f1' x , f2' x)) →
    (f1 : ofe_fun B, f2) ~l~> (f1', f2').
  Proof.
    intros Hupd.
    apply local_update_unital=> n mf Hmv Hm; simpl in *.
    split.
    - intros k. specialize (Hupd k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (Hupd n (Some (mf k))); eauto.
    - intros k. specialize (Hupd k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (Hupd n (Some (mf k))); eauto.
  Qed.

  Lemma gen_heap_ctx_proper σ σ' :
    (∀ k, σ k = σ' k) →
    gen_heap_ctx σ -∗ gen_heap_ctx σ'.
  Proof.
    intros Hequiv. rewrite /gen_heap_ctx.
    iApply own_mono.
    rewrite /to_gen_heap.
    apply auth_included; split; auto => //=.
    exists ε. rewrite right_id.
    do 2 f_equiv. intros k. rewrite Hequiv; eauto.
  Qed.

  Lemma gen_heap_alloc σ l v :
    σ l = None → gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=(Unlocked, v)]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hnone) "Hσ". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iMod (own_update _ _ (● to_gen_heap (<[l := (Unlocked, v)]> σ) ⋅
                            ◯ <[l := (Count 0, (Cinl 0, to_agree v))]>ε)
            with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc. apply ofe_fun_local_update => k.
      rewrite /to_gen_heap.
      rewrite /insert/partial_fn_insert.
      destruct ((k == l)).
      * subst. rewrite /insert/partial_fn_insert. destruct ((l == l)); last by congruence.
        rewrite Hnone.
        rewrite ofe_fun_lookup_empty.
        apply (alloc_option_local_update (Count 0, (to_lock Unlocked, to_agree (v:leibnizC _))))=> //.
      * reflexivity.
    }
    by iFrame.
  Qed.

  Lemma gen_heap_dealloc σ l v :
    gen_heap_ctx σ -∗ l ↦ v ==∗ gen_heap_ctx (delete l σ).
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    rewrite to_gen_heap_delete. iApply (own_update_2 with "Hσ Hl").
    eapply auth_update_dealloc.
    apply ofe_fun_local_update => k.
    rewrite /delete/partial_fn_delete.
    destruct ((k == l)).
    * apply delete_option_local_update; apply _.
    * reflexivity.
  Qed.

  Lemma gen_heap_valid1 σ l s v :
    gen_heap_ctx σ -∗ mapsto l 0 s v -∗ ⌜σ l = Some (s, v)⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl _]%auth_valid_discrete_2; auto.
    apply gen_heap_singleton_full_included in Hl; eauto.
  Qed.

  Lemma gen_heap_valid2 σ l z s v :
    gen_heap_ctx σ -∗ mapsto l z s v -∗
    ⌜ ∃ s' : LockStatus, σ l = Some (s', v) ∧ to_lock s ≼ to_lock s' ⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl _]%auth_valid_discrete_2; auto.
    apply gen_heap_singleton_included in Hl; eauto.
  Qed.

  Lemma gen_heap_valid σ l q v :
    gen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜∃ s, σ l = Some (s, v) ∧ s ≠ Locked ⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[(s'&Hl&Hincl)%gen_heap_singleton_included _]%auth_valid_discrete_2; auto.
    iExists s'; iPureIntro; split; auto.
    destruct s'; auto.
    rewrite //= in Hincl.
    apply csum_included in Hincl.
    destruct Hincl as [|[(?&?&?)|(?&?&?)]]; intuition; try congruence.
  Qed.

  (*
  Lemma gen_heap_valid_2 σ l v : gen_heap_ctx σ -∗ l r↦ v -∗ ⌜σ l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx read_mapsto_eq /read_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.
   *)

  Lemma gen_heap_update σ l s1 s2 v1 v2 :
    gen_heap_ctx σ -∗ mapsto l 0 s1 v1 ==∗ gen_heap_ctx (<[l:=(s2,v2)]>σ) ∗ mapsto l 0 s2 v2.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2.
    iMod (own_update_2 _ _ _ (● to_gen_heap (<[l := (s2, v2)]> σ)
                                ⋅ ◯ <[l := (Count 0, (to_lock s2, to_agree v2))]>ε)
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      rewrite /to_gen_heap/insert/partial_fn_insert//=.
      destruct ((k == l)).
      * subst. destruct Hl as (s'&Hl&?). rewrite Hl.
        unshelve (apply: option_local_update).
        apply exclusive_local_update=>//=.
        repeat econstructor =>//=. destruct s2; econstructor.
      * reflexivity.
    }
    by iFrame.
  Qed.

  Lemma Cinl_included_nat (n m: nat): (Cinl n : lockR) ≼ Cinl m → n <= m.
  Proof.
    rewrite csum_included.
    intros [|[(n'&m'&Heqn&Heqm&Hincl)|(?&?&?)]]; intuition; try congruence.
    inversion Heqn. inversion Heqm. subst.
    by apply nat_included in Hincl.
  Qed.

  Lemma Cinl_included_nat' (n: nat) s:
    (Cinl n : lockR) ≼ to_lock s → ∃ m, n <= m ∧ to_lock s = Cinl m.
  Proof.
    rewrite csum_included.
    intros [|[(n'&m'&Heqn&Heqm&Hincl)|(?&?&?)]]; intuition; try congruence.
    { destruct s; simpl in *; congruence. }
    inversion Heqn. inversion Heqm. subst.
     apply nat_included in Hincl.
    eexists; split; eauto.
  Qed.

  Lemma Cinr_included_excl' s:
    (Cinr (to_agree tt): lockR) ≼ to_lock s → s = Locked.
  Proof.
    rewrite csum_included.
    intros [|[(n'&m'&Heqn&Heqm&Hincl)|(?&?&?)]]; intuition;
      destruct s; simpl in *; congruence.
  Qed.

  Lemma gen_heap_readlock σ l q v :
    gen_heap_ctx σ -∗ mapsto l q Unlocked v ==∗ ∃ s, ⌜ σ l = Some (s, v) ⌝ ∗
                 gen_heap_ctx (<[l:=(force_read_lock s,v)]>σ) ∗ mapsto l q (ReadLocked 0) v.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2.
    destruct Hl as (s&Hl&Hincl).
    iMod (own_update_2 _ _ _ (● to_gen_heap (<[l := (force_read_lock s, v)]> σ)
                                ⋅ ◯ <[l := (Count q, (to_lock (ReadLocked 0), to_agree v))]>ε)
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      rewrite /to_gen_heap/insert/partial_fn_insert//=.
      destruct ((k == l)).
      * subst. rewrite Hl.
        unshelve (apply: option_local_update).
        unshelve (apply: prod_local_update_2).
        destruct s.
        ** simpl in Hincl. apply csum_included in Hincl.
           destruct Hincl as [|[(?&?&?)|(?&?&?)]]; intuition; try congruence.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           apply csum_local_update_l.
           apply nat_local_update; lia.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           apply csum_local_update_l.
           apply nat_local_update; lia.
      * reflexivity.
    }
    iExists s. by iFrame.
  Qed.

  Lemma gen_heap_readlock' σ l q v n :
    gen_heap_ctx σ -∗ mapsto l q (ReadLocked n) v ==∗ ∃ s, ⌜ σ l = Some (s, v) ⌝ ∗
                 gen_heap_ctx (<[l:=(force_read_lock s,v)]>σ)
                 ∗ mapsto l q (ReadLocked (S n)) v.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2.
    destruct Hl as (s&Hl&Hincl).
    iMod (own_update_2 _ _ _ (● to_gen_heap (<[l := (force_read_lock s, v)]> σ)
                                ⋅ ◯ <[l := (Count q, (to_lock (ReadLocked (S n)), to_agree v))]>ε)
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      rewrite /to_gen_heap/insert/partial_fn_insert//=.
      destruct ((k == l)).
      * subst. rewrite Hl.
        unshelve (apply: option_local_update).
        unshelve (apply: prod_local_update_2).
        destruct s.
        ** simpl in Hincl. apply csum_included in Hincl.
           destruct Hincl as [|[(?&?&?)|(?&?&?)]]; intuition; try congruence.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           apply csum_local_update_l.
           apply nat_local_update; lia.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           apply csum_local_update_l.
           apply nat_local_update; lia.
      * reflexivity.
    }
    iExists s. by iFrame.
  Qed.

  Lemma gen_heap_readunlock σ l q n v :
    gen_heap_ctx σ -∗ mapsto l q (ReadLocked n) v ==∗ ∃ n', ⌜ σ l = Some (ReadLocked n', v) ⌝ ∗
                 gen_heap_ctx (<[l:=(force_read_unlock (ReadLocked n'),v)]>σ)
                 ∗ mapsto l q (force_read_unlock (ReadLocked n)) v.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2.
    destruct Hl as (s&Hl&Hincl).
    iMod (own_update_2 _ _ _ (● to_gen_heap (<[l := (force_read_unlock s, v)]> σ)
                                ⋅ ◯ <[l := (Count q, (to_lock (force_read_unlock (ReadLocked n)),
                                                      to_agree v))]>ε)
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      rewrite /to_gen_heap/insert/partial_fn_insert//=.
      destruct ((k == l)).
      * subst. rewrite Hl.
        unshelve (apply: option_local_update).
        unshelve (apply: prod_local_update_2).
        destruct s.
        ** simpl in Hincl. apply csum_included in Hincl.
           destruct Hincl as [|[(?&?&?)|(?&?&?)]]; intuition; try congruence.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           destruct num, n => //=;
           apply csum_local_update_l;
           apply nat_local_update; lia.
        ** simpl.
           unshelve (apply: prod_local_update_1).
           simpl in Hincl. apply Cinl_included_nat in Hincl. lia.
      * reflexivity.
    }
    apply Cinl_included_nat' in Hincl as (m&?&Heq).
    destruct s; simpl in *; inversion Heq; subst; try lia.
    iExists num; by iFrame.
  Qed.


End gen_heap.
