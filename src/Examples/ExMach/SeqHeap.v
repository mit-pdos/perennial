(* Multi-generational heaps *)
From iris.algebra Require Import auth gmap frac agree functions.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own invariants.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition seq_heapUR (L V : Type) `{Countable L}: ucmraT :=
  ofe_funUR (fun (_ : nat) => (gen_heapUR L V)).

Class seq_heapG (L V: Type) (Σ : gFunctors) `{Countable L} := SeqHeapG {
  seq_heap_inG :> inG Σ (authR (seq_heapUR L V));
  seq_heap_name : gname
}.

Definition to_seq_heap {L V} `{Countable L} (f: nat → gmap L V) : seq_heapUR L V :=
  λ n, to_gen_heap (f n).

Arguments seq_heap_name {_ _ _ _ _} _ : assert.

Class seq_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} :=
  { seq_heap_preG_inG :> inG Σ (authR (seq_heapUR L V)) }.

Definition seq_heapΣ (L V : Type) `{Countable L} : gFunctors :=
  #[GFunctor (authR (seq_heapUR L V))].

Instance subG_seq_heapPreG {Σ L V} `{Countable L} :
  subG (seq_heapΣ L V) Σ → seq_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : seq_heapG L V Σ}.

  Definition seq_heap_ctx (σs : nat → gmap L V) : iProp Σ :=
    own (seq_heap_name hG) (● (to_seq_heap σs)).

  Definition mapsto_fun_def (l : L) (q : Qp) (vs: nat → option V) : iProp Σ :=
    own (seq_heap_name hG)
        (◯ (fun n =>
              match vs n with
              | Some v => {[ l := (q, to_agree (v : leibnizC V)) ]}
              | None => ε
              end)).

  Definition mapsto_fun_aux : seal (@mapsto_fun_def). by eexists. Qed.
  Definition mapsto_fun := mapsto_fun_aux.(unseal).
  Definition mapsto_fun_eq : @mapsto_fun = @mapsto_fun_def := mapsto_fun_aux.(seal_eq).

  Definition mapsto_gt (n: nat) (l: L) (q: Qp) (v: V) : iProp Σ :=
    (∃ vs, ⌜ vs n = Some v ∧ (∀ n', n' < n → vs n' = None) ∧ (∀ n', n' > n → is_Some (vs n')) ⌝
          ∗ mapsto_fun l q vs)%I.

End definitions.

Local Notation "l ↦{ q } vs @ ⊤" := (mapsto_fun l q vs)
  (at level 20, q at level 50, format "l  ↦{ q }  vs @ ⊤") : bi_scope.
Local Notation "l ↦ vs @ ⊤" := (mapsto_fun l 1 vs) (at level 20) : bi_scope.

Local Notation "l ↦{ q } - @ ⊤" := (∃ vs, l ↦{q} vs @ ⊤)%I
  (at level 20, q at level 50, format "l  ↦{ q } - @ ⊤") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} - @ ⊤)%I (at level 20) : bi_scope.


Local Notation "l ↦{ q } v @ k" := (mapsto_gt k l q v)
  (at level 20, q at level 50, format "l  ↦{ q } v @ k") : bi_scope.
Local Notation "l ↦ v @ k" := (mapsto_gt k l 1 v) (at level 20) : bi_scope.

Section to_seq_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σs : nat → gmap L V.
  Implicit Types σ : gmap L V.

  (** Conversion to heaps and back *)
  Lemma to_seq_heap_valid σs : ✓ to_seq_heap σs.
  Proof. intros k l. rewrite lookup_fmap. by case (σs k !! l). Qed.
  Lemma lookup_to_seq_heap_None σs k l : σs k !! l = None → to_seq_heap σs k !! l = None.
  Proof. by rewrite /to_seq_heap lookup_fmap=> ->. Qed.
  Lemma seq_heap_singleton_included σs l q vs :
    ((fun n => match vs n with
              | Some v => {[ l := (q, to_agree (v : leibnizC V)) ]}
              | None => ε
              end) : seq_heapUR L V) ≼ to_seq_heap σs →
    (∀ k v, vs k = Some v → σs k !! l = Some v).
  Proof.
    intros Hincl k v Hsubst. apply (ofe_fun_included_spec_1 _ _ k) in Hincl.
    move: Hincl. rewrite Hsubst singleton_included=> -[[q' av] []].
    rewrite /to_seq_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
  Lemma seq_heap_singleton_included' σs k l q v :
    ofe_fun_singleton k {[l := (q, to_agree v)]} ≼ to_seq_heap σs → σs k !! l = Some v.
  Proof.
    intros Hincl. apply (ofe_fun_included_spec_1 _ _ k) in Hincl.
    rewrite ofe_fun_lookup_singleton in Hincl.
    move: Hincl. rewrite singleton_included=> -[[q' av] []].
    rewrite /to_seq_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
  Lemma to_seq_heap_insert (l: L) vs σs :
    to_seq_heap (fun n => <[l:=vs n]> (σs n)) ≡
    fun n => <[l:=(1%Qp, to_agree (vs n:leibnizC V))]> (to_gen_heap (σs n)).
  Proof.  rewrite /to_seq_heap => k. rewrite to_gen_heap_insert. done. Qed.
  Lemma to_seq_heap_insert_maybe (l: L) vs σs :
    to_seq_heap (fun n =>
                   match vs n with
                   | Some v => <[l:=v]> (σs n)
                   | None => (σs n)
                   end) ≡
    (fun n =>
       match vs n with
       | Some v => <[l:=(1%Qp, to_agree (v:leibnizC V))]> (to_gen_heap (σs n))
       | None => to_gen_heap (σs n)
       end).
  Proof.
    rewrite /to_seq_heap => k. destruct (vs k); auto.
    rewrite to_gen_heap_insert. done.
  Qed.
End to_seq_heap.

Lemma seq_heap_init `{seq_heapPreG L V Σ} σs :
  (|==> ∃ _ : seq_heapG L V Σ, seq_heap_ctx σs)%I.
Proof.
  iMod (own_alloc (● to_seq_heap σs)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_seq_heap_valid. }
  iModIntro. by iExists (SeqHeapG L V Σ _ _ _ γ).
Qed.

Lemma seq_heap_strong_init `{seq_heapPreG L V Σ} σs :
  (|==> ∃ _ : seq_heapG L V Σ, seq_heap_ctx σs ∗
    own (seq_heap_name _) (◯ (to_seq_heap σs)))%I.
Proof.
  iMod (own_alloc (● to_seq_heap σs ⋅ ◯ to_seq_heap σs)) as (γ) "(?&?)".
  { apply auth_valid_discrete_2; split; auto. exact: to_seq_heap_valid. }
  iModIntro. iExists (SeqHeapG L V Σ _ _ _ γ). iFrame.
Qed.

Section seq_heap.
  Context `{seq_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types σs : nat → gmap L V.
  Implicit Types h g : seq_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_fun_timeless l q vs : Timeless (l ↦{q} vs @ ⊤).
  Proof. rewrite mapsto_fun_eq /mapsto_def. apply _. Qed.
  (*
  Global Instance mapsto_fractional l vs : Fractional (λ q, l ↦{q} vs @ ⊤)%I.
  Proof.
    intros p q. rewrite mapsto_fun_eq /mapsto_fun_def -own_op -auth_frag_op.
      op_singleton pair_op agree_idemp.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.
   *)

  Lemma mapsto_fun_agree l q1 q2 vs1 vs2 : l ↦{q1} vs1 @ ⊤ -∗ l ↦{q2} vs2 @ ⊤ -∗
                                             ⌜∀ x z1 z2, vs1 x = Some z1 →
                                                         vs2 x = Some z2 →
                                                         z1 = z2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_fun_eq /mapsto_fun_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. intros Hval n ?? Heq1 Heq2.
    specialize (Hval n).
    rewrite ofe_fun_lookup_op Heq1 Heq2 op_singleton singleton_valid pair_op in Hval *.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_fun_split l q vs vs1 vs2 :
    (∀ i, is_Some (vs1 i) → ¬ is_Some (vs2 i)) →
    (∀ i, is_Some (vs2 i) → ¬ is_Some (vs1 i)) →
    (∀ i v, vs i = Some v ↔ (vs1 i = Some v ∨ vs2 i = Some v)) →
    (l ↦{q} vs @ ⊤ -∗ l ↦{q} vs1 @ ⊤ ∗ l ↦{q} vs2 @ ⊤).
  Proof.
    intros Hnon_overlap1 Hnon_overlap2 Hlookup.
    rewrite mapsto_fun_eq /mapsto_fun_def -own_op -auth_frag_op.
    apply own_mono.
    unshelve (apply: auth_frag_mono).
    exists ε. rewrite right_id.
    intros i. rewrite ofe_fun_lookup_op.
    specialize (Hlookup i).
    specialize (Hnon_overlap1 i).
    specialize (Hnon_overlap2 i).
    destruct (vs i) as [v|].
    - edestruct (Hlookup v) as ([Heq|Heq]&?); first by reflexivity.
      * rewrite Heq.
        assert (vs2 i = None) as ->.
        { apply eq_None_not_Some; eauto. }
        by rewrite right_id.
      * rewrite Heq.
        assert (vs1 i = None) as ->.
        { apply eq_None_not_Some; eauto. }
        by rewrite left_id.
    - destruct (vs1 i) as [v|].
      { edestruct (Hlookup v) as (_&Hfalse).
        exfalso. feed pose proof Hfalse; eauto. congruence. }
      destruct (vs2 i) as [v|].
      { edestruct (Hlookup v) as (_&Hfalse).
        exfalso. feed pose proof Hfalse; eauto. congruence. }
      by rewrite right_id.
  Qed.

  Lemma mapsto_fun_weaken l q vs1 vs2 k:
    (∀ i, vs2 i = if nat_eq_dec i k then None else vs1 i) →
    (l ↦{q} vs1 @ ⊤ -∗ l ↦{q} vs2 @ ⊤).
  Proof.
    intros Hlookup.
    rewrite (mapsto_fun_split l q vs1 (fun i => if nat_eq_dec i k then vs1 k else None)
                              vs2).
    { iIntros "(_&?)". done. }
    { intros i. rewrite Hlookup. destruct nat_eq_dec => //=. intros []%is_Some_None. }
    { intros i. rewrite Hlookup. destruct nat_eq_dec => //=. intros []%is_Some_None. }
    { intros i v. rewrite Hlookup. destruct nat_eq_dec => //=; subst;
      split; intuition; congruence.  }
  Qed.

  (*
  Global Instance ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (mapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance ex_mapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_valid l q v : l ↦{q} v -∗ ✓ q.
  Proof.
    rewrite mapsto_eq /mapsto_def own_valid !discrete_valid.
    by apply pure_mono=> /auth_own_valid /singleton_valid [??].
  Qed.
  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.
   *)

  (*
  Lemma seq_heap_alloc k σ l vs :
    σ !! l = None → gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, to_agree (v:leibnizC _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iModIntro. rewrite to_gen_heap_insert. iFrame.
  Qed.

  Lemma gen_heap_dealloc σ l v :
    gen_heap_ctx σ -∗ l ↦ v ==∗ gen_heap_ctx (delete l σ).
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    rewrite to_gen_heap_delete. iApply (own_update_2 with "Hσ Hl").
    eapply auth_update_dealloc, (delete_singleton_local_update _ _ _).
  Qed.
   *)

  Lemma seq_heap_valid σs l q vs :
    seq_heap_ctx σs -∗ l ↦{q} vs @ ⊤ -∗ ⌜∀ k v, vs k = Some v → (σs k) !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /seq_heap_ctx /mapsto mapsto_fun_eq /mapsto_fun_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %Hval.
    apply auth_valid_discrete_2 in Hval as [Hl _].
    simpl in Hl. iPureIntro; intros. eapply seq_heap_singleton_included in Hl; eauto.
  Qed.

  Lemma seq_heap_valid_gt σs l q v k : seq_heap_ctx σs -∗ l ↦{q} v @ k -∗ ⌜(σs k) !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct "Hl" as (f) "(%&H)".
    iDestruct (seq_heap_valid with "Hσ H") as %Hpure.
    iPureIntro; intuition.
  Qed.

  Lemma ofe_fun_local_update `{EqDecision A} {B: A → ucmraT} f1 f2 f1' f2' :
    (∀ x, (f1 x, f2 x) ~l~> (f1' x , f2' x)) →
    (f1 : ofe_fun B, f2) ~l~> (f1', f2').
  Proof.
    intros. 
    apply local_update_unital=> n mf Hmv Hm; simpl in *.
    split.
    - intros k. specialize (H1 k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (H1 n (Some (mf k))); eauto.
    - intros k. specialize (H1 k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (H1 n (Some (mf k))); eauto.
  Qed.

  Lemma seq_heap_update σs l (vs1 : nat → option V) (vs2: nat → option V) :
    (∀ k, is_Some (vs1 k) ↔ is_Some (vs2 k)) →
    seq_heap_ctx σs -∗ (l ↦ vs1 @ ⊤) ==∗
                 seq_heap_ctx (λ n, match vs2 n with | None => σs n | Some v => <[l:=v]>(σs n) end)
                 ∗ l ↦ vs2 @ ⊤.
  Proof.
    iIntros (Hnone) "Hσ Hl". rewrite /seq_heap_ctx mapsto_fun_eq /mapsto_fun_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %Hval.
    apply auth_valid_discrete_2 in Hval as [Hl _].
    iMod (own_update_2 _ _ _
                       (● to_seq_heap (λ n, match vs2 n with
                                            | None => σs n
                                            | Some v => <[l:=v]>(σs n)
                                            end) ⋅
                       (◯ (λ n : nat, match vs2 n with
                                      | Some v => {[l := (1%Qp, to_agree v)]}
                                      | None => ε
                                      end)))
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      specialize (Hnone k) as (Hs1&Hs2). rewrite /to_seq_heap. rewrite /to_seq_heap in Hl.
      apply (ofe_fun_included_spec_1 _ _ k) in Hl. simpl in Hl.
      destruct (vs1 k); destruct (vs2 k);
        try (exfalso; eapply is_Some_None; eauto; fail).
      - apply gen_heap_singleton_included in Hl. 
        rewrite /to_gen_heap fmap_insert //=.
        rewrite -/to_gen_heap.
        eapply (singleton_local_update (to_gen_heap (σs k)) l),
        (exclusive_local_update _ (1%Qp, to_agree (_:leibnizC _)))=> //.
          by rewrite /to_gen_heap lookup_fmap Hl.
      - reflexivity.
    }
    iModIntro. iFrame.
  Qed.

  Lemma seq_heap_update_gt σs l v1 vs2 v2 k :
    vs2 k = Some v2 →
    (∀ n, n < k → vs2 n = None) →
    (∀ n, n > k → is_Some (vs2 n)) →
    seq_heap_ctx σs -∗ l ↦ v1 @ k ==∗
                 seq_heap_ctx (λ n, match vs2 n with | None => σs n | Some v => <[l:=v]>(σs n) end)
                 ∗ l ↦ v2 @ k.
  Proof.
    iIntros (Hvs2k Hvs2lt Hvs2gt) "Hσ Hl".
    iDestruct "Hl" as (vs1) "(Hp&Hl)".
    iDestruct "Hp" as %[Hvs1k [Hvs1lt Hvs1gt]].
    iMod (seq_heap_update _ _ vs1 vs2 with "Hσ Hl") as "(Hσ&Hl)".
    { intros k'. destruct (Nat.lt_trichotomy k' k) as [|[ |]].
      - rewrite Hvs1lt // Hvs2lt //=.
      - subst. rewrite Hvs1k // Hvs2k //=. clear. firstorder.
      - split; intros; eauto.
    }
    iModIntro; iFrame. iExists vs2; iFrame.
    iPureIntro. split_and!; eauto.
  Qed.
End seq_heap.