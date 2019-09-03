From iris.algebra Require Import auth agree functions csum.
From Perennial.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Import SemanticsHelpers.
From Perennial Require Export Spec.LockDefs.
Require Import Count_Heap.
Unset Implicit Arguments.

Set Default Proof Using "Type".
Import uPred.
From Classes Require Import EqualDec.
Import EqualDecNotation.

(* TODO: move *)
Ltac inj_pair2 :=
  repeat match goal with
         | [ H: existT ?x ?o1 = existT ?x ?o2 |- _ ] =>
           apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         | [ H: existT ?x _ = existT ?y _ |- _ ] => inversion H; subst
         end.

Definition gen_typed_heapUR A (L: A → Type) (V: A → Type) {Heq: EqualDec (sigT L)}: ucmraT :=
  gen_heapUR (sigT L) (sigT V).

Definition pull_lock {A} {V: A → Type} (v: option (sigT (λ A, LockStatus * V A))%type) :=
   match v with
   | Some (existT T (s, x)) => Some (s, existT T x)
   | None => None
   end.

Definition to_gen_typed_heap {A} {L V : A → Type} {Heq: EqualDec (sigT L)}
           (f: DynMap L (λ T, (LockStatus * V T)%type)) :
  @gen_typed_heapUR A L V _ := to_gen_heap (λ k, pull_lock (dynMap f k)).

(** The CMRA we need. *)
Class gen_typed_heapG {A} (L V : A → Type) (Σ : gFunctors) `{Heq: EqualDec (sigT L)}  :=
{
  gt_inG :> gen_heapG (sigT L) (sigT V) Σ
}.

Definition gen_typed_heapΣ {A} (L V : A → Type) `{Heq: EqualDec (sigT L)} : gFunctors :=
  gen_heapΣ (sigT L) (sigT V).

Instance subG_gen_heapPreG {Σ A} {L V: A → Type} `{Heq: EqualDec (sigT L)}:
  subG (gen_typed_heapΣ L V) Σ → gen_heapPreG (sigT L) (sigT V) Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_typed_heapG A L V Σ}.

  Definition gen_typed_heap_ctx σ : iProp Σ :=
    own (gen_heap_name (gt_inG)) (● (to_gen_typed_heap σ)).
  Definition mapsto {T} (l: L T) (n: Z) (s: LockStatus) (v: V T) :=
    mapsto (existT _ l) n s (existT _ v).
  Definition read_mapsto {T} (l : L T) (s: LockStatus) (v: V T) : iProp Σ :=
    read_mapsto (existT _ l) s (existT _ v).
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

Section to_gen_typed_heap.
  Context {A} (L V : A → Type) `{EqualDec (sigT L)}.
  Implicit Types σ : DynMap L (λ T, (LockStatus * V T)%type).
  (** Conversion to heaps and back *)
  Lemma to_gen_typed_heap_valid σ : ✓ to_gen_typed_heap σ.
  Proof. apply to_gen_heap_valid. Qed.
  Lemma getDyn_to_gen_typed_heap_None {T} σ (l: L T) :
    getDyn σ l = None → to_gen_typed_heap σ (existT _ l) = None.
  Proof.
    rewrite /to_gen_typed_heap => Hget. apply lookup_to_gen_heap_None.
    rewrite /pull_lock getDyn_lookup_none2 //=.
  Qed.

  Lemma to_gen_typed_heap_insert {T} (l: L T) s v σ :
    to_gen_typed_heap (updDyn l (s, v) σ)
    ≡ <[existT _ l:=(Count 0, (to_lock s, to_agree (existT _ v)))]> (to_gen_typed_heap σ).
  Proof.
    rewrite -to_gen_heap_insert/to_gen_typed_heap/to_gen_heap.
    intros k.
    rewrite /updDyn//=.
    rewrite /insert/partial_fn_insert.
    destruct (k == existT T l); subst => //=.
  Qed.
  Lemma to_gen_typed_heap_delete {T} l σ :
    to_gen_typed_heap (deleteDyn l σ) ≡ delete (existT T l) (to_gen_typed_heap σ).
  Proof.
    rewrite -to_gen_heap_delete/to_gen_typed_heap/to_gen_heap.
    intros k.
    rewrite /deleteDyn//=.
    rewrite /delete/partial_fn_delete.
    destruct ((k == existT T l)) => //=.
  Qed.
End to_gen_typed_heap.

Lemma gen_typed_heap_init {A} {L V : A → Type} `{gen_heapPreG (sigT L) (sigT V) Σ} σ :
  (|==> ∃ _ : gen_typed_heapG L V Σ, gen_typed_heap_ctx σ)%I.
Proof.
  iMod (gen_heap_init (λ k, pull_lock (dynMap σ k))) as (Hgen) "?".
  iModIntro. by iExists {| gt_inG := Hgen |}.
Qed.

Lemma gen_typed_heap_strong_init {A} {L V: A → Type} `{H: gen_heapPreG (sigT L) (sigT V) Σ} σ :
  (|==> ∃ (H0 : gen_typed_heapG L V Σ) (Hpf: @gen_heap_inG _ _ _ _ (gt_inG) = gen_heap_preG_inG),
        gen_typed_heap_ctx σ ∗ own (gen_heap_name (gt_inG)) (◯ (to_gen_typed_heap σ)))%I.
Proof.
  iMod (gen_heap_strong_init (λ k, pull_lock (dynMap σ k))) as (Hgen ?) "(?&?)".
  iModIntro. unshelve (iExists {| gt_inG := Hgen |}, _); eauto. iFrame.
Qed.

Section gen_heap.
  Context `{gen_typed_heapG A L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : DynMap L (λ T, (LockStatus * V T)%type).
  Implicit Types h g : gen_typed_heapUR A L V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless {T} (l: L T) q m v : Timeless (mapsto l q m v).
  Proof. apply _. Qed.
  Global Instance read_mapsto_timeless {T} (l: L T) v : Timeless (l r↦ v).
  Proof. apply _. Qed.

  Lemma mapsto_agree_generic {T} (l: L T) (q1 q2: Z) ls1 ls2 v1 v2 :
    mapsto l q1 ls1 v1 -∗ mapsto l q2 ls2 v2 -∗ ⌜ v1 = v2 ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (@mapsto_agree_generic with "H1 H2") as %Heq'. by inj_pair2.
  Qed.

  Lemma mapsto_agree {T} (l: L T) q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (@mapsto_agree with "H1 H2") as %Heq'. by inj_pair2.
  Qed.

  Lemma mapsto_valid {T} (l: L T) q1 q2 v1 v2 :
    (q1 >= 0 → q2 >= 0 → l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ False)%Z.
  Proof. iIntros (??) "H1 H2". by iApply (@mapsto_valid with "H1 H2"). Qed.

  Lemma mapsto_valid' {T} (l: L T) v1 v2: l ↦{0} v1 -∗ l ↦{-1} v2 -∗ False.
  Proof. iIntros "H1 H2". by iApply (@mapsto_valid' with "H1 H2"). Qed.

  Lemma mapsto_valid_generic {T} (l: L T) (q1 q2: Z) ls1 ls2 v1 v2 :
    (q1 >= 0 → q2 >= 0 → mapsto l q1 ls1 v1 -∗ mapsto l q2 ls2 v2 -∗ False)%Z.
  Proof. iIntros (??) "H1 H2". by iApply (@mapsto_valid_generic with "H1 H2"). Qed.

  Lemma read_split_join1 {T} (l: L T) (q: nat) n v :
    mapsto l q (ReadLocked n) v ⊣⊢
           mapsto l (S q) Unlocked v ∗ mapsto l (-1) (ReadLocked n) v.
  Proof. rewrite /mapsto/read_mapsto. apply @read_split_join1. Qed.

  Lemma read_split_join2 {T} (l: L T) (q: nat) n v :
    mapsto l q (ReadLocked n) v ⊣⊢
           mapsto l (S q) (ReadLocked n) v ∗ mapsto l (-1) Unlocked v.
  Proof. rewrite /mapsto/read_mapsto. apply @read_split_join2. Qed.

  Lemma read_split_join3 {T} (l: L T) (q: nat) v :
    mapsto l q Locked v ⊣⊢
           mapsto l (S q) Locked v ∗ mapsto l (-1) Locked v.
  Proof. rewrite /mapsto/read_mapsto. apply @read_split_join3. Qed.

  Lemma read_split_join {T} (l: L T) (q: nat) v : l ↦{q} v ⊣⊢ (l ↦{S q} v ∗ l r↦ v).
  Proof. rewrite /mapsto/read_mapsto. apply @read_split_join. Qed.

  Lemma pull_lock_getDyn {T} σ l (s: LockStatus) v:
    pull_lock (σ.(dynMap) (existT T l)) = Some (s, existT T v) →
    getDyn σ l = Some (s, v).
  Proof.
    rewrite /pull_lock => Heq'.
    eapply (getDyn_lookup1 σ).
    destruct (dynMap) as [(?&(?&?))|] => //=. inversion Heq'.
    subst. by inj_pair2.
  Qed.

  Lemma gen_typed_heap_alloc T σ (l: L T) v :
    getDyn σ l = None → gen_typed_heap_ctx σ
      ==∗ gen_typed_heap_ctx (updDyn l (Unlocked, v) σ) ∗ l ↦ v.
  Proof.
    iIntros (Hnone) "Hσ".
    iMod (@gen_heap_alloc _ _ _ _ _ _ (existT _ l) (existT _ v) with "Hσ") as "(H&$)".
    { rewrite /= getDyn_lookup_none2 //=. }
    iModIntro. iApply (@gen_heap_ctx_proper with "H") => k.
    rewrite /insert/partial_fn_insert/updDyn//=.
    destruct equal => //=.
  Qed.

  Lemma gen_typed_heap_dealloc T σ (l: L T) v :
    gen_typed_heap_ctx σ -∗ l ↦ v ==∗ gen_typed_heap_ctx (deleteDyn l σ).
  Proof.
    iIntros "Hσ Hl".
    iMod (@gen_heap_dealloc _ _ _ _ _ _ (existT _ l) with "Hσ Hl") as "H".
    iModIntro. iApply (@gen_heap_ctx_proper with "H") => k.
    rewrite /delete/partial_fn_delete/deleteDyn//=.
    destruct equal => //=.
  Qed.

  Lemma gen_typed_heap_valid1 T σ (l: L T) s v :
    gen_typed_heap_ctx σ -∗ mapsto l 0 s v -∗ ⌜getDyn σ l = Some (s, v)⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct (@gen_heap_valid1 with "Hσ Hl") as %Heq'.
    eauto using pull_lock_getDyn.
  Qed.

  Lemma gen_typed_heap_valid2 T σ (l: L T) z s v :
    gen_typed_heap_ctx σ -∗ mapsto l z s v -∗
    ⌜ ∃ s' : LockStatus, getDyn σ l = Some (s', v) ∧ to_lock s ≼ to_lock s' ⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct (@gen_heap_valid2 with "Hσ Hl") as %[s' [Heq' ?]].
    iPureIntro. exists s'; split; auto.
    eauto using pull_lock_getDyn.
  Qed.


  Lemma gen_typed_heap_valid T σ (l: L T) q v :
    gen_typed_heap_ctx σ -∗ l ↦{q} v -∗ ⌜∃ s, getDyn σ l = Some (s, v) ∧ s ≠ Locked ⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct (@gen_heap_valid with "Hσ Hl") as %[s' [Heq' ?]].
    iPureIntro. exists s'; split; auto.
    eauto using pull_lock_getDyn.
  Qed.

  Lemma gen_typed_heap_update T σ (l: L T) s1 s2 (v1 v2: V T) :
    gen_typed_heap_ctx σ -∗ mapsto l 0 s1 v1 ==∗
      gen_typed_heap_ctx (updDyn l (s2, v2) σ) ∗ mapsto l 0 s2 v2.
  Proof.
    iIntros "Hσ Hl". iMod (@gen_heap_update with "Hσ Hl") as "(Hσ&$)".
    iModIntro. iApply (@gen_heap_ctx_proper with "Hσ") => k.
    rewrite /insert/partial_fn_insert/updDyn//=.
    destruct equal => //=.
  Qed.

  Lemma gen_typed_heap_readlock T σ (l: L T) q v :
    gen_typed_heap_ctx σ -∗ mapsto l q Unlocked v ==∗ ∃ s, ⌜ getDyn σ l = Some (s, v) ⌝ ∗
                 gen_typed_heap_ctx (updDyn l (force_read_lock s, v) σ)
                 ∗ mapsto l q (ReadLocked 0) v.
  Proof.
    iIntros "Hσ Hl". iMod (@gen_heap_readlock with "Hσ Hl") as (s Heq') "(Hσ&$)".
    iModIntro. iExists s. iSplitL "".
    { eauto using pull_lock_getDyn. }
    iApply (@gen_heap_ctx_proper with "Hσ") => k.
    rewrite /insert/partial_fn_insert/updDyn//=.
    destruct equal => //=.
  Qed.

  Lemma gen_typed_heap_readlock' T σ (l: L T) q v n :
    gen_typed_heap_ctx σ -∗ mapsto l q (ReadLocked n) v ==∗ ∃ s, ⌜ getDyn σ l = Some (s, v) ⌝ ∗
                 gen_typed_heap_ctx (updDyn l (force_read_lock s,v) σ)
                 ∗ mapsto l q (ReadLocked (S n)) v.
  Proof.
    iIntros "Hσ Hl". iMod (@gen_heap_readlock' with "Hσ Hl") as (s Heq') "(Hσ&$)".
    iModIntro. iExists s. iSplitL "".
    { eauto using pull_lock_getDyn. }
    iApply (@gen_heap_ctx_proper with "Hσ") => k.
    rewrite /insert/partial_fn_insert/updDyn//=.
    destruct equal => //=.
  Qed.

  Lemma gen_typed_heap_readunlock T σ (l: L T) q n1 v :
    gen_typed_heap_ctx σ -∗ mapsto l q (ReadLocked n1) v ==∗
      ∃ n, ⌜ getDyn σ l = Some (ReadLocked n, v) ⌝ ∗
                               gen_typed_heap_ctx (updDyn l (force_read_unlock (ReadLocked n),v) σ)
                               ∗ mapsto l q (force_read_unlock (ReadLocked n1)) v.
  Proof.
    iIntros "Hσ Hl". iMod (@gen_heap_readunlock with "Hσ Hl") as (s Heq') "(Hσ&$)".
    iModIntro. iExists s. iSplitL "".
    { eauto using pull_lock_getDyn. }
    iApply (@gen_heap_ctx_proper with "Hσ") => k.
    rewrite /insert/partial_fn_insert/updDyn//=.
    destruct equal => //=.
  Qed.

End gen_heap.
