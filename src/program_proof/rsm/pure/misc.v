From iris.proofmode Require Import proofmode.

Lemma set_Forall_Forall_subsume `{Countable A} (l : list A) (s : gset A) P :
  set_Forall P s ->
  Forall (λ x, x ∈ s) l ->
  Forall P l.
Proof. do 2 rewrite Forall_forall. intros HP Hl x Hin. by auto. Qed.

Lemma gset_to_gmap_same_union `{Countable K} {A} (X Y : gset K) (x : A) :
  gset_to_gmap x (X ∪ Y) = gset_to_gmap x X ∪ gset_to_gmap x Y.
Proof.
  apply map_eq.
  intros i.
  rewrite lookup_union 3!lookup_gset_to_gmap.
  destruct (decide (i ∈ X)) as [Hinx | Hnotinx].
  { rewrite option_guard_True.
    { rewrite option_guard_True; last done.
      by rewrite union_Some_l.
    }
    set_solver.
  }
  rewrite (option_guard_False (i ∈ X)); last done.
  rewrite option_union_left_id.
  destruct (decide (i ∈ Y)) as [Hiny | Hnotiny].
  { rewrite option_guard_True.
    { by rewrite option_guard_True. }
    set_solver.
  }
  { rewrite option_guard_False.
    { by rewrite option_guard_False. }
    set_solver.
  }
Qed.
