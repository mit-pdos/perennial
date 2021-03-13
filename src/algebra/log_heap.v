(* Multi-generational heaps *)
From iris.algebra Require Import auth gmap frac agree functions.

Set Default Proof Using "Type".

Record async T := {
  latest : T;
  pending : list T;
}.

Arguments Build_async {_} _ _.
Arguments latest {_} _.
Arguments pending {_} _.

Definition possible {T} (ab : async T) :=
  pending ab ++ [latest ab].

Definition sync {T} (v : T) : async T :=
  Build_async v nil.

Definition async_put {T} (v : T) (a : async T) :=
  Build_async v (possible a).

Lemma length_possible_pending {T} (a : async T) :
  length (possible a) = S (length (pending a)).
Proof. rewrite /possible last_length //. Qed.
Lemma length_possible_pending' {T} (a : async T) :
  length (possible a) - 1 = length (pending a).
Proof. rewrite /possible last_length. lia. Qed.

Lemma possible_lookup_0 {T} (a: async T) :
  is_Some (possible a !! 0).
Proof. destruct a as [? []]; eauto. Qed.

Lemma lookup_possible_latest {T} (a : async T) :
  possible a !! length (pending a) = Some (latest a).
Proof.
  rewrite /possible.
  rewrite -> lookup_app_r by lia.
  replace (length (pending a) - length (pending a)) with 0 by lia.
  reflexivity.
Qed.
Lemma lookup_possible_latest' {T} (a : async T) :
  possible a !! (length (possible a) - 1) = Some (latest a).
Proof. rewrite length_possible_pending'. apply lookup_possible_latest. Qed.

Lemma possible_async_put {T} (v:T) a :
  possible (async_put v a) = possible a ++ [v].
Proof. rewrite /async_put /possible //. Qed.

Lemma length_possible_async_put {T} (v:T) a :
  length (possible (async_put v a)) = S (length (possible a)).
Proof. rewrite possible_async_put !app_length /=. lia. Qed.

Definition list_to_async {A} `{!Inhabited A} (l: list A) : async A :=
  {| latest := match last l with
               | Some x => x
               | None => inhabitant
               end;
     pending := take (length l - 1)%nat l;
  |}.

Instance rev_inj A : Inj eq eq (@rev A).
Proof.
  intros l1 l2 Heq.
  rewrite -[l1]rev_involutive -[l2]rev_involutive.
  rewrite Heq //.
Qed.

Lemma possible_list_to_async {A} `{!Inhabited A} (l: list A) :
  (0 < length l)%nat →
  possible (list_to_async l) = l.
Proof.
  intros.
  rewrite /possible /list_to_async /=.
  (* this is proof isn't really inductive, but somehow the reverse part of this
  induction is helpful (we're basically doing case analysis on [] vs l ++
  [x]) *)
  induction l using rev_ind.
  - simpl in H; lia.
  - rewrite last_snoc.
    rewrite app_length /=.
    replace (length l + 1 - 1)%nat with (length l) by lia.
    rewrite take_app //.
Qed.

Lemma length_possible {A} (x: async A) :
  length (possible x) = 1 + length x.(pending).
Proof.
  rewrite /possible /=.
  rewrite app_length /=.
  lia.
Qed.

Definition async_take {A} `{!Inhabited A} (n:nat) (l: async A) : async A :=
  list_to_async (take n (possible l)).

Definition async_prefix {A} (l1 l2: async A) :=
  possible l1  `prefix_of` possible l2.

Lemma async_prefix_lookup_0 {A} (l1 l2: async A) :
  async_prefix l1 l2 →
  possible l1 !! 0 = possible l2 !! 0.
 Proof. intros (?&->). destruct l1 as [? []] => //=. Qed.

Lemma async_take_pending_prefix {A} `{!Inhabited A} (n: nat) (l: async A) :
  pending (async_take n l) `prefix_of` pending l.
Proof.
  rewrite /async_take//=/possible.
  destruct l as [latest0 pending0] => //=.
  remember (length _ - 1) as k.
  pose proof (take_length (pending0 ++ [latest0]) n) as Hlen.
  rewrite take_take.
  rewrite min_l; last first.
  { rewrite Heqk.
    lia.
  }
  rewrite app_length /= in Hlen.
  rewrite take_app_le; last by lia.
  rewrite -{2}(firstn_skipn k pending0).
  eexists; eauto.
Qed.

Lemma last_take_drop_prefix {A} `{Hin: Inhabited A} (l : list A) (n: nat) :
  0 < n →
  n ≤ length l →
  [match last (take n l) with
                 | Some x => x
                 | None => inhabitant
                 end] `prefix_of` drop (n - 1) l.
Proof.
  intros.
  assert (∃ a l1 l2, l = l1 ++ a :: l2 /\
                     length l1 = n - 1) as (a&l1&l2&->&Hlen).
  {
    destruct Hin as [inh].
    exists (nth (n -1) l inh).
    edestruct (nth_split (n:=n-1) l inh) as (l1&l2&?&Hlen); first lia.
    exists l1, l2. eauto.
  }
  rewrite drop_app_ge; last lia.
  replace (n - 1 - length l1) with 0 by lia.
  rewrite /=.
  rewrite take_app_ge; last lia.
  replace (n - length l1) with 1 by lia.
  rewrite //= firstn_O.
  rewrite last_snoc. exists l2; eauto.
Qed.

Lemma async_take_possible_prefix {A} `{!Inhabited A} (n: nat) (l: async A) :
  0 < n →
  n <= length (possible l) →
  possible (async_take n l) `prefix_of` possible l.
Proof.
  intros Hnonz Hle.
  rewrite /async_take//=/possible.
  destruct l as [latest0 pending0] => //=.
  remember (length _ - 1) as k.
  pose proof (take_length (pending0 ++ [latest0]) n) as Hlen.
  rewrite app_length /= in Hlen.
  rewrite ?take_take.
  rewrite min_l; last first.
  { rewrite Heqk.
    lia.
  }
  rewrite take_app_le; last by lia.
  rewrite -{3}(firstn_skipn k pending0).
  rewrite -app_assoc.
  apply prefix_app.
  rewrite firstn_length_le in Heqk; eauto.
  subst. rewrite /possible/= in Hle.
  clear Hlen.
  replace (drop (n - 1) pending0 ++ [latest0]) with
      (drop (n- 1) (pending0 ++ [latest0])); last first.
  { rewrite drop_app_le; last first.
    { rewrite app_length/= in Hle. lia. }
    auto.
  }
  eapply last_take_drop_prefix; eauto.
Qed.

Lemma async_take_async_prefix {A} `{!Inhabited A} (n: nat) (l: async A):
  0 < n →
  n <= length (possible l) →
  async_prefix (async_take n l) l.
Proof. intros. apply async_take_possible_prefix; auto. Qed.
