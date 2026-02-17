From New.ghost Require Export all.

(** * Properties about ghost ownership *)
Section global.
Context `{!allG Σ} `{!IsCmra (iProp Σ) A e}.
Implicit Types a : A.

(** ** Properties of [own] *)
(* Global Instance own_ne γ : NonExpansive (@own Σ A _ γ). *)
(* Proof. rewrite !own_eq. solve_proper. Qed. *)
Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (own (A:=A) γ) := ne_proper _.

(* Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2. *)
(* Proof. by rewrite !own_eq /own_def -ownM_op iRes_singleton_op. Qed. *)
Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (own (A:=A) γ).
Proof. intros a1 a2. apply own_mono. Qed.

(* Lemma own_valid γ a : own γ a ⊢ ✓ a. *)
(* Proof. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed. *)
Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.

(* Global Instance own_timeless γ a : Discrete a → Timeless (own γ a). *)
(* Proof. rewrite !own_eq /own_def. apply _. Qed. *)
(* Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a). *)
(* Proof. rewrite !own_eq /own_def; apply _. Qed. *)

(* Lemma later_own γ a : ▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b). *)
(* Proof. *)
(*   rewrite own_eq /own_def later_ownM. apply exist_elim=> r. *)
(*   assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)). *)
(*   { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). } *)
(*   rewrite internal_eq_sym later_internal_eq_iRes_singleton. *)
(*   rewrite (except_0_intro (uPred_ownM r)) -except_0_and. f_equiv. *)
(*   rewrite and_exist_l. f_equiv=> b. rewrite and_exist_l. apply exist_elim=> r'. *)
(*   rewrite assoc. apply and_mono_l. *)
(*   etrans; [|apply ownM_mono, (cmra_included_l _ r')]. *)
(*   eapply (internal_eq_rewrite' _ _ uPred_ownM _); [apply and_elim_r|]. *)
(*   apply and_elim_l. *)
(* Qed. *)

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
(* Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) : *)
(*   pred_infinite P → *)
(*   (∀ γ, P γ → ✓ (f γ)) → *)
(*   ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ). *)
(* Proof. *)
(*   intros HPinf Hf. *)
(*   rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I). *)
(*   - rewrite /bi_emp_valid (ownM_unit emp). *)
(*     apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ, *)
(*       m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ)); *)
(*       [|naive_solver]. *)
(*     apply (alloc_updateP_strong_dep _ P _ (λ γ, *)
(*       inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver]. *)
(*     intros γ _ ?. *)
(*     by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf. *)
(*   - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]]. *)
(*     by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id. *)
(* Qed. *)
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
(* Lemma own_updateP P γ a : a ~~>: P → own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a'. *)
(* Proof. *)
(*   intros Hupd. rewrite !own_eq. *)
(*   rewrite -(bupd_mono (∃ m, *)
(*     ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I). *)
(*   - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x, *)
(*       m = {[ γ := x ]} ∧ ∃ x', *)
(*       x = inG_unfold x' ∧ ∃ a', *)
(*       x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver]. *)
(*     apply singleton_updateP', (iso_cmra_updateP' inG_fold). *)
(*     { apply inG_unfold_fold. } *)
(*     { apply (cmra_morphism_op _). } *)
(*     { apply inG_unfold_validN. } *)
(*     by apply cmra_transport_updateP'. *)
(*   - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]]. *)
(*     rewrite -(exist_intro a'). rewrite -persistent_and_sep. *)
(*     by apply and_intro; [apply pure_intro|]. *)
(* Qed. *)

Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
Proof.
  intros. iIntros "?".
  iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
  { by apply cmra_update_updateP. }
  done.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. apply entails_wand. do 2 apply wand_intro_r. rewrite -!own_op. by iApply own_update. Qed.
End global.

Global Arguments own_valid {_ _} [_] {_ _} _ _.
Global Arguments own_valid_2 {_ _} [_] {_ _} _ _ _.
Global Arguments own_valid_3 {_ _} [_] {_ _} _ _ _ _.
Global Arguments own_valid_l {_ _} [_] {_ _} _ _.
Global Arguments own_valid_r {_ _} [_] {_ _} _ _.
Global Arguments own_updateP {_ _} [_] {_ _} _ _ _ _.
Global Arguments own_update {_ _} [_] {_ _} _ _ _ _.
Global Arguments own_update_2 {_ _} [_] {_ _} _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] {_ _} _ _ _ _ _ _.

(* Lemma own_unit A `{i : !inG Σ (A:ucmra)} γ : ⊢ |==> own γ (ε:A). *)
(* Proof. *)
(*   rewrite /bi_emp_valid (ownM_unit emp) !own_eq /own_def. *)
(*   apply bupd_ownM_update, discrete_fun_singleton_update_empty. *)
(*   apply (alloc_unit_singleton_update (inG_unfold (cmra_transport inG_prf ε))). *)
(*   - apply (cmra_morphism_valid _), cmra_transport_valid, ucmra_unit_valid. *)
(*   - intros x. rewrite -(inG_unfold_fold x) -(cmra_morphism_op inG_unfold). *)
(*     f_equiv. generalize (inG_fold x)=> x'. *)
(*     destruct inG_prf=> /=. by rewrite left_id. *)
(*   - done. *)
(* Qed. *)

(** Big op class instances *)
Section big_op_instances.
  Context {A : ucmra} `{!allG Σ} `{!IsCmra (iProp Σ) A e}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!allG Σ} {A e} {HC : IsCmra (iProp Σ) A e}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (own γ b1) (own γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

(* Section own_forall. *)
(*   Context {A : ucmra} `{!allG Σ} `{!Is (iProp Σ) A e}. *)
(*   Implicit Types a c : A. *)
(*   Implicit Types x z : iResUR Σ. *)

(*   (** Our main goal in this section is to prove [own_forall]: *)

(*     (∀ b, own γ (f b)) ⊢ ∃ c : A, own γ c ∗ (∀ b, Some (f b) ≼ Some c) *)

(*   We have the analogue in the global ucmra, from [ownM_forall]: *)

(*     (∀ a, uPred_ownM (f a)) ⊢ ∃ z : iRes Σ, uPred_ownM z ∧ (∀ a, f a ≼ z) *)

(*   We need to relate [uPred_ownM (iRes_singleton γ _)] to [own γ _] so that we *)
(*   can bring this theorem from the global ucmra world to the [A] world. *)
(*   In particular, [ownM_forall] gives us some [z] in the ucmra world, but to prove *)
(*   the theorem in the end, we need to supply a witness [z'] in the [A] world. *)
(*   We start by defining the [iRes_project] function to map from the ucmra world *)
(*   to the [A] world, basically an inverse of [iRes_singleton]: *) *)

(*   Local Definition iRes_project (γ : gname) (x : iResUR Σ) : option A := *)
(*     cmra_transport (eq_sym inG_prf) ∘ inG_fold <$> x (inG_id i) !! γ. *)

(*   (* Now we prove some properties about [iRes_project] *) *)
(*   Local Lemma iRes_project_op γ x y : *)
(*     iRes_project γ (x ⋅ y) ≡@{option A} iRes_project γ x ⋅ iRes_project γ y. *)
(*   Proof. *)
(*     rewrite /iRes_project lookup_op. *)
(*     case: (x (inG_id i) !! γ)=> [x1|]; case: (y (inG_id i) !! γ)=> [y1|] //=. *)
(*     rewrite -Some_op -cmra_transport_op. do 2 f_equiv. apply: cmra_morphism_op. *)
(*   Qed. *)

(*   Local Instance iRes_project_ne γ : NonExpansive (iRes_project γ). *)
(*   Proof. intros n x1 x2 Hx. rewrite /iRes_project. do 2 f_equiv. apply Hx. Qed. *)

(*   Local Lemma iRes_project_singleton γ a : *)
(*     iRes_project γ (iRes_singleton γ a) ≡ Some a. *)
(*   Proof. *)
(*     rewrite /iRes_project /iRes_singleton discrete_fun_lookup_singleton. *)
(*     rewrite lookup_singleton_eq /= inG_fold_unfold. *)
(*     by rewrite cmra_transport_trans eq_trans_sym_inv_r. *)
(*   Qed. *)

(*   (** The singleton result [c] of [iRes_project γ z] is below [z] *) *)
(*   Local Lemma iRes_project_below γ z c : *)
(*     iRes_project γ z = Some c → iRes_singleton γ c ≼ z. *)
(*   Proof. *)
(*     rewrite /iRes_project /iRes_singleton fmap_Some. *)
(*     intros (a' & Hγ & ->). rewrite cmra_transport_trans eq_trans_sym_inv_l /=. *)
(*     exists (discrete_fun_insert (inG_id i) (delete γ (z (inG_id i))) z). *)
(*     intros j. rewrite discrete_fun_lookup_op. *)
(*     destruct (decide (j = inG_id i)) as [->|]; last first. *)
(*     { rewrite discrete_fun_lookup_singleton_ne //. *)
(*       rewrite discrete_fun_lookup_insert_ne //. by rewrite left_id. } *)
(*     rewrite discrete_fun_lookup_singleton discrete_fun_lookup_insert. *)
(*     intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|]. *)
(*     - by rewrite lookup_singleton_eq lookup_delete_eq Hγ inG_unfold_fold. *)
(*     - by rewrite lookup_singleton_ne // lookup_delete_ne // left_id. *)
(*   Qed. *)

(*   (** If another singleton [c] is below [z], [iRes_project] is above [c]. *) *)
(*   Local Lemma iRes_project_above γ z c : *)
(*     iRes_singleton γ c ≼ z ⊢@{iProp Σ} Some c ≼ iRes_project γ z. *)
(*   Proof. *)
(*     iIntros "#[%x Hincl]". iExists (iRes_project γ x). *)
(*     rewrite -(iRes_project_singleton γ) -iRes_project_op. *)
(*     by iRewrite "Hincl". *)
(*   Qed. *)

(*   (** Finally we tie it all together. *)
(*   As usual, we use [Some a ≼ Some c] for the reflexive closure of [a ≼ c]. *) *)
(*   Lemma own_forall `{!Inhabited B} γ (f : B → A) : *)
(*     (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, Some (f b) ≼ Some c). *)
(*   Proof. *)
(*     rewrite own_eq /own_def. iIntros "Hown". *)
(*     iDestruct (ownM_forall with "Hown") as (z) "[Hown Hincl]". *)
(*     destruct (iRes_project γ z) as [c|] eqn:Hc. *)
(*     - iExists c. iSplitL "Hown". *)
(*       { iApply (ownM_mono with "Hown"). by apply iRes_project_below. } *)
(*       iIntros (b). rewrite -Hc. by iApply iRes_project_above. *)
(*     - iDestruct ("Hincl" $! inhabitant) as "Hincl". *)
(*       iDestruct (iRes_project_above with "Hincl") as "Hincl". *)
(*       rewrite Hc. iDestruct "Hincl" as (mx) "H". *)
(*       rewrite option_equivI. by destruct mx. *)
(*   Qed. *)

(*   (** Now some corollaries. *) *)
(*   Lemma own_forall_total `{!CmraTotal A, !Inhabited B} γ (f : B → A) : *)
(*     (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, f b ≼ c). *)
(*   Proof. setoid_rewrite <-Some_included_totalI. apply own_forall. Qed. *)

(*   Lemma own_and γ a1 a2 : *)
(*     own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ Some a1 ≼ Some c ∗ Some a2 ≼ Some c. *)
(*   Proof. *)
(*     iIntros "Hown". iDestruct (own_forall γ (λ b, if b : bool then a1 else a2) *)
(*       with "[Hown]") as (c) "[$ Hincl]". *)
(*     { rewrite and_alt. *)
(*       iIntros ([]); [iApply ("Hown" $! true)|iApply ("Hown" $! false)]. } *)
(*     iSplit; [iApply ("Hincl" $! true)|iApply ("Hincl" $! false)]. *)
(*   Qed. *)
(*   Lemma own_and_total `{!CmraTotal A} γ a1 a2 : *)
(*     own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ a1 ≼ c ∗ a2 ≼ c. *)
(*   Proof. setoid_rewrite <-Some_included_totalI. apply own_and. Qed. *)

(*   (** A version of [own_forall] for bounded quantification. Here [φ : B → Prop] *)
(*   is a pure predicate that restricts the elements of [B]. *) *)
(*   Lemma own_forall_pred {B} γ (φ : B → Prop) (f : B → A) : *)
(*     (∃ b, φ b) → (* [φ] is non-empty *) *)
(*     (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢ *)
(*     ∃ c, own γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ Some (f b) ≼ Some c). *)
(*   Proof. *)
(*     iIntros ([b0 pb0]) "Hown". *)
(*     iAssert (∀ b : { b | φ b }, own γ (f (`b)))%I with "[Hown]" as "Hown". *)
(*     { iIntros ([b pb]). by iApply ("Hown" $! b). } *)
(*     iDestruct (@own_forall _ with "Hown") as (c) "[$ Hincl]". *)
(*     { split. apply (b0 ↾ pb0). } *)
(*     iIntros (b pb). iApply ("Hincl" $! (b ↾ pb)). *)
(*   Qed. *)
(*   Lemma own_forall_pred_total `{!CmraTotal A} {B} γ (φ : B → Prop) (f : B → A) : *)
(*     (∃ b, φ b) → *)
(*     (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ f b ≼ c). *)
(*   Proof. setoid_rewrite <-Some_included_totalI. apply own_forall_pred. Qed. *)

(*   Lemma own_and_discrete_total `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 c : *)
(*     (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') → *)
(*     own γ a1 ∧ own γ a2 ⊢ own γ c. *)
(*   Proof. *)
(*     iIntros (Hvalid) "Hown". *)
(*     iDestruct (own_and_total with "Hown") as (c') "[Hown [%Ha1 %Ha2]]". *)
(*     iDestruct (own_valid with "Hown") as %?. *)
(*     iApply (own_mono with "Hown"); eauto. *)
(*   Qed. *)
(*   Lemma own_and_discrete_total_False `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 : *)
(*     (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) → *)
(*     own γ a1 ∧ own γ a2 ⊢ False. *)
(*   Proof. *)
(*     iIntros (Hvalid) "Hown". *)
(*     iDestruct (own_and_total with "Hown") as (c) "[Hown [%Ha1 %Ha2]]". *)
(*     iDestruct (own_valid with "Hown") as %?; eauto. *)
(*   Qed. *)
(* End own_forall. *)
