From iris.algebra Require Import auth agree excl csum.
From Perennial.algebra Require Import auth_map.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.
From Perennial.goose_lang.lib.struct Require Import struct.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.program_proof Require Import addr_proof.

Section recoverable.
  Context {Σ:Type}.
  Context `{INH: Inhabited Σ}.
  Inductive RecoverableState :=
    | Closed (s:Σ)
    | Opened (s:Σ)
  .

  Definition recoverable_model : ffi_model :=
    mkFfiModel (RecoverableState) (populate (Closed (inhabitant INH))).

  Local Existing Instance recoverable_model.

  Context {ext:ext_op}.

  Definition openΣ : transition state Σ :=
    bind (reads id) (λ rs, match rs.(world) with
                           | Opened s => ret s
                           | _ => undefined
                           end).

  Definition modifyΣ (f:Σ -> Σ) : transition state unit :=
    bind openΣ (λ s, modify (set world (λ _, Opened (f s)))).

  Definition open : transition state Σ :=
    bind (reads id) (λ rs, match rs.(world) with
                           | Closed s => bind (modify (set world (fun _ => Opened s)))
                                             (fun _ => ret s)
                           | _ => undefined
                           end).

  Definition close : transition (RecoverableState) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s | Closed s => modify (fun _ => Closed s)
                           end).

  Global Instance Recoverable_inhabited : Inhabited RecoverableState := populate (Closed (inhabitant INH)).
End recoverable.

Arguments RecoverableState Σ : clear implicits.
Arguments recoverable_model Σ : clear implicits.

Definition ty_ := forall (val_ty:val_types), @ty val_ty.
(* TODO: slice should not require an entire ext_ty *)
Definition sliceT_ (t: ty_) : ty_ := λ val_ty, prodT (arrayT (t _)) uint64T.
Definition blockT_: ty_ := sliceT_ (λ val_ty, byteT).

Inductive JrnlOp :=
  | ReadBufOp (* jrnl, addr *)
  | ReadBitOp (* jrnl, addr *)
  | OverWriteOp (* jrnl, addr, data tuple *)
  | OverWriteBitOp (* jrnl, addr, byte *)
  | OpenOp (* (no arguments) *)
.

Instance eq_JrnlOp : EqDecision JrnlOp.
Proof.
  solve_decision.
Defined.

Instance JrnlOp_fin : Countable JrnlOp.
Proof.
  solve_countable JrnlOp_rec 5%nat.
Qed.

Definition jrnl_op : ext_op.
Proof.
  refine (mkExtOp JrnlOp _ _).
Defined.

(* Should addrs be opaque? I think not *)
Inductive Jrnl_ty := JrnlT.

Instance jrnl_val_ty: val_types :=
  {| ext_tys := Jrnl_ty; |}.

Section jrnl.
  Existing Instances jrnl_op jrnl_val_ty.

  Definition obj := list u8.

  Definition val_of_obj (o : obj) := val_of_list ((λ u, LitV (LitByte u)) <$> o).

  Definition blkno := u64.
  Definition kind := { k : Z | k = 0 ∨ 3 <= k <= 15 }.

  (* The only operation that can be called outside an atomically block is OpenOp *)
  Inductive jrnl_ext_tys : @val jrnl_op -> (ty * ty) -> Prop :=
  | JrnlOpType :
      jrnl_ext_tys (λ: "v", ExternalOp OpenOp (Var "v"))%V (unitT, extT JrnlT).

  Instance jrnl_ty: ext_types jrnl_op :=
    {| val_tys := jrnl_val_ty;
       get_ext_tys := jrnl_ext_tys |}.

  Definition addrT : ty := impl.struct.t (impl.struct.decl [
    "Blkno" :: uint64T;
    "Off" :: uint64T
  ])%struct.

  Definition jrnl_map : Type := gmap addr obj * gmap blkno kind.

  Definition jrnlData (m : jrnl_map) := fst m.
  Definition jrnlKinds (m : jrnl_map) := snd m.

  Definition updateData m a o := (<[a := o]> (jrnlData m), jrnlKinds m).

  Definition offsets_aligned (m : jrnl_map) :=
    (∀ a, a ∈ dom (gset _) (jrnlData m) →
     ∃ k, jrnlKinds m !! (addrBlock a) = Some k ∧ (int.Z (addrOff a) `mod` 2^(`k) = 0)).

  Definition size_consistent a (o: obj) (jk: gmap blkno kind) :=
    ∃ k, jk !! (addrBlock a) = Some k ∧ (length o : Z) = 2^(`k).

  Definition sizes_correct (m : jrnl_map) :=
    (∀ a o, jrnlData m !! a = Some o → ∃ k, jrnlKinds m !! (addrBlock a) = Some k ∧ (length o : Z) = 2^(`k)).

  (* TODO: do we need to enforce that every valid offset in a block has some data? *)
  Definition wf_jrnl (m : jrnl_map) := offsets_aligned m ∧ sizes_correct m.

  Definition jrnl_state := RecoverableState (jrnl_map).

  Definition get_jrnl (s: jrnl_state) :=
    match s with
      | Closed j | Opened j => j
    end.

  Instance jrnl_model : ffi_model := recoverable_model jrnl_map (populate (∅, ∅)).

  Existing Instances r_mbind r_fmap.

  Fixpoint tmapM {Σ A B} (f: A -> transition Σ B) (l: list A) : transition Σ (list B) :=
    match l with
    | [] => ret []
    | x::xs => b ← f x;
             bs ← tmapM f xs;
             ret (b :: bs)
    end.

  Definition allocIdent: transition state loc :=
    l ← allocateN 1;
    modify (set heap <[l := Free #()]>);;
    ret l.

  Existing Instance fallback_genPred.

  Definition jrnl_step (op:JrnlOp) (v:val) : transition state val :=
    match op, v with
    | OpenOp, LitV LitUnit =>
      j ← open;
      ret $ LitV $ LitUnit
    | ReadBufOp, PairV (#(LitInt blkno), (#(LitInt off), #()))%V #(LitInt sz) =>
      j ← openΣ;
      d ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      (* bit reads must be done with ReadBitOp *)
      check (`k ≠ 0 ∧ 2^(`k) = int.Z sz);;
      ret $ val_of_obj d
    | WriteBufOp, ((#(LitInt blkno), #(LitInt off), #()), ov)%V =>
      j ← openΣ;
      (* This only allows writing to addresses that already have defined contents *)
      _ ← unwrap (jrnlData j !! (Build_addr blkno off));
      k ← unwrap (jrnlKinds j !! blkno);
      o ← suchThat (λ _ o, val_of_obj o = ov);
      check ((length o : Z) = 2^(`k) ∧ `k ≠ 0);;
      modifyΣ (λ j, updateData j (Build_addr blkno off) o);;
      ret $ #()
    | _, _ => undefined
    end.

  Instance jrnl_semantics : ext_semantics jrnl_op jrnl_model :=
    {| ext_step := jrnl_step;
       ext_crash := fun s s' => relation.denote close s s' tt; |}.
End jrnl.


Definition openR := csumR (prodR fracR (agreeR (leibnizO unitO))) (agreeR (leibnizO unitO)).
Definition jrnl_opened : openR := Cinr (to_agree tt).

Class jrnlG Σ :=
  { jrnlG_open_inG :> inG Σ openR;
    jrnlG_open_name : gname;
    jrnlG_data_inG :> mapG Σ addr obj;
    jrnlG_data_name: gname;
    jrnlG_kinds_inG :> mapG Σ blkno kind;
    jrnlG_kinds_name: gname;
  }.

Class jrnl_preG Σ :=
  { jrnlG_preG_open_inG :> inG Σ openR;
    jrnlG_preG_data_inG:> mapG Σ addr obj;
    jrnlG_preG_kinds_inG:> mapG Σ blkno kind;
  }.

Definition jrnlΣ : gFunctors :=
  #[GFunctor openR; mapΣ addr obj; mapΣ blkno kind].

Instance subG_jrnlG Σ: subG jrnlΣ Σ → jrnl_preG Σ.
Proof. solve_inG. Qed.

Record jrnl_names :=
  { jrnl_names_open: gname;
    jrnl_names_data: gname;
    jrnl_names_kinds: gname;
  }.

Definition jrnl_get_names {Σ} (jG: jrnlG Σ) :=
  {| jrnl_names_open := jrnlG_open_name;
     jrnl_names_data := jrnlG_data_name;
     jrnl_names_kinds := jrnlG_kinds_name |}.

Definition jrnl_update {Σ} (jG: jrnlG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
  |}.

Definition jrnl_update_pre {Σ} (jG: jrnl_preG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_preG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_preG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_preG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
  |}.

Definition jrnl_open {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (jrnl_opened).
Definition jrnl_closed_frag {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_closed_auth {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_mapsto {Σ} {lG: jrnlG Σ} a q v : iProp Σ :=
  ptsto_mut (jrnlG_data_name) a q v ∗
  (∃ (k : kind), ⌜ (length v : Z) = 2^(`k) ⌝ ∗ ptsto_ro (jrnlG_kinds_name) (addrBlock a) (k : kind)).
Definition jrnl_kinds_mapsto {Σ} {lG: jrnlG Σ} blk k : iProp Σ :=
  ptsto_ro (jrnlG_kinds_name) blk (k : kind).

Section jrnl_interp.
  Existing Instances jrnl_op jrnl_model jrnl_val_ty.

  Definition jrnl_state_ctx {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ⌜ wf_jrnl m ⌝ ∗
      map_ctx jrnlG_data_name 1 (jrnlData m) ∗
      map_ctx jrnlG_kinds_name 1 (jrnlKinds m).

  Definition jrnl_ctx {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_ctx s
    | Closed s => jrnl_closed_auth ∗ jrnl_state_ctx s
    end.

  Definition jrnl_state_start {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    [∗ map] a ↦ v ∈ jrnlData m, jrnl_mapsto a 1 v.

  Definition jrnl_start {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_start s
    | Closed s => jrnl_closed_frag ∗ jrnl_state_start s
    end.

  Definition jrnl_restart {Σ} (jG: jrnlG Σ) (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open
    | Closed s => jrnl_closed_frag
    end.

  Program Instance jrnl_interp : ffi_interp jrnl_model :=
    {| ffiG := jrnlG;
       ffi_names := jrnl_names;
       ffi_get_names := @jrnl_get_names;
       ffi_update := @jrnl_update;
       ffi_get_update := _;
       ffi_ctx := @jrnl_ctx;
       ffi_start := @jrnl_start;
       ffi_restart := @jrnl_restart;
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @jrnlG_data_inG _ hF1 = @jrnlG_data_inG _ hF2 ∧
                                             @jrnlG_kinds_inG _ hF1 = @jrnlG_kinds_inG _ hF2 ∧
                                           jrnl_names_data (jrnl_get_names hF1) =
                                           jrnl_names_data (jrnl_get_names hF2) ∧
                                           jrnl_names_kinds (jrnl_get_names hF1) =
                                           jrnl_names_kinds (jrnl_get_names hF2) ⌝%I;
    |}.
  Next Obligation. intros ? [] [] => //=. Qed.
  Next Obligation. intros ? [] => //=. Qed.
  Next Obligation. intros ? [] => //=. Qed.

End jrnl_interp.


Section jrnl_lemmas.
  Context `{lG: jrnlG Σ}.

  Global Instance jrnl_ctx_Timeless lg: Timeless (jrnl_ctx lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_start_Timeless lg: Timeless (jrnl_start lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_restart_Timeless lg: Timeless (jrnl_restart _ lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance jrnl_open_Persistent : Persistent (jrnl_open).
  Proof. rewrite /jrnl_open/jrnl_opened. apply own_core_persistent. rewrite /CoreId//=. Qed.

  Lemma jrnl_closed_auth_opened :
    jrnl_closed_auth -∗ jrnl_open -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma jrnl_closed_token_open :
    jrnl_closed_auth -∗ jrnl_closed_frag ==∗ jrnl_open.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (jrnl_opened) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op' Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma jrnl_ctx_unify_closed lg:
    jrnl_closed_frag -∗ jrnl_ctx lg -∗ ⌜ ∃ vs, lg = Closed vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hclosed_frag Hctx".
    iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
    iDestruct (jrnl_closed_auth_opened with "[$] [$]") as %[].
  Qed.

  Lemma jrnl_ctx_unify_opened lg:
    jrnl_open -∗ jrnl_ctx lg -∗ ⌜ ∃ vs, lg = Opened vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hopen Hctx".
    iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

End jrnl_lemmas.

From Perennial.goose_lang Require Import adequacy.

Program Instance jrnl_interp_adequacy:
  @ffi_interp_adequacy jrnl_model jrnl_interp jrnl_op jrnl_semantics :=
  {| ffi_preG := jrnl_preG;
     ffiΣ := jrnlΣ;
     subG_ffiPreG := subG_jrnlG;
     ffi_initP := λ σ, ∃ m, σ = Closed m ∧ wf_jrnl m;
     ffi_update_pre := @jrnl_update_pre;
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ (m&->&Hwf)). simpl.
  iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (map_init_many (jrnlData m)) as (γdata) "(Hdata_ctx&Hdata)".
  iMod (map_init_many_ro (jrnlKinds m)) as (γkinds) "(Hkinds_ctx&#Hkinds)".
  iExists {| jrnl_names_open := γ1; jrnl_names_data := γdata; jrnl_names_kinds := γkinds |}.
  iFrame. iModIntro. iFrame "%".
  rewrite assoc.
  iSplitL "H".
  { by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp. }
  rewrite /jrnl_state_start.
  iDestruct (big_sepM.big_sepM_mono_with_inv with "Hkinds Hdata") as "(_&$)".
  iIntros (a x Hlookup) "(#Hkinds&Hpt)". iFrame "Hkinds".
  rewrite /jrnl_mapsto.
  rewrite /wf_jrnl/offsets_aligned/sizes_correct in Hwf.
  destruct Hwf as (Hoff&Hsize).
  edestruct Hsize as (k&Hlookup_kind&Hlen); eauto. iFrame.
  iExists k. iFrame "%".
  iApply (big_sepM_lookup); eauto.
Qed.
Next Obligation.
  iIntros (Σ σ σ' Hcrash Hold) "Hinterp".
  inversion Hcrash; subst.
  monad_inv. inversion H. subst. inversion H1. subst.
  destruct x; monad_inv.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/jrnl_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/jrnl_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance jrnl_spec_ext : spec_ext_op := {| spec_ext_op_field := jrnl_op |}.
Instance jrnl_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := jrnl_model |}.
Instance jrnl_spec_ext_semantics : spec_ext_semantics (jrnl_spec_ext) (jrnl_spec_ffi_model) :=
  {| spec_ext_semantics_field := jrnl_semantics |}.
Instance jrnl_spec_ffi_interp : spec_ffi_interp jrnl_spec_ffi_model :=
  {| spec_ffi_interp_field := jrnl_interp |}.
Instance jrnl_spec_ty : ext_types (spec_ext_op_field) := jrnl_ty.
Instance jrnl_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := jrnl_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := jrnl_interp_adequacy |}.

Context `{invG Σ}.
Context `{crashG Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.

Implicit Types K: spec_lang.(language.expr) → spec_lang.(language.expr).
Instance jrnlG0 : jrnlG Σ := refinement_spec_ffiG.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | [ H1: context[ match world ?σ with | _ => _ end ], Heq: world ?σ = _ |- _ ] =>
          rewrite Heq in H1
        end.

Notation spec_ext := jrnl_spec_ext.
Notation sstate := (@state (@spec_ext_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation shead_step := (@head_step (@spec_ext_op_field spec_ext)).
Notation sworld := (@world (@spec_ext_op_field spec_ext) (@spec_ffi_model_field jrnl_spec_ffi_model)).

Definition jrnl_sub_dom (σj1 σj2 : jrnl_map) : Prop :=
  (dom (gset _) (jrnlData σj1) = dom _ (jrnlData σj2) ∧ jrnlKinds σj1 ⊆ jrnlKinds σj2).

Definition jrnl_sub_state (σj : jrnl_map) (s: sstate) : Prop :=
  (∃ sj, s.(world) = Opened sj ∧ jrnlData σj ⊆ jrnlData sj ∧ jrnlKinds σj ⊆ jrnlKinds sj).

Definition jrnl_upd (σj: jrnl_map) (s: sstate) : sstate :=
  set sworld (λ s, Opened (jrnlData σj ∪ (jrnlData $ get_jrnl s), jrnlKinds $ get_jrnl s)) s.

Definition always_steps (e: sexpr) (σj: jrnl_map) (e': sexpr) (σj': jrnl_map) : Prop :=
  (jrnlKinds σj = jrnlKinds σj') ∧
  (jrnl_sub_dom σj σj') ∧
  (∀ s, jrnl_sub_state σj s →
           rtc (λ '(e, s) '(e', s'), prim_step' e s [] e' s' []) (e, s) (e', jrnl_upd σj' s)).

Lemma jrnl_upd_sub σj s :
  jrnl_sub_state σj s →
  jrnl_upd σj s = s.
Proof.
  intros (sj&Heq1&Hsub1&Hsub2).
  rewrite /jrnl_upd.
  destruct s. rewrite /set//=. f_equal.
  rewrite /= in Heq1. rewrite Heq1. f_equal. destruct sj as (sjd, sjk).
  f_equal => /=. apply map_subseteq_union; auto.
Qed.

Lemma jrnl_sub_state_upd σj1 σj2 s :
  jrnl_sub_state σj1 s →
  jrnlKinds σj1 = jrnlKinds σj2 →
  jrnl_sub_state σj2 (jrnl_upd σj2 s).
Proof.
  intros (sj&Heq&Hsub_data&Hsub_kinds) Heq_kinds.
  eexists; split; eauto => /=.
  split.
  - apply map_union_subseteq_l.
  - rewrite Heq /= -Heq_kinds //.
Qed.

Lemma jrnl_upd_upd_sub_dom σj1 σj2 s :
  jrnl_sub_dom σj1 σj2 →
  jrnl_upd σj2 (jrnl_upd σj1 s) = jrnl_upd σj2 s.
Proof.
  intros (?&?).
  rewrite /jrnl_upd/set //=. do 3 f_equal.
  apply map_eq => i.
  destruct (jrnlData σj2 !! i) eqn:Hlookup.
  { erewrite lookup_union_Some_l; eauto.
    erewrite lookup_union_Some_l; eauto. }
  rewrite ?lookup_union_r //.
  apply not_elem_of_dom. apply not_elem_of_dom in Hlookup. rewrite H1. auto.
Qed.

Lemma jrnl_upd_idemp σj s :
  jrnl_upd σj (jrnl_upd σj s) = jrnl_upd σj s.
Proof.
  rewrite /jrnl_upd/set//=. do 3 f_equal.
  rewrite map_union_assoc map_union_idemp //.
Qed.

Lemma always_steps_refl e σj :
  always_steps e σj e σj.
Proof.
  split_and! => //= s Hsub.
  rewrite jrnl_upd_sub //.
Qed.

Lemma jrnl_sub_dom_trans σj1 σj2 σj3 :
  jrnl_sub_dom σj1 σj2 →
  jrnl_sub_dom σj2 σj3 →
  jrnl_sub_dom σj1 σj3.
Proof.
  intros (?&?) (?&?); split; etransitivity; eauto.
Qed.

Lemma always_steps_trans e1 σj1 e2 σj2 e3 σj3 :
  always_steps e1 σj1 e2 σj2 →
  always_steps e2 σj2 e3 σj3 →
  always_steps e1 σj1 e3 σj3.
Proof.
  intros (Hkinds1&Hsub1&Hsteps1) (Hkinds2&Hsub2&Hsteps2).
  split_and!; first congruence.
  { eapply jrnl_sub_dom_trans; eassumption. }
  intros s Hsub.
  eapply rtc_transitive.
  { eapply Hsteps1; eauto. }
  { assert (jrnl_upd σj3 s = jrnl_upd σj3 (jrnl_upd σj2 s)) as ->.
    { rewrite jrnl_upd_upd_sub_dom; eauto. }
    eapply Hsteps2; eauto.
    eapply jrnl_sub_state_upd; eauto.
  }
Qed.

Lemma insert_jrnl_upd a o σj s :
  a ∉ dom (gset _) (jrnlData σj) →
  jrnl_upd (<[a := o]> (jrnlData σj), jrnlKinds σj) s =
  jrnl_upd σj (jrnl_upd ({[ a := o]}, jrnlKinds σj) s).
Proof.
  intros.
  rewrite /jrnl_upd/set/=. do 3 f_equal.
  rewrite insert_union_singleton_l.
  rewrite (map_union_comm ({[a := o]})) ?assoc //.
  apply map_disjoint_dom_2.
  rewrite dom_singleton. set_solver.
Qed.

Lemma always_steps_bind `{Hctx: LanguageCtx' (ext := @spec_ext_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K} e1 e2 σj1 σj2 :
  always_steps e1 σj1 e2 σj2 →
  always_steps (K e1) σj1 (K e2) σj2.
Proof.
  rewrite /always_steps.
  intros (?&?&Hstep). split_and!; eauto.
  intros s Hsub. specialize (Hstep _ Hsub).
  clear -Hstep Hctx.
  remember (e1, s) as ρ1 eqn:Hρ1.
  remember (e2, jrnl_upd σj2 s) as ρ2 eqn:Hρ2.
  revert Hρ1 Hρ2.
  generalize (jrnl_upd σj2 s) as s'.
  revert e1 e2 s.
  induction Hstep.
  - intros. rewrite Hρ1 in Hρ2. inversion Hρ2. subst.
    apply rtc_refl.
  - intros. subst. destruct y as (e0'&s0').
    eapply rtc_l; last first.
    { eapply IHHstep; eauto. }
    simpl. eapply fill_step'. eauto.
Qed.

Lemma insert_jrnl_sub_state a o σj s:
  jrnl_sub_state (<[a:=o]> (jrnlData σj), jrnlKinds σj) s →
  s = (jrnl_upd ({[ a := o]}, jrnlKinds σj) s).
Proof.
  rewrite /jrnl_sub_state /=.
  intros (sj&Heq1&Hsub1&Hsub2).
  rewrite /jrnl_upd/set. destruct s => //=. simpl in Heq1. f_equal.
  rewrite Heq1. f_equal.
  destruct sj; f_equal. apply map_eq.
  intros i => /=.
  destruct (decide (a = i)).
  - subst.
    transitivity (({[i := o]} : gmap addr obj) !! i).
    { rewrite lookup_singleton.
      eapply lookup_weaken; eauto. rewrite lookup_insert //=. }
    rewrite lookup_singleton. symmetry.
    apply lookup_union_Some_l.
    apply lookup_singleton.
  - rewrite lookup_union_r //.
    rewrite lookup_singleton_ne //=.
Qed.

Lemma always_steps_extend e1 σj1 e2 σj2 a o :
  (a ∉ dom (gset _) (jrnlData σj2)) →
  size_consistent a o (jrnlKinds σj1) →
  always_steps e1 σj1 e2 σj2 →
  always_steps e1 (<[a := o]> $ jrnlData σj1, jrnlKinds σj1)
               e2 (<[a := o]> $ jrnlData σj2, jrnlKinds σj2).
Proof.
  intros Hdom Hconsistent (?&Hsub&Hstep).
  split_and!.
  - simpl. congruence.
  - destruct Hsub as (?&?). split_and! => //=.
    rewrite ?dom_insert_L H2. set_solver.
  - intros s Hsub_state.
    rewrite insert_jrnl_upd //.
    rewrite {1}(insert_jrnl_sub_state _ _ _ _ Hsub_state).
    apply Hstep.
    rewrite /jrnl_sub_state.
    destruct Hsub_state as (sj&Hworld&Hsub_data&?).
    rewrite /jrnl_upd/set//=. rewrite Hworld /=.
    eexists; split_and!; eauto => /=.
    intros i => /=.
    specialize (Hsub_data i).
    destruct Hsub as (Hsub_data'&?).
    assert (a ∉ dom (gset _) (jrnlData σj1)) as Hdom' by (rewrite Hsub_data'; set_solver).
    destruct (decide (a = i)).
    * subst. apply not_elem_of_dom in Hdom'.
      rewrite Hdom' => //=. destruct (({[ i := o]} ∪ jrnlData sj) !! i) eqn:Heq; rewrite Heq //.
    * rewrite lookup_union_r ?lookup_singleton_ne //.
      rewrite lookup_insert_ne // in Hsub_data.
Qed.

Definition addr2val' (a : addr) : sval := (#(addrBlock a), (#(addrOff a), #()))%V.
Lemma always_steps_ReadBufOp a v (sz: u64) k σj:
  jrnlData σj !! a = Some v →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (`k ≠ 0 ∧ 2^(`k) = int.Z sz) →
  always_steps (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                           ReadBufOp
                           (PairV (addr2val' a) #sz))
               σj
               (val_of_obj v)
               σj.
Proof.
  intros Hlookup1 Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; set_solver. }
  intros s Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    eapply lookup_weaken in Hlookup2; last eassumption.
    rewrite Hlookup2. econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite decide_True //=. }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ:
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ jrnl_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ?????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)) eqn:Heq; try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
  }
  { solve_ndisj. }
Qed.

Lemma jrnl_opened_open_false E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_open -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma jrnl_open_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step_trans. simpl. econstructor.
      * eexists _ _; repeat econstructor.
        ** simpl. rewrite Heq. repeat econstructor.
      * repeat econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { simpl. congruence. }
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma jrnl_ctx_sub_state_valid σj s :
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  ([∗ map] b ↦ k ∈ (jrnlKinds σj), jrnl_kinds_mapsto b k) -∗
    jrnl_open -∗
    jrnl_ctx s.(world) -∗
    ⌜ jrnl_sub_state σj s ⌝.
Proof.
  iIntros "Hpts #Hkinds #Hopen Hctx".
  rewrite /jrnl_sub_state.
Admitted.

(*
Lock Invariant for address a in 2PL:

durable_mapsto γ a o

Doesn't work: ∃ o, jrnl_mapsto a 1 o ∗  durable_mapsto_own γ a o

durable_mapsto γ a o
ephemeral_mapsto γ a o

Lock invariant :
∃ o, ephemeral_mapsto γ a o ∗
     na_crash_inv (jrnl_mapsto a 1 o ∗ durable_mapsto γ a o)
                  (∃ o', jrnl_mapsto a 1 o' ∗ durable_mapsto γ' a o')

*)

Lemma ghost_step_jrnl_atomically E j K {HCTX: LanguageCtx K} (l: sval) e σj (v: sval) σj' :
  always_steps e σj v σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  ([∗ map] b ↦ k ∈ (jrnlKinds σj), jrnl_kinds_mapsto b k) -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |NC={E}=>
  j ⤇ K (SOMEV v) ∗ ([∗ map] a ↦ o ∈ (jrnlData σj'), jrnl_mapsto a 1 o).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hopen Hj".
  destruct Hsteps as (?&?&Hrtc).
  iInv "Hstate" as (s) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$]") as %Hsub.
  iMod (ghost_step_lifting _ _ _ (Atomically l e) s [] (jrnl_upd σj' s) (SOMEV v) [] with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step.
    apply head_step_atomically.
    eapply Hrtc.
    auto.
  }
  { solve_ndisj. }
  simpl.
  (*
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _. iFrame "H".  iFrame. iFrame "Hopen". }
  iModIntro. iFrame "# ∗".
   *)
Abort.


End spec.
