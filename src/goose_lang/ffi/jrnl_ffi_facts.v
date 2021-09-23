(* This file contains lemmas and facts for proving refinements from the jrnl
   FFI.  These lemmas could in principle be of use for many possible
   implementations of the jrnl and its concurrency control. *)

From iris.algebra Require Import auth frac agree excl csum.
From Perennial.algebra Require Import auth_map.
From RecordUpdate Require Import RecordSet.
Require Import Coq.Logic.Classical_Prop.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.base_logic.lib Require Import ghost_var.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.
From Perennial.goose_lang.lib.struct Require Import struct.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.program_proof Require Import addr_proof buf.buf_proof.
From Perennial.program_proof Require obj.recovery_proof.

From Perennial.goose_lang Require Import ffi.jrnl_ffi_spec.

Local Existing Instances jrnl_op jrnl_val_ty.

Lemma val_of_list_inj o1 o2:
  val_of_list o1 = val_of_list o2 →
  o1 = o2.
Proof.
  revert o2.
  induction o1 => o2.
  - rewrite //=. destruct o2; try congruence.
    inversion 1.
  - rewrite //=. destruct o2; try inversion 1.
    subst. naive_solver.
Qed.

Lemma val_of_obj'_inj o1 o2:
  val_of_obj' (objBytes o1) = val_of_obj' (objBytes o2) →
  o1 = o2.
Proof.
  rewrite /=.
  intros Hval%val_of_list_inj.
  apply fmap_inj in Hval; eauto.
  intros ??. inversion 1; eauto.
Qed.

Lemma val_of_obj'_inj2 o1 o k:
  val_of_obj' (objBytes o1) = val_of_obj' o →
  objSz (objBytes o1) = bufSz k →
  k ≠ KindBit →
  o = objBytes o1.
Proof.
  destruct o.
  - rewrite /val_of_obj'; destruct o1 => //=.
  - intros ?%val_of_obj'_inj; eauto. congruence.
Qed.

Lemma val_of_obj'_inj3 o1 o:
  val_of_obj' (objBit o1) = val_of_obj' o →
  o = objBit o1.
Proof.
  destruct o.
  - rewrite /val_of_obj'; destruct o1 => //=; congruence.
  - rewrite //=.
    rewrite /val_of_list; destruct data => //=.
Qed.

Definition openR := csumR (prodR fracR (agreeR (leibnizO unitO))) (agreeR (leibnizO unitO)).
Definition jrnl_opened : openR := Cinr (to_agree tt).

Class jrnlG Σ :=
  { jrnlG_open_inG :> inG Σ openR;
    jrnlG_open_name : gname;
    jrnlG_data_inG :> mapG Σ addr obj;
    jrnlG_data_name: gname;
    jrnlG_kinds_inG :> inG Σ (agreeR (leibnizO (gmap blkno kind)));
    jrnlG_kinds_name: gname;
    jrnlG_dom_inG :> inG Σ (agreeR (leibnizO (gset addr)));
    jrnlG_dom_name: gname;
    jrnlG_crash_toks_inG :> mapG Σ addr unit;
    jrnlG_crash_toks_name: gname;
    jrnlG_full_crash_tok_inG :> ghost_varG Σ unit;
    jrnlG_full_crash_tok_name: gname;
    jrnlG_allocs_inG :> mapG Σ loc u64;
    jrnlG_allocs_name : gname;
  }.

Class jrnl_preG Σ :=
  { jrnlG_preG_open_inG :> inG Σ openR;
    jrnlG_preG_data_inG:> mapG Σ addr obj;
    jrnlG_preG_kinds_inG:> inG Σ (agreeR (leibnizO (gmap blkno kind)));
    jrnlG_preG_dom_inG:> inG Σ (agreeR (leibnizO (gset addr)));
    jrnlG_preG_crash_toks_inG:> mapG Σ addr unit;
    jrnlG_preG_full_crash_tok_inG :> ghost_varG Σ unit;
    jrnlG_preG_allocs_inG :> mapG Σ loc u64;
  }.

Definition jrnlΣ : gFunctors :=
  #[GFunctor openR; mapΣ addr obj;
    GFunctor (agreeR (leibnizO (gmap blkno kind)));
    GFunctor (agreeR (leibnizO (gset addr)));
    mapΣ addr unit;
    ghost_varΣ unit;
    mapΣ loc u64
   ].

Instance subG_jrnlG Σ: subG jrnlΣ Σ → jrnl_preG Σ.
Proof. solve_inG. Qed.

Record jrnl_names :=
  { jrnl_names_open: gname;
    jrnl_names_data: gname;
    jrnl_names_kinds: gname;
    jrnl_names_dom: gname;
    jrnl_names_crash: gname;
    jrnl_names_full_crash: gname;
    jrnl_names_allocs: gname;
  }.

Definition jrnl_get_names {Σ} (jG: jrnlG Σ) :=
  {| jrnl_names_open := jrnlG_open_name;
     jrnl_names_data := jrnlG_data_name;
     jrnl_names_kinds := jrnlG_kinds_name;
     jrnl_names_dom := jrnlG_dom_name;
     jrnl_names_crash := jrnlG_crash_toks_name;
     jrnl_names_full_crash := jrnlG_full_crash_tok_name;
     jrnl_names_allocs := jrnlG_allocs_name;
|}.

Definition jrnl_update {Σ} (jG: jrnlG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
     jrnlG_dom_inG := jrnlG_dom_inG;
     jrnlG_dom_name := (jrnl_names_dom names);
     jrnlG_crash_toks_inG := jrnlG_crash_toks_inG;
     jrnlG_crash_toks_name := (jrnl_names_crash names);
     jrnlG_full_crash_tok_inG := jrnlG_full_crash_tok_inG;
     jrnlG_full_crash_tok_name := (jrnl_names_full_crash names);
     jrnlG_allocs_inG := jrnlG_allocs_inG;
     jrnlG_allocs_name := (jrnl_names_allocs names);
  |}.

Definition jrnl_update_pre {Σ} (jG: jrnl_preG Σ) (names: jrnl_names) :=
  {| jrnlG_open_inG := jrnlG_preG_open_inG;
     jrnlG_open_name := (jrnl_names_open names);
     jrnlG_data_inG := jrnlG_preG_data_inG;
     jrnlG_data_name := (jrnl_names_data names);
     jrnlG_kinds_inG := jrnlG_preG_kinds_inG;
     jrnlG_kinds_name := (jrnl_names_kinds names);
     jrnlG_dom_inG := jrnlG_preG_dom_inG;
     jrnlG_dom_name := (jrnl_names_dom names);
     jrnlG_crash_toks_inG := jrnlG_preG_crash_toks_inG;
     jrnlG_crash_toks_name := (jrnl_names_crash names);
     jrnlG_full_crash_tok_inG := jrnlG_preG_full_crash_tok_inG;
     jrnlG_full_crash_tok_name := (jrnl_names_full_crash names);
     jrnlG_allocs_inG := jrnlG_preG_allocs_inG;
     jrnlG_allocs_name := (jrnl_names_allocs names);
  |}.

Definition jrnl_open {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (jrnl_opened).
Definition jrnl_closed_frag {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_closed_auth {Σ} {lG :jrnlG Σ} :=
  own (jrnlG_open_name) (Cinl ((1/2)%Qp, to_agree (tt : leibnizO unit))).
Definition jrnl_kinds {Σ} {lG: jrnlG Σ} σj : iProp Σ :=
 (own (jrnlG_kinds_name) (to_agree (σj : leibnizO (gmap blkno kind)))).
Definition jrnl_kinds_lb {Σ} {lG: jrnlG Σ} (σj : gmap blkno kind) : iProp Σ :=
 (∃ σj', ⌜ σj ⊆ σj' ⌝ ∧ own (jrnlG_kinds_name) (to_agree (σj' : leibnizO (gmap blkno kind)))).
Definition jrnl_mapsto {Σ} {lG: jrnlG Σ} a q v : iProp Σ :=
  ptsto_mut (jrnlG_data_name) a q v ∗
  (∃ σj,  ⌜ size_consistent_and_aligned a v σj ⌝ ∗ jrnl_kinds σj).
Definition jrnl_crash_tok {Σ} {lG: jrnlG Σ} a : iProp Σ :=
  ptsto_mut (jrnlG_crash_toks_name) a 1 tt.
Definition jrnl_dom {Σ} {lG: jrnlG Σ} (σ: gset addr) : iProp Σ :=
  own (jrnlG_dom_name) (to_agree (σ: leibnizO (gset addr))).
Definition jrnl_full_crash_tok {Σ} {lG: jrnlG Σ} : iProp Σ :=
  ghost_var (jrnlG_full_crash_tok_name) 1 tt.
Definition jrnl_alloc {Σ} {lG: jrnlG Σ} (l: loc) (v : u64) : iProp Σ :=
  ptsto_ro (jrnlG_allocs_name) l v.
Definition jrnl_alloc_map {Σ} {lG: jrnlG Σ} (σ: gmap loc u64) : iProp Σ :=
  [∗ map] l ↦ v ∈ σ, jrnl_alloc l v.

Section jrnl_interp.
  Existing Instances jrnl_op jrnl_model jrnl_val_ty.

  Definition jrnl_state_ctx {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ⌜ wf_jrnl m ⌝ ∗
      map_ctx jrnlG_data_name 1 (jrnlData m) ∗
      jrnl_kinds (jrnlKinds m) ∗
      jrnl_dom (dom (gset _) (jrnlData m)) ∗
      map_ctx jrnlG_allocs_name 1 (jrnlAllocs m).

  Definition jrnl_ctx {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_ctx s
    | Closed s => jrnl_closed_auth ∗ jrnl_state_ctx s
    end.

  Definition jrnl_crash_ctx {Σ} {jG: jrnlG Σ} : iProp Σ :=
    ∃ m, ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
          map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
          jrnl_full_crash_tok.

  Definition jrnl_state_start {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_mapsto a 1 v) ∗
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
    map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
    jrnl_kinds (jrnlKinds m) ∗
    jrnl_dom (dom (gset _) (jrnlData m)) ∗
    jrnl_full_crash_tok.


  Definition jrnl_state_restart {Σ} {jG: jrnlG Σ} (m: jrnl_map) : iProp Σ :=
    ([∗ map] a ↦ v ∈ jrnlData m, jrnl_crash_tok a) ∗
    map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> jrnlData m) ∗
    jrnl_kinds (jrnlKinds m) ∗
    jrnl_dom (dom (gset _) (jrnlData m)) ∗
    jrnl_full_crash_tok.

  Definition jrnl_start {Σ} {jG: jrnlG Σ} (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_start s
    | Closed s => jrnl_closed_frag ∗ jrnl_state_start s
    end.

  Definition jrnl_restart {Σ} (jG: jrnlG Σ) (jrnl: @ffi_state jrnl_model) : iProp Σ :=
    match jrnl with
    | Opened s => jrnl_open ∗ jrnl_state_restart s
    | Closed s => jrnl_closed_frag ∗ jrnl_state_restart s
    end.

  Program Instance jrnl_interp : ffi_interp jrnl_model :=
    {| ffiLocalGS := jrnlG;
       ffiGlobalGS _ := ()%type;
       ffi_local_ctx := @jrnl_ctx;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ G w := @jrnl_start Σ G w;
       ffi_global_start _ _ _ := True%I;
       ffi_restart := @jrnl_restart;
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @jrnlG_data_inG _ hF1 = @jrnlG_data_inG _ hF2 ∧
                                             @jrnlG_kinds_inG _ hF1 = @jrnlG_kinds_inG _ hF2 ∧
                                             @jrnlG_dom_inG _ hF1 = @jrnlG_dom_inG _ hF2 ∧
                                           jrnl_names_data (jrnl_get_names hF1) =
                                           jrnl_names_data (jrnl_get_names hF2) ∧
                                           jrnl_names_kinds (jrnl_get_names hF1) =
                                           jrnl_names_kinds (jrnl_get_names hF2) ∧
                                           jrnl_names_dom (jrnl_get_names hF1) =
                                           jrnl_names_dom (jrnl_get_names hF2) ⌝%I;
    |}.

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

  Global Instance jrnl_kinds_lb_Persistent kmap : Persistent (jrnl_kinds_lb kmap).
  Proof. refine _. Qed.

  Definition jrnl_full_crash_tok_excl :
    jrnl_full_crash_tok -∗ jrnl_full_crash_tok -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_valid_2 with "[$] [$]") as %[Hval _].
    rewrite //= in Hval.
  Qed.

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
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
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

   Lemma jrnl_dom_agree σ1 σ2:
     jrnl_dom σ1 -∗ jrnl_dom σ2 -∗ ⌜ σ1 = σ2 ⌝.
   Proof.
     iIntros "H1 H2".
     iDestruct (own_valid_2 with "H1 H2") as %Hval.
     apply to_agree_op_valid in Hval. iPureIntro. set_solver.
   Qed.

  Lemma jrnl_ctx_allocs_agree σja σ:
    jrnl_alloc_map σja -∗ jrnl_state_ctx σ -∗ ⌜ σja ⊆ jrnlAllocs σ ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H2" as "(_&_&_&_&Hctx)".
    destruct σ as [? ? σja'] => /=.
    rewrite /jrnl_alloc_map.
    rewrite map_subseteq_spec.
    iIntros (l v Hlookup).
    iDestruct (big_sepM_lookup with "H1") as "H"; eauto.
    iDestruct (map_ro_valid with "[$] [$]") as %?; eauto.
  Qed.

  Lemma jrnl_ctx_allocs_agree2 σja l u:
    jrnl_alloc_map σja -∗ jrnl_alloc l u -∗ ⌜ σja !! l = None ∨ σja !! l = Some u ⌝.
  Proof.
    iIntros "Hjrnl_allocs Hjrnl_alloc1".
    destruct (σja !! l) as [u'|] eqn:Hlookup'; last eauto.
    iDestruct (big_sepM_lookup with "Hjrnl_allocs") as "H"; eauto.
    iDestruct (auth_map.ptsto_ro_agree with "H Hjrnl_alloc1") as %->; eauto.
  Qed.

  Lemma jrnl_ctx_allocs_extend σ l u:
    jrnl_alloc_map (jrnlAllocs σ) -∗ jrnl_alloc l u -∗ jrnl_alloc_map (jrnlAllocs (updateAllocs σ l u)).
  Proof.
    iIntros "Hjrnl_allocs Hjrnl_alloc1".
    rewrite /updateAllocs. destruct σ => //=.
    iDestruct (jrnl_ctx_allocs_agree2 with "[$] [$]") as %Hlookup.
    rewrite /jrnl_alloc_map.
    destruct Hlookup.
    - rewrite big_sepM_insert; auto.
    - rewrite insert_id //=.
  Qed.

  Lemma jrnl_state_ctx_extract_pers m :
    jrnl_state_ctx m -∗
    ⌜ wf_jrnl m ⌝ ∗
      jrnl_kinds (jrnlKinds m) ∗
      jrnl_dom (dom (gset _) (jrnlData m)).
  Proof. iDestruct 1 as "($&?&$&$&?)". Qed.

End jrnl_lemmas.

From Perennial.goose_lang Require Import adequacy.

Program Instance jrnl_interp_adequacy:
  @ffi_interp_adequacy jrnl_model jrnl_interp jrnl_op jrnl_semantics :=
  {| ffiGpreS := jrnl_preG;
     ffiΣ := jrnlΣ;
     subG_ffiPreG := subG_jrnlG;
     ffi_initgP := λ _, True;
     ffi_initP := λ σ _, ∃ m, σ = Closed m ∧ wf_jrnl m;
  |}.
Next Obligation. rewrite //=. eauto. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ g (m&->&Hwf)). simpl.
  iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (map_init_many (jrnlData m)) as (γdata) "(Hdata_ctx&Hdata)".
  iMod (map_init_many ((λ _, tt) <$> jrnlData m)) as (γcrash) "(Hcrash_ctx&Hcrash)".
  iMod (own_alloc (to_agree (jrnlKinds m : leibnizO (gmap blkno kind)))) as (γkinds) "#Hkinds".
  { constructor. }
  iMod (own_alloc (to_agree (dom (gset _) (jrnlData m) : leibnizO (gset addr)))) as (γdom) "#Hdom".
  { constructor. }
  iMod (ghost_var_alloc ()) as (γfull) "Hfull".
  iMod (map_init_many (jrnlAllocs m)) as (γallocs) "(Hallocs_ctx&_)".
  set (names := {| jrnl_names_open := γ1; jrnl_names_data := γdata; jrnl_names_kinds := γkinds;
             jrnl_names_dom := γdom;
             jrnl_names_crash := γcrash;
             jrnl_names_full_crash := γfull;
             jrnl_names_allocs := γallocs;
          |}).
  iExists (jrnl_update_pre _ names).
  iFrame. iModIntro. iFrame "% #".
  rewrite assoc.
  iSplitL "H".
  { by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp. }
  rewrite /jrnl_state_start.
  rewrite big_sepM_fmap.
  iFrame.
  iDestruct (big_sepM.big_sepM_mono_with_inv with "Hkinds Hdata") as "(_&$)".
  iIntros (a x Hlookup) "(#Hkinds&Hpt)". iFrame "Hkinds".
  rewrite /jrnl_mapsto.
  rewrite /wf_jrnl/offsets_aligned/sizes_correct in Hwf.
  destruct Hwf as (Hoff&Hsize).
  edestruct Hsize as (k&Hlookup_kind&Hlen); eauto. iFrame.
  iExists _. iFrame "% #".
  iPureIntro. exists k.
  split_and!; eauto.
  edestruct (Hoff a); eauto.
  { apply elem_of_dom. eauto. }
  naive_solver.
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
    iMod (map_init_many ((λ _, tt) <$> jrnlData s)) as (γcrash) "(Hcrash_ctx&Hcrash)".
    iMod (ghost_var_alloc ()) as (γfull) "Hfull".
    iMod (map_init_many ∅) as (γallocs) "(Hallocs_ctx&_)".
    iExists (jrnl_update _ {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) ;
               jrnl_names_crash := γcrash;
               jrnl_names_full_crash := γfull;
               jrnl_names_allocs := γallocs;
            |}).
    iDestruct "Hinterp" as "(?&Hstate)".
    iDestruct (jrnl_state_ctx_extract_pers with "Hstate") as "(%&#?&#?)".
    iDestruct "Hstate" as "(?&?&?&?&?)".
    rewrite //=/jrnl_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first by eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    rewrite big_sepM_fmap.
    rewrite /jrnl_state_restart.
    rewrite /jrnl_crash_tok.
    rewrite /jrnl_full_crash_tok.
    rewrite //= /=. iFrame "# ∗".
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree tt) : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iMod (map_init_many ((λ _, tt) <$> jrnlData s)) as (γcrash) "(Hcrash_ctx&Hcrash)".
    iMod (ghost_var_alloc ()) as (γfull) "Hfull".
    iMod (map_init_many ∅) as (γallocs) "(Hallocs_ctx&_)".
    iExists (jrnl_update _ {| jrnl_names_open := γ1;
               jrnl_names_data := jrnl_names_data (jrnl_get_names _);
               jrnl_names_kinds := jrnl_names_kinds (jrnl_get_names _) ;
               jrnl_names_crash := γcrash;
               jrnl_names_allocs := γallocs;
            |}).
    iDestruct "Hinterp" as "(?&Hstate)".
    iDestruct (jrnl_state_ctx_extract_pers with "Hstate") as "(%&#?&#?)".
    rewrite //=/jrnl_restart//=.
    iDestruct "Hstate" as "(?&?&?&?&?)".
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /jrnl_closed_auth/jrnl_closed_frag.
    rewrite big_sepM_fmap.
    rewrite /jrnl_state_restart.
    rewrite /jrnl_crash_tok.
    rewrite /jrnl_full_crash_tok.
    rewrite //=. iFrame "# ∗".
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance jrnl_spec_ext : spec_ffi_op := {| spec_ffi_op_field := jrnl_op |}.
Instance jrnl_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := jrnl_model |}.
Instance jrnl_spec_ext_semantics : spec_ext_semantics (jrnl_spec_ext) (jrnl_spec_ffi_model) :=
  {| spec_ext_semantics_field := jrnl_semantics |}.
Instance jrnl_spec_ffi_interp : spec_ffi_interp jrnl_spec_ffi_model :=
  {| spec_ffi_interp_field := jrnl_interp |}.
Instance jrnl_spec_ty : ext_types (spec_ffi_op_field) := jrnl_ty.
Instance jrnl_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := jrnl_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := jrnl_interp_adequacy |}.

Context `{invGS Σ}.
Context `{crashGS Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ffi_op_field.
Existing Instance spec_ffi_model_field.

Implicit Types K: spec_lang.(language.expr) → spec_lang.(language.expr).
Instance jrnlG0 : jrnlG Σ := refinement_spec_ffiLocalGS.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | [ H1: context[ match world ?σ with | _ => _ end ], Heq: world ?σ = _ |- _ ] =>
          rewrite Heq in H1
        end.

Notation spec_ext := jrnl_spec_ext.
Notation sstate := (@state (@spec_ffi_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field spec_ext)).
Notation sval := (@val (@spec_ffi_op_field spec_ext)).
Notation shead_step := (@head_step (@spec_ffi_op_field spec_ext)).
Notation sworld := (@world (@spec_ffi_op_field spec_ext) (@spec_ffi_model_field jrnl_spec_ffi_model)).

Definition jrnl_sub_dom (σj1 σj2 : jrnl_map) : Prop :=
  (dom (gset _) (jrnlData σj1) = dom _ (jrnlData σj2) ∧ jrnlKinds σj1 ⊆ jrnlKinds σj2 ∧
   jrnlAllocs σj1 = jrnlAllocs σj2 ∧
  wf_jrnl σj1 ∧ wf_jrnl σj2).

Definition jrnl_sub_state (σj : jrnl_map) (s: sstate) : Prop :=
  (∃ sj, s.(world) = Opened sj ∧ jrnlData σj ⊆ jrnlData sj ∧ jrnlKinds σj = jrnlKinds sj ∧ jrnlAllocs σj ⊆ jrnlAllocs sj).

Definition jrnl_upd (σj: jrnl_map) (s: sstate) : sstate :=
  set sworld (λ s, Opened {| jrnlData := jrnlData σj ∪ (jrnlData $ get_jrnl s);
                             jrnlKinds := jrnlKinds $ get_jrnl s;
                             jrnlAllocs := jrnlAllocs $ (get_jrnl s) |}) s.

Definition jrnl_upd_allocs (σj: jrnl_map) (s: sstate) : sstate :=
  set sworld (λ s, Opened {| jrnlData := jrnlData σj;
                             jrnlKinds := jrnlKinds $ get_jrnl s;
                             jrnlAllocs := jrnlAllocs σj ∪ (jrnlAllocs $ get_jrnl s) |}) s.

(* This definition captures the idea that an expression e (may) transition to e'
   with zero or more steps, starting from *any* state whose journal contains σj
   as a submap. At the end of this execution, the final state is guaranteed to
   be the same, except that this submap of the journal is now updated to σj'.

   The refinement proof for two phase locking works by incrementally building up
   a proof of `always_steps` as it executes the code in an Atomically
   block. Crucially, the subset of locked addresses will correspond to the σj
   argument of this `always_steps` execution.  *)

Definition always_steps (e: sexpr) (σj: jrnl_map) (e': sexpr) (σj': jrnl_map) : Prop :=
  (jrnlKinds σj = jrnlKinds σj') ∧
  (jrnl_sub_dom σj σj') ∧
  (∀ s g, jrnl_sub_state σj s →
           rtc (λ '(e, (s,g)) '(e', (s',g')), prim_step' e s g [] e' s' g' []) (e, (s,g)) (e', (jrnl_upd σj' s, g))).

Lemma jrnl_upd_sub σj s :
  jrnl_sub_state σj s →
  jrnl_upd σj s = s.
Proof.
  intros (sj&Heq1&Hsub1&Hsub2).
  rewrite /jrnl_upd.
  destruct s. rewrite /set//=. f_equal.
  rewrite /= in Heq1. rewrite Heq1. f_equal. destruct sj as [sjd [sjk sja]].
  f_equal => /=. apply map_subseteq_union; auto.
Qed.

Lemma jrnl_sub_state_upd σj1 σj2 s :
  jrnl_sub_state σj1 s →
  jrnlKinds σj1 = jrnlKinds σj2 →
  jrnlAllocs σj1 = jrnlAllocs σj2 →
  jrnl_sub_state σj2 (jrnl_upd σj2 s).
Proof.
  intros (sj&Heq&Hsub_data&Hsub_kinds&Hsub_allocs) Heq_kinds Heq_allocs.
  eexists; split; eauto => /=.
  split_and!.
  - apply map_union_subseteq_l.
  - rewrite Heq /= -Heq_kinds //.
  - rewrite Heq /= -Heq_allocs //.
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
  wf_jrnl σj →
  always_steps e σj e σj.
Proof.
  intros. split_and! => //= s g Hsub.
  rewrite jrnl_upd_sub //.
Qed.

Lemma jrnl_sub_dom_trans σj1 σj2 σj3 :
  jrnl_sub_dom σj1 σj2 →
  jrnl_sub_dom σj2 σj3 →
  jrnl_sub_dom σj1 σj3.
Proof.
  intros (?&?&?&?&?) (?&?&?&?&?); split_and!; eauto.
  - congruence.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Lemma always_steps_trans e1 σj1 e2 σj2 e3 σj3 :
  always_steps e1 σj1 e2 σj2 →
  always_steps e2 σj2 e3 σj3 →
  always_steps e1 σj1 e3 σj3.
Proof.
  intros (Hkinds1&Hsub1&Hsteps1) (Hkinds2&Hsub2&Hsteps2).
  split_and!; first congruence.
  { eapply jrnl_sub_dom_trans; eassumption. }
  intros s g Hsub.
  eapply rtc_transitive.
  { eapply Hsteps1; eauto. }
  { assert (jrnl_upd σj3 s = jrnl_upd σj3 (jrnl_upd σj2 s)) as ->.
    { rewrite jrnl_upd_upd_sub_dom; eauto. }
    eapply Hsteps2; eauto.
    eapply jrnl_sub_state_upd; eauto.
    { destruct Hsub1 as (?&?&?&?).
      destruct Hsub2 as (?&?&?&?). congruence. }
  }
Qed.

Lemma insert_jrnl_upd a o σj s :
  a ∉ dom (gset _) (jrnlData σj) →
  jrnl_upd (updateData σj a o) s =
  jrnl_upd σj (jrnl_upd ({| jrnlData := {[ a := o]};
                           jrnlKinds := jrnlKinds σj;
                           jrnlAllocs := jrnlAllocs σj|}) s).
Proof.
  intros.
  rewrite /jrnl_upd/set/=. do 3 f_equal.
  rewrite insert_union_singleton_l.
  rewrite (map_union_comm ({[a := o]})) ?assoc //.
  apply map_disjoint_dom_2.
  rewrite dom_singleton. set_solver.
Qed.

Lemma insert_jrnl_upd_allocs a o σj s :
  a ∉ dom (gset _) (jrnlAllocs σj) →
  jrnl_upd_allocs (updateAllocs σj a o) s =
  jrnl_upd_allocs σj (jrnl_upd_allocs ({| jrnlData := jrnlData σj;
                           jrnlKinds := jrnlKinds σj;
                           jrnlAllocs := {[ a := o ]}|}) s).
Proof.
  intros.
  rewrite /jrnl_upd_allocs/set/=. do 3 f_equal.
  rewrite insert_union_singleton_l.
  rewrite (map_union_comm ({[a := o]})) ?assoc //.
  apply map_disjoint_dom_2.
  rewrite dom_singleton. set_solver.
Qed.

Lemma always_steps_bind `{Hctx: LanguageCtx' (ext := @spec_ffi_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K} e1 e2 σj1 σj2 :
  always_steps e1 σj1 e2 σj2 →
  always_steps (K e1) σj1 (K e2) σj2.
Proof.
  rewrite /always_steps.
  intros (?&?&Hstep). split_and!; eauto.
  intros s g Hsub. specialize (Hstep _ g Hsub).
  clear -Hstep Hctx.
  remember (e1, (s,g)) as ρ1 eqn:Hρ1.
  remember (e2, (jrnl_upd σj2 s,g)) as ρ2 eqn:Hρ2.
  revert Hρ1 Hρ2. destruct g.
  generalize (jrnl_upd σj2 s) as s'.
  revert e1 e2 s.
  induction Hstep.
  - intros. rewrite Hρ1 in Hρ2. inversion Hρ2. subst.
    apply rtc_refl.
  - intros. subst. destruct y as (e0'&s0'&[]).
    eapply rtc_l; last first.
    { eapply IHHstep; eauto. }
    simpl. eapply fill_step'. eauto.
Qed.

Lemma insert_jrnl_sub_state a o σj s:
  jrnl_sub_state (updateData σj a o ) s →
  s = (jrnl_upd ({| jrnlData := {[ a := o]};
                           jrnlKinds := jrnlKinds σj;
                           jrnlAllocs := jrnlAllocs σj|}) s).
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

Lemma wf_jrnl_extend σj a o:
  size_consistent_and_aligned a o (jrnlKinds σj) →
  wf_jrnl σj →
  wf_jrnl (updateData σj a o).
Proof.
  intros Haligned Hwf. rewrite /wf_jrnl.
  split.
  - rewrite /offsets_aligned => a' Hin.
    rewrite dom_insert_L in Hin. set_unfold in Hin. destruct Hin; subst.
    * simpl. destruct Haligned. naive_solver.
    * eapply Hwf; eauto.
  - rewrite /sizes_correct => a' Hin Hlookup.
    destruct (decide (a' = a)).
    { subst. rewrite lookup_insert in Hlookup. destruct Haligned. naive_solver. }
    rewrite lookup_insert_ne in Hlookup; auto.
    eapply Hwf; eauto.
Qed.

Lemma always_steps_extend e1 σj1 e2 σj2 a o :
  (a ∉ dom (gset _) (jrnlData σj2)) →
  size_consistent_and_aligned a o (jrnlKinds σj1) →
  always_steps e1 σj1 e2 σj2 →
  always_steps e1 (updateData σj1 a o)
               e2 (updateData σj2 a o).
Proof.
  intros Hdom Hconsistent (?&Hsub&Hstep).
  split_and!.
  - simpl. congruence.
  - destruct Hsub as (?&?&?&?&?). split_and! => //=.
    * rewrite ?dom_insert_L H2. set_solver.
    * apply wf_jrnl_extend; auto.
    * apply wf_jrnl_extend; auto. congruence.
  - intros s g Hsub_state.
    rewrite insert_jrnl_upd //.
    rewrite {1}(insert_jrnl_sub_state _ _ _ _ Hsub_state).
    apply Hstep.
    rewrite /jrnl_sub_state.
    destruct Hsub_state as (sj&Hworld&Hsub_data&?&Hsub_allocs).
    rewrite /jrnl_upd/set//=. rewrite Hworld /=.
    eexists; split_and!; eauto => /=.
    intros i => /=.
    specialize (Hsub_data i).
    destruct Hsub as (Hsub_data'&?).
    assert (a ∉ dom (gset _) (jrnlData σj1)) as Hdom' by (rewrite Hsub_data'; set_solver).
    destruct (decide (a = i)).
    * subst. apply not_elem_of_dom in Hdom'.
      rewrite Hdom' => //=. destruct (({[ i := o]} ∪ jrnlData sj) !! i) eqn:Heq; auto.
    * rewrite lookup_union_r ?lookup_singleton_ne //.
      rewrite lookup_insert_ne // in Hsub_data.
Qed.

Lemma always_steps_extend_allocs1 e1 σj1 e2 σj2 l u :
  (l ∉ dom (gset _) (jrnlAllocs σj2)) →
  always_steps e1 σj1 e2 σj2 →
  always_steps e1 (updateAllocs σj1 l u)
               e2 (updateAllocs σj2 l u).
Proof.
  intros Hdom (?&Hsub&Hstep).
  split_and!.
  - simpl. congruence.
  - destruct Hsub as (?&?&Ha&?&?). split_and! => //=.
    * rewrite ?dom_insert_L Ha. set_solver.
  - intros s g Hsub_state.
    assert (jrnl_upd (updateAllocs σj2 l u) s =
            jrnl_upd σj2 s) as ->.
    { rewrite /jrnl_upd/updateAllocs //=. }
    apply Hstep.
    rewrite /jrnl_sub_state.
    destruct Hsub_state as (sj&Hworld&Hsub_data&?&Hsub_allocs).
    rewrite /jrnl_upd/set//=. rewrite Hworld /=.
    eexists; split_and!; eauto => /=.
    intros i => /=.
    specialize (Hsub_allocs i).
    destruct Hsub as (Hsub_data'&?&Hsub_alloc'&?).
    assert (l ∉ dom (gset _) (jrnlAllocs σj1)) as Hdom' by (rewrite Hsub_alloc'; set_solver).
    destruct (decide (l = i)).
    * subst. apply not_elem_of_dom in Hdom'.
      rewrite Hdom' => //=. destruct ((jrnlAllocs sj) !! i) eqn:Heq; auto.
    * subst. rewrite /updateAllocs /= in Hsub_allocs.
      rewrite lookup_insert_ne // in Hsub_allocs.
Qed.

Lemma always_steps_extend_allocs2 e1 σj1 e2 σj2 l u :
  (l ∉ dom (gset _) (jrnlAllocs σj1) ∨ jrnlAllocs σj1 !! l = Some u) →
  always_steps e1 σj1 e2 σj2 →
  always_steps e1 (updateAllocs σj1 l u)
               e2 (updateAllocs σj2 l u).
Proof.
  intros [Hdom|Hlookup] Halways_steps. (* (?&Hsub&Hstep). *)
  { eapply always_steps_extend_allocs1; eauto.
    destruct Halways_steps as (?&Hsub&?).
    destruct Hsub as (?&?&<-&?); eauto.
  }
  assert (updateAllocs σj1 l u = σj1) as ->.
  { rewrite /updateAllocs//=; destruct σj1 => //=; f_equal.
    rewrite insert_id //. }
  assert (updateAllocs σj2 l u = σj2) as ->.
  {
    destruct Halways_steps as (?&Hsub&?).
    destruct Hsub as (?&?&HeqAllocs&?); eauto.
    rewrite HeqAllocs in Hlookup.
    rewrite /updateAllocs//=; destruct σj2 => //=; f_equal.
    rewrite insert_id //.
  }
  eauto.
Qed.

Definition addr2val' (a : addr) : sval := (#(addrBlock a), (#(addrOff a), #()))%V.

Lemma always_steps_lifting_puredet K `{Hctx: LanguageCtx' (ext := @spec_ffi_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K}:
  ∀ e0 σ0 e1 σ1 e2,
  (∀ σ g, prim_step' e1 σ g [] e2 σ g []) →
  always_steps e0 σ0 (K e1) σ1 →
  always_steps e0 σ0 (K e2) σ1.
Proof.
  intros e0 σ0 e1 σ1 e2 Hdet Hsteps.
  split_and!; eauto.
  { eapply Hsteps. }
  { eapply Hsteps. }
  intros s g Hsub.
  destruct Hsteps as (?&?&Hrtc).
  specialize (Hrtc _ g Hsub).
  eapply rtc_r; eauto.
  simpl. eapply fill_step'. eapply Hdet.
Qed.

Lemma always_steps_MarkUsedOp l n max σj:
  wf_jrnl σj →
  jrnlAllocs σj !! l = Some max →
  (int.Z n < int.Z max) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           MarkUsedOp
                           (PairV #(LitLoc l) #(LitInt n)))
               σj
               #()
               σj.
Proof.
  intros Hwf Hlookup Hmax.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup.
    eapply lookup_weaken in Hlookup; last eassumption.
    rewrite Hlookup. econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite decide_True //=. }
Qed.

Lemma always_steps_FreeNumOp l n max σj:
  wf_jrnl σj →
  jrnlAllocs σj !! l = Some max →
  (int.Z n ≠ 0 ∧ int.Z n < int.Z max) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           FreeNumOp
                           (PairV #(LitLoc l) #(LitInt n)))
               σj
               #()
               σj.
Proof.
  intros Hwf Hlookup Hmax.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup.
    eapply lookup_weaken in Hlookup; last eassumption.
    rewrite Hlookup. econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite decide_True //=. }
Qed.

Lemma always_steps_AllocOp l n max σj:
  wf_jrnl σj →
  jrnlAllocs σj !! l = Some max →
  (0 < int.Z max ∧ int.Z n < int.Z max) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           AllocOp
                           #(LitLoc l))
               σj
               #(LitInt n)
               σj.
Proof.
  intros Hwf Hlookup (Hgt0&Hmax).
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup.
    eapply lookup_weaken in Hlookup; last eassumption.
    rewrite Hlookup. econstructor; eauto. }
  { rewrite /checkPf. rewrite decide_True_pi //=. }
Qed.

Lemma always_steps_NumFreeOp l n max σj:
  wf_jrnl σj →
  jrnlAllocs σj !! l = Some max →
  (int.Z n ≤ int.Z max) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           NumFreeOp
                           #(LitLoc l))
               σj
               #(LitInt n)
               σj.
Proof.
  intros Hwf Hlookup Hmax.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup.
    eapply lookup_weaken in Hlookup; last eassumption.
    rewrite Hlookup. econstructor; eauto. }
Qed.

Lemma always_steps_ReadBufOp a v (sz: u64) k σj:
  wf_jrnl σj →
  jrnlData σj !! a = Some v →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (k ≠ KindBit ∧ bufSz k = int.nat sz) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           ReadBufOp
                           (PairV (addr2val' a) #sz))
               σj
               (val_of_obj' v)
               σj.
Proof.
  intros Hwf Hlookup1 Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite -H2. rewrite Hlookup2; eauto.
    econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite decide_True //=. }
Qed.

Lemma always_steps_ReadBitOp a v σj:
  wf_jrnl σj →
  jrnlData σj !! a = Some v →
  jrnlKinds σj !! (addrBlock a) = Some KindBit →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           ReadBitOp
                           (addr2val' a))
               σj
               (val_of_obj' v)
               σj.
Proof.
  intros Hwf Hlookup1 Hlookup2.
  split_and!; eauto.
  { split_and!; try set_solver. }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite jrnl_upd_sub // /head_step//=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite -H2. rewrite Hlookup2; eauto.
    econstructor; eauto. }
  { rewrite /check/ifThenElse. rewrite //=. }
Qed.

Lemma val_of_obj'_bytes vs: val_of_obj' (objBytes vs) = val_of_list ((λ u : u8, #u) <$> vs).
Proof. rewrite //=. Qed.

Lemma val_of_obj'_bit (vs : bool) : val_of_obj' (objBit vs) = #vs.
Proof. rewrite //=. Qed.

Lemma wf_jrnl_updateData σj a vs vs_old k :
  wf_jrnl σj →
  jrnlData σj !! a = Some vs_old →
  jrnlKinds σj !! addrBlock a = Some k →
  objSz vs = bufSz k →
  wf_jrnl (updateData σj a vs).
Proof.
  intros Hwf Hlookup1 Hlookup2 Hsize.
  split.
  - rewrite /offsets_aligned => a' Hin.
    eapply Hwf. move: Hin. rewrite dom_insert_L.
    cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
    apply elem_of_dom. eauto.
  - rewrite /sizes_correct//= => a' o Hlookup'.
    destruct (decide (a' = a)).
    * subst. eexists; split; eauto. rewrite lookup_insert in Hlookup'. congruence.
    * eapply Hwf. rewrite lookup_insert_ne in Hlookup'; eauto.
Qed.

Lemma always_steps_OverWriteOp a vs k σj:
  wf_jrnl σj →
  is_Some (jrnlData σj !! a)  →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (objSz (objBytes vs) = bufSz k ∧ k ≠ KindBit) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           OverWriteOp
                           (PairV (addr2val' a) (val_of_obj' (objBytes vs))))
               σj
               #()
               (updateData σj a (objBytes vs)).
Proof.
  intros Hwf (vs_old&Hlookup1) Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver.
    - rewrite //=. rewrite dom_insert_L.
      cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
      apply elem_of_dom. eauto.
    - eapply wf_jrnl_updateData; eauto. naive_solver.
  }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite H2 in Hlookup2.
    rewrite Hlookup2. econstructor; eauto. }
  { eapply val_of_obj'_bytes. }
  { rewrite /check/ifThenElse.
    rewrite decide_True; auto.
    { repeat econstructor. }
  }
  { rewrite //= Heq. repeat econstructor. }
  { rewrite //=. do 2 f_equal.
    rewrite /jrnl_upd //=. rewrite /set. destruct s => //=.
    do 2 f_equal. rewrite /updateData. rewrite /= in Heq.
    subst => //=. repeat f_equal.
    rewrite -insert_union_l.
    rewrite map_subseteq_union //.
  }
Qed.

Lemma always_steps_OverWriteBitOp a b k σj:
  wf_jrnl σj →
  is_Some (jrnlData σj !! a)  →
  jrnlKinds σj !! (addrBlock a) = Some k →
  (objSz (objBit b) = bufSz k ∧ k = KindBit) →
  always_steps (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                           OverWriteBitOp
                           (PairV (addr2val' a) (val_of_obj' (objBit b))))
               σj
               #()
               (updateData σj a (objBit b)).
Proof.
  intros Hwf (vs_old&Hlookup1) Hlookup2 Hk.
  split_and!; eauto.
  { split_and!; try set_solver.
    - rewrite //=. rewrite dom_insert_L.
      cut (a ∈ dom (gset _) (jrnlData σj)); first by set_solver.
      apply elem_of_dom. eauto.
    - eapply wf_jrnl_updateData; eauto. naive_solver.
  }
  intros s g Hsub.
  apply rtc_once.
  eapply (Ectx_step' _ _ _ _ _ _ _ _ []) => //=.
  rewrite /jrnl_sub_state in Hsub.
  destruct Hsub as (?&Heq&?&?&?).
  destruct a as (ablk&aoff).
  econstructor; last econstructor; eauto.
  econstructor; repeat (econstructor; eauto).
  { simpl. rewrite Heq. econstructor. eauto. }
  { simpl in Hlookup1.
    eapply lookup_weaken in Hlookup1; last eassumption.
    rewrite Hlookup1. econstructor; eauto. }
  { simpl in Hlookup2.
    rewrite H2 in Hlookup2.
    rewrite Hlookup2. econstructor; eauto. }
  {
    eapply val_of_obj'_bit. }
  { rewrite /check/ifThenElse.
    rewrite decide_True; auto.
    { repeat econstructor. }
  }
  { rewrite //= Heq. repeat econstructor. }
  { rewrite //=. do 2 f_equal.
    rewrite /jrnl_upd //=. rewrite /set. destruct s => //=.
    do 2 f_equal. rewrite /updateData. rewrite /= in Heq.
    subst => //=. repeat f_equal.
    rewrite -insert_union_l.
    rewrite map_subseteq_union //.
  }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ g (v : sval):
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ jrnl_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp v) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ g -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ??????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)) eqn:Heq; try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
  }
  { solve_ndisj. }
Qed.

Lemma jrnl_opened_open_false E j K {HCTX: LanguageCtx K} (v : sval):
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_open -∗
  j ⤇ K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp v) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma jrnl_open_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'} (v: sval) :
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp v) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp v) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
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

Lemma ghost_step_jrnl_open E j K {HCTX: LanguageCtx K} (v: sval):
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_closed_frag -∗
  j ⤇ K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) OpenOp v)
  -∗ |NC={E}=> j ⤇ K #true%V ∗ jrnl_open.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_unify_closed with "[$] [$]") as %(σj&Heq).
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl. econstructor.
    * repeat econstructor => //=.
      rewrite Heq.
      repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (jrnl_closed_token_open with "[$] [$]") as "#Hopen".
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen". }
  iModIntro. iFrame "Hopen". iFrame.
Qed.

Lemma jrnl_ctx_sub_state_valid' σj s :
  (∀ sj, (s.(world) : @ffi_state jrnl_model) ≠ Closed sj) →
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ jrnl_sub_state σj s ⌝.
Proof.
  iIntros (?) "Hpts #Hkinds #Hallocs Hctx".
  rewrite /jrnl_sub_state.
  destruct (s.(world)) as [|sj] eqn:Heq_world; first by congruence.
  iExists _. iSplit; first eauto.
  iSplit; [| iSplit].
  - iIntros (a). destruct (jrnlData σj !! a) as [o|] eqn:Heq'.
    { rewrite /=. iDestruct (big_sepM_lookup with "Hpts") as "H"; eauto.
      rewrite /jrnl_ctx. rewrite /jrnl_state_ctx. iDestruct "Hctx" as "(_&_&Hctx1&Hctx2)".
      iDestruct "H" as "(?&?)".
      iDestruct (map_valid with "Hctx1 [$]") as %->; eauto.
    }
    { rewrite /=. destruct (jrnlData sj !! _); eauto. }
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom)".
    iDestruct (own_valid_2 with "Hkinds Hctx2") as %Hval.
    apply to_agree_op_valid in Hval. iPureIntro. set_solver.
  - iDestruct "Hctx" as "(_&Hctx)". iApply (jrnl_ctx_allocs_agree with "[$] [$]"); eauto.
Qed.

Lemma jrnl_ctx_dom_eq σj (s: sstate) :
  jrnl_dom (σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ dom (gset addr) (jrnlData (get_jrnl s.(world))) = σj ⌝.
Proof.
  iIntros "#Hdom Hctx".
  rewrite /jrnl_sub_state.
  rewrite /jrnl_ctx.
  destruct (s.(world)) as [sj|sj] eqn:Heq_world.
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom'&?)".
    iDestruct (jrnl_dom_agree with "[$] [$]") as %Heq; eauto.
  - iDestruct "Hctx" as "(_&_&Hctx1&Hctx2&Hdom'&?)".
    iDestruct (jrnl_dom_agree with "[$] [$]") as %Heq; eauto.
Qed.

Lemma jrnl_ctx_sub_state_valid σj s :
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_open -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_ctx s.(world) -∗
  ⌜ jrnl_sub_state σj s ⌝.
Proof.
  iIntros "Hpts #Hkinds #Hopen #Halloc Hctx".
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %[sj Heq].
  iApply (jrnl_ctx_sub_state_valid' with "[$] [$] [$] [$]").
  congruence.
Qed.

Lemma offsets_aligned_delete i σjd σjk σja :
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  offsets_aligned {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros Hoa k Hin. eapply Hoa.
  set_solver.
Qed.

Lemma sizes_correct_delete i σjd σjk σja :
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  sizes_correct {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros Hoa k Hin Hlookup. eapply Hoa.
  rewrite /=.
  eapply lookup_delete_Some; eauto.
Qed.

Lemma wf_jrnl_delete i σjd σjk σja :
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  wf_jrnl {| jrnlData := (delete i σjd); jrnlKinds := σjk; jrnlAllocs := σja |}.
Proof.
  intros (?&?).
  split; eauto using offsets_aligned_delete, sizes_correct_delete.
Qed.

Lemma offsets_aligned_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  offsets_aligned {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros Hsub Hoa i Hin. edestruct Hoa as (k&?&?); eauto.
  exists k; split_and!; eauto. rewrite /=.
  eapply lookup_weaken; eauto.
Qed.

Lemma sizes_correct_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  sizes_correct {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros Hsub Hoa i ? Hin. edestruct Hoa as (k&?&?); eauto.
  exists k; split_and!; eauto. rewrite /=.
  eapply lookup_weaken; eauto.
Qed.

Lemma wf_jrnl_mono_kinds σjd σjk σjk' σja :
  σjk ⊆ σjk' →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk'; jrnlAllocs := σja |}.
Proof.
  intros ? (?&?).
  split; eauto using offsets_aligned_mono_kinds, sizes_correct_mono_kinds.
Qed.

Lemma wf_jrnl_lookup_size_consistent_and_aligned σjd σjk σja i o :
  σjd !! i = Some o →
  wf_jrnl {| jrnlData := σjd; jrnlKinds := σjk; jrnlAllocs := σja |} →
  size_consistent_and_aligned i o σjk.
Proof.
  intros Hlookup (Hoa&Hsizes).
  edestruct Hsizes as (k&?&?); eauto.
  exists k; split_and!; eauto.
  edestruct (Hoa i) as (k'&?&?).
  { apply elem_of_dom; eauto. }
  congruence.
Qed.

Lemma jrnl_ctx_upd σj σjd' σjk σja s :
  wf_jrnl {| jrnlData := σjd'; jrnlKinds := σjk; jrnlAllocs := σja |} →
  dom (gset _) (jrnlData σj) = dom (gset _) σjd' →
  jrnl_open -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds σjk -∗
  jrnl_alloc_map σja -∗
  jrnl_ctx s.(world) ==∗
  ([∗ map] a ↦ o ∈ (σjd'), jrnl_mapsto a 1 o) ∗
  jrnl_ctx (jrnl_upd {| jrnlData := σjd'; jrnlKinds := σjk; jrnlAllocs := σja |} s).(world).
Proof.
  iIntros (Hwf Hdom) "#Hopen Hpts #Hkinds #Hallocs Hctx".
  iDestruct (jrnl_ctx_unify_opened with "[$] [$]") as %[sj Heq].
  iDestruct (jrnl_ctx_sub_state_valid {| jrnlData := jrnlData σj; jrnlKinds := σjk; jrnlAllocs := σja |}
     with "Hpts Hkinds [$] [$] [$]") as %Hval.
  rewrite /jrnl_ctx. rewrite Heq.
  iDestruct "Hctx" as "(_&Hstate)".
  iDestruct "Hstate" as (Hwf0) "(Hctx&Hkinds'&Hdom'&Halloc_ctx)". simpl.
  assert (Hdom_sub: dom (gset _) (jrnlData σj) ⊆ dom (gset _) (jrnlData sj)).
  { rewrite /jrnl_sub_state/sworld in Hval.
    destruct Hval as (?&Heq'&?&?). rewrite /world in Heq. rewrite Heq in Heq'.
    inversion Heq'; subst.
    apply subseteq_dom. eauto. }
  clear Hval.
  rewrite /jrnl_state_ctx/=.
  iAssert (jrnl_dom (dom (gset addr) (σjd' ∪ jrnlData (get_jrnl s.(world))))) with "[Hdom']" as "$".
  { rewrite Heq /= dom_union_L.
    assert (dom (gset addr) σjd' ∪ dom (gset addr) (jrnlData sj) =
            dom (gset addr) (jrnlData sj)) as ->.
    { rewrite -Hdom. set_solver. }
    eauto. }
  clear Hdom_sub.
  iInduction (jrnlData σj) as [| i x m] "IH" using map_ind forall (σjd' Hwf Hdom).
  - rewrite dom_empty_L in Hdom.
    symmetry in Hdom. apply dom_empty_iff_L in Hdom.
    rewrite ?Hdom big_sepM_empty. iFrame.
    rewrite /=. rewrite left_id_L //=. rewrite Heq => //=. iFrame. eauto.
  - assert (Hin: i ∈ dom (gset _) σjd').
    { rewrite -Hdom. rewrite dom_insert_L. set_solver. }
    apply elem_of_dom in Hin.
    destruct Hin as (o&Hin).
    rewrite (big_sepM_delete _ σjd'); eauto.
    rewrite big_sepM_insert; eauto.
    iDestruct "Hpts" as "(Hmaps&Hpts)".
    iMod ("IH" with "[] [] Hpts [$] [$] [$]") as "($&Hctx)".
    { iPureIntro. apply wf_jrnl_delete; auto. }
    { iPureIntro. rewrite dom_insert_L in Hdom. rewrite dom_delete_L.
      apply not_elem_of_dom in H1. set_solver. }
    iDestruct "Hctx" as "($&Hstate)".
    iDestruct "Hstate" as (Hwf') "(Hctx&Hkinds'&Halloc_ctx)".
    iDestruct "Hmaps" as "(Hmaps&Hkind)".
    iDestruct "Hkind" as (? Hconsistent) "Hkind".
    iMod (map_update _ _ o with  "[$] [$]") as "(Hctx&?)".
    iDestruct (own_valid_2 with "Hkind Hkinds'") as %Hval.
    apply to_agree_op_valid, leibniz_equiv in Hval. rewrite /= in Hval.
    iDestruct (own_valid_2 with "Hkinds' Hkinds") as %Hval2.
    apply to_agree_op_valid, leibniz_equiv in Hval2. rewrite /= in Hval2.
    subst.
    iFrame. simpl.
    rewrite insert_union_l.
    rewrite insert_delete //.
    iFrame.
    assert (size_consistent_and_aligned i o (jrnlKinds (get_jrnl s.(world)))).
    {
      eapply wf_jrnl_lookup_size_consistent_and_aligned; eauto.
    }
    iModIntro; iSplit; auto.
    { iPureIntro. eapply wf_jrnl_extend in Hwf'; last eauto.
      rewrite /updateData//= in Hwf'.
      rewrite /= insert_union_l insert_delete in Hwf'; eauto.
    }
Qed.

Lemma ghost_step_jrnl_atomically_abort E j K {HCTX: LanguageCtx K} (l: sval) e :
  nclose sN ⊆ E →
  spec_ctx -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |NC={E}=>
  j ⤇ K NONEV.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopen Hj".
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iMod (ghost_step_stuck' with "[$] [$] [$]") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod (ghost_step_lifting _ _ _ _ _ _ [] _ _ _ [] with "[$] [$] [$]") as "($&Hstate'&_)".
  { apply head_prim_step. eapply head_step_atomically_fail.
    eapply atomically_not_stuck_body_safe; eauto. }
  { solve_ndisj. }
  iMod ("Hclo" with "[-]") as "_".
  { iNext. iExists _, _. iFrame. }
  iModIntro. eauto.
Qed.

Lemma ghost_step_jrnl_atomically E j K {HCTX: LanguageCtx K} (l: sval) e σj (v: sval) σj' :
  always_steps e σj (SOMEV v) σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |NC={E}=>
  j ⤇ K (SOMEV v) ∗ ([∗ map] a ↦ o ∈ (jrnlData σj'), jrnl_mapsto a 1 o).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_allocs Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iMod (ghost_step_stuck' with "[$] [$] [$]") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod (ghost_step_lifting _ _ _ (Atomically l e) s g [] (jrnl_upd σj' s) g (SOMEV v) []
          with "Hj Hctx H") as "(Hj&H&_)".
  { destruct g. apply head_prim_step.
    apply head_step_atomically; eauto.
    eapply atomically_not_stuck_body_safe; eauto.
  }
  { solve_ndisj. }
  iMod (jrnl_ctx_upd _ (jrnlData σj') _ (jrnlAllocs σj) with "[$] [$] [$] [$] [$]") as "(Hσj'_data&Hffi)".
  { destruct Hwf as (?&?&?&?&?). rewrite Heq_kinds; eauto. }
  { destruct Hwf as (?&?&?&?&?). eauto. }
  iMod ("Hclo" with "[Hσ Hrest H Hffi]") as "_".
  { iNext. iExists _, _. iFrame "H". iFrame. }
  iModIntro. iFrame.
Qed.

Lemma ghost_step_jrnl_atomically_crash E j K {HCTX: LanguageCtx K} (l: sval) e σj (v: sval) σj' :
  always_steps e σj (SOMEV v) σj' →
  nclose sN ⊆ E →
  spec_crash_ctx (jrnl_crash_ctx) -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  ([∗ map] a ↦ _ ∈ (jrnlData σj), jrnl_crash_tok a) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e)
  -∗ |C={E}_0=>
    ([∗ map] a ↦ o ∈ (jrnlData σj'), jrnl_mapsto a 1 o) ∗
    ([∗ map] a ↦ _ ∈ (jrnlData σj), jrnl_crash_tok a).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_crash_toks Hσj_kinds Hσj_allocs Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iMod (cfupd_weaken_all with "Hstate") as "#Hstate'"; eauto.
  { solve_ndisj. }
  iInv "Hstate'" as "[>Hbad|Hrest]" "Hclo".
  { iIntros "HC".
    destruct Hwf as (Hdom&?).
    iDestruct "Hbad" as (?) "(Htok&Hcrash_ctx&Hfull_tok)".
    induction (jrnlData σj) as [| x v' ? ? _] using map_ind.
    { rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_iff_L in Hdom. rewrite Hdom.
      rewrite ?big_sepM_empty. iMod ("Hclo" with "[-]").
      { iLeft. iNext; iExists _; eauto. iFrame. }
      eauto. }
    iEval (rewrite big_sepM_insert //) in "Hσj_crash_toks".
    iDestruct "Hσj_crash_toks" as "(Hcrash1&_)".
    iDestruct (map_valid with "Hcrash_ctx Hcrash1") as %Hlookup.
    apply lookup_fmap_Some in Hlookup as (?&_&Hlookup).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Htok") as "(H1&_)"; eauto.
    iDestruct (ptsto_conflict with "Hcrash1 H1") as %[].
  }
  iDestruct "Hrest" as (s g) "(>H&Hinterp)".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&?&?&?&?&>Hctok&Hresv)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iIntros "#HC".
  iMod (ghost_step_crash_stuck' with "[] Hctx Hctok Hj [$] [$]") as (Hnstuck) "(Hj&H&Hctok)"; first by solve_ndisj.
  { iModIntro. iIntros "(h1&>h2)". iDestruct (pending_pending with "[$] [$]") as %[]. }
  iMod (ghost_step_crash_lifting _ _ _ _ _ (Atomically l e) s g [] (jrnl_upd σj' s) g (SOMEV v) []
          with "[] Hctok Hj Hctx H HC") as "(Hctok&Hj&H&_)".
  { apply head_prim_step.
    apply head_step_atomically; eauto.
    eapply atomically_not_stuck_body_safe; eauto.
  }
  { solve_ndisj. }
  { iModIntro. iIntros "(h1&>h2)". iDestruct (pending_pending with "[$] [$]") as %[]. }
  iMod (jrnl_ctx_upd _ (jrnlData σj') _ (jrnlAllocs σj) with "[$] [$] [$] [$] [$]") as "(Hσj'_data&Hffi)".
  { destruct Hwf as (?&?&?&?&?). rewrite Heq_kinds; eauto. }
  { destruct Hwf as (?&?&?&?&?). eauto. }
  iMod ("Hclo" with "[-Hσj_crash_toks Hσj'_data]") as "_".
  { iNext. iRight. iExists _, _. iFrame "H". iFrame. }
  iModIntro. iFrame.
Qed.

Lemma ghost_step_jrnl_atomically_ub' E j K {HCTX: LanguageCtx K} (l: sval) e1 σj e2 σj' σdom :
  always_steps e1 σj e2 σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_dom σdom -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e1)
  -∗ |NC={E}=>
   ⌜ (∃ s g, jrnl_sub_state σj' s ∧
        dom (gset _) (jrnlData (get_jrnl s.(world))) = σdom ∧
        ¬ stuck' e2 s g) ⌝ ∗
  j ⤇ K (Atomically l e1) ∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o).
Proof.
  iIntros (Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_allocs Hdom Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iDestruct (jrnl_ctx_dom_eq _ s with "[$] [$]") as %Hdom.
  iMod (ghost_step_stuck' with "Hj Hctx H") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  iMod ("Hclo" with "[-Hj Hσj_data]").
  { iNext. iExists _, _. iFrame. }
  iModIntro. iFrame.  iPureIntro.
  exists (jrnl_upd σj' s), g.
  split_and!.
  - eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto.
  - rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
    destruct Hsub as (?&?&Hsub&_).
    eapply subseteq_dom in Hsub.
    rewrite /=.
    rewrite /addr in Hsub Hdom.  rewrite -Hdom.
    match goal with
    | [ H: sworld _ = _ |- _ ] => rewrite H
    end.
    set_solver.
  - intros Hnstuck'. apply Hnstuck.
  split; first done.
  apply prim_head_irreducible; last first.
  { intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    naive_solver.
  }
  rewrite /irreducible. intros ????? Hnostep.
  inversion Hnostep; subst.
  {
    inversion H2; eauto.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
  }
Qed.

Lemma ghost_step_jrnl_atomically_ub E j K {HCTX: LanguageCtx K} (l: sval) e1 σj e2 σj' σdom :
  (∀ s g, jrnl_sub_state σj' s →
        dom (gset _) (jrnlData (get_jrnl s.(world))) = σdom →
        stuck' e2 s g) →
  always_steps e1 σj e2 σj' →
  nclose sN ⊆ E →
  spec_ctx -∗
  ([∗ map] a ↦ o ∈ (jrnlData σj), jrnl_mapsto a 1 o) -∗
  jrnl_kinds (jrnlKinds σj) -∗
  jrnl_alloc_map (jrnlAllocs σj) -∗
  jrnl_dom σdom -∗
  jrnl_open -∗
  j ⤇ K (Atomically l e1)
  -∗ |NC={E}=> False.
Proof.
  iIntros (Hub Hsteps ?) "(#Hctx&#Hstate) Hσj_data Hσj_kinds Hσj_alloc Hdom Hopen Hj".
  destruct Hsteps as (Heq_kinds&Hwf&Hrtc).
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (jrnl_ctx_sub_state_valid with "[$] [$] [$] [$] [$]") as %Hsub.
  iDestruct (jrnl_ctx_dom_eq _ s with "[$] [$]") as %Hdom.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[]; last by solve_ndisj.
  rewrite /stuck.
  split; first done.
  apply prim_head_irreducible; last first.
  { intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    naive_solver.
  }
  rewrite /irreducible. intros ????? Hnostep.
  inversion Hnostep; subst.
  {
    inversion H2; eauto.
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
    eapply Hub.
    { eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto. }
    { rewrite /jrnl_sub_dom in Hwf.
      rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
      destruct Hsub as (?&?&Hsub&_).
      eapply subseteq_dom in Hsub.
      match goal with
      | [ H: sworld _ = _ |- _ ] => rewrite H
      end.
      set_solver.
    }
  }
  {
    match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H; first eapply Hrtc; eauto
    end.
    eapply Hub.
    { eapply jrnl_sub_state_upd; eauto. destruct Hwf as (?&?&?&?); eauto. }
    { rewrite /jrnl_sub_dom in Hwf.
      rewrite //= dom_union_L /addr. destruct Hwf as (Heq&?). rewrite -Heq.
      destruct Hsub as (?&?&Hsub&_).
      eapply subseteq_dom in Hsub.
      match goal with
      | [ H: sworld _ = _ |- _ ] => rewrite H
      end.
      set_solver.
    }
  }
Qed.

Lemma objSize_non_bit_inv o b:
  objSz o = bufSz b ∧ b ≠ KindBit →
  ∃ vs, o = objBytes vs.
Proof.
  destruct o.
  - intros (Hsize&?). destruct b; try congruence; rewrite /objSz/bufSz in Hsize; lia.
  - eauto.
Qed.

Lemma objSize_bit_inv o b:
  objSz o = bufSz b ∧ b = KindBit →
  ∃ vs, o = objBit vs.
Proof.
  destruct o.
  - intros (Hsize&?). eauto.
  - intros (Hsize&?). subst. rewrite //= in Hsize. lia.
Qed.

Lemma not_stuck'_OverWriteBit_inv K `{!LanguageCtx' K} a (ov : sval) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        OverWriteBitOp (addr2val' a, ov)%V)) s g →
  ∃ σj o, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some KindBit ∧
  val_of_obj' (objBit o) = ov.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (objSz o0 = bufSz b ∧ b = KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  edestruct (objSize_bit_inv) as (vs&Heq_vs); eauto.
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_OverWrite_inv K `{!LanguageCtx' K} a (ov : sval) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        OverWriteOp (addr2val' a, ov)%V)) s g →
  ∃ σj k o, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some k ∧
  val_of_obj' (objBytes o) = ov ∧
  objSz (objBytes o) = bufSz k ∧ k ≠ KindBit.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (objSz o0 = bufSz b ∧ b ≠ KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  edestruct (objSize_non_bit_inv) as (vs&Heq_vs); eauto.
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_ReadBuf_inv K `{!LanguageCtx' K} a (sz : u64) s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        ReadBufOp (addr2val' a, #sz)%V)) s g →
  ∃ σj k, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some k ∧
  bufSz k = int.nat sz ∧ k ≠ KindBit.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (b ≠ KindBit ∧ bufSz b = int.nat sz)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_ReadBit_inv K `{!LanguageCtx' K} a s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        ReadBitOp (addr2val' a)%V)) s g →
  ∃ σj, world s = Opened σj ∧
  is_Some (jrnlData σj !! a) ∧
  jrnlKinds σj !! (addrBlock a) = Some (KindBit).
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlData _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlKinds _ !! _) eqn:Heq3; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (b = KindBit)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck_MkAllocOp_inv max s g:
  ¬ stuck ((ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        MkAllocOp #(LitInt max)%V)) s g →
  ∃ σj, world s = Opened σj ∧ 0 < int.Z max ∧ int.Z max `mod` 8 = 0.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck_ExternalOp; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  inversion H1. subst.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H2.
  { inversion H2. subst. monad_inv. }
  repeat (simpl in *; monad_inv); eauto.
Qed.

Lemma not_stuck'_MarkUsedOp_inv K `{!LanguageCtx' K} l n s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        MarkUsedOp (PairV #(LitLoc l) #(LitInt n)%V))) s g →
  ∃ σj max, world s = Opened σj ∧
  jrnlAllocs σj !! l = Some max ∧ int.Z n < int.Z max.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlAllocs _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (int.Z n < int.Z r)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

Lemma not_stuck'_FreeNumOp_inv K `{!LanguageCtx' K} l n s g:
  ¬ stuck' (K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext)
                        FreeNumOp (PairV #(LitLoc l) #(LitInt n)%V))) s g →
  ∃ σj max, world s = Opened σj ∧
  jrnlAllocs σj !! l = Some max ∧ int.Z n ≠ 0 ∧ int.Z n < int.Z max.
Proof.
  intros Hnstuck. eapply NNPP.
  intros Hneg. apply Hnstuck.
  apply stuck'_fill; eauto.
  apply stuck_ExternalOp'; eauto.
  intros ????? Hstep.
  inversion Hstep; subst.
  simpl in H1.
  repeat (simpl in *; monad_inv).
  destruct (s.(world)) eqn:Heq; rewrite Heq in H1.
  { inversion H1. subst. monad_inv. }
  repeat (simpl in *; monad_inv).
  destruct (jrnlAllocs _ !! _) eqn:Heq2; last first.
  { inversion H1. inversion H2. eauto. }
  repeat (simpl in *; monad_inv).
  destruct (decide (int.Z n ≠ 0 ∧ int.Z n < int.Z r)); last first.
  { repeat (simpl in *; monad_inv). eauto. }
  eapply Hneg. naive_solver.
Qed.

Lemma ghost_step_jrnl_mkalloc E j K {HCTX: LanguageCtx K} (n: u64):
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ffi_op_field jrnl_spec_ext) MkAllocOp #n)
  -∗ |NC={E}=> ∃ (l: loc), ⌜ 0 < int.Z n ∧ int.Z n `mod` 8 = 0 ⌝ ∗ j ⤇ K #l ∗ jrnl_alloc l n.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (s g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hj".
  iMod (ghost_step_stuck' with "[$] [$] [$]") as (Hnstuck) "(Hj&H)"; first by solve_ndisj.
  eapply not_stuck_MkAllocOp_inv in Hnstuck as (σj&Hopen&Hngt0); eauto.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl. econstructor.
    * repeat econstructor => //=.
      { rewrite Hopen. econstructor. eauto. }
      { refine (proj2_sig _). apply gen_isFreshAlloc. }
      { rewrite /check/ifThenElse decide_True //=. }
      { rewrite //= Hopen //=. }
    * repeat econstructor.
  }
  { solve_ndisj. }
  rewrite Hopen.
  iDestruct "Hffi" as "(Hopen&Hstate_ctx)".
  iDestruct "Hstate_ctx" as "(?&?&?&?&Hallocs)".
  iMod (map_alloc_ro (` (gen_isFreshAlloc σj.(jrnlAllocs))) with "Hallocs") as "(Hallocs&Halloc1)".
  { destruct (gen_isFreshAlloc _); eauto. }
  iMod ("Hclo" with "[-Hj Halloc1]") as "_".
  { iNext. iExists _, _. iFrame "H". iFrame. }
  iModIntro. iExists _. iFrame "∗ %".
Qed.

End spec.
