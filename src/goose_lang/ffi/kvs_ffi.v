From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.

(* TODO: move this out, it's completely general *)
(* Generalize life cycle of object state *)
Section recoverable.
  Context {Σ:Type}.
  Inductive RecoverableState :=
    | UnInit
    | Initing
    | Closed (s:Σ)
    | Opening (s:Σ)
    | Opened (s:Σ) (l:loc)
  .

  Definition recoverable_model : ffi_model :=
    mkFfiModel (RecoverableState) (populate UnInit).

  Local Existing Instance recoverable_model.

  Context {ext:ext_op}.

  Definition openΣ : transition state (Σ*loc) :=
    bind (reads id) (λ rs, match rs.(world) with
                           | Opened s l => ret (s,l)
                           | _ => undefined
                           end).

  Definition modifyΣ (f:Σ -> Σ) : transition state unit :=
    bind openΣ (λ '(s, l), modify (set world (λ _, Opened (f s) l))).

  (* TODO: generalize to a transition to construct the initial value, using a zoom *)
  Definition initTo (init:Σ) (l:loc) : transition state unit :=
    bind (reads id) (λ rs, match rs.(world) with
                           | UnInit => modify (set world (fun _ => Opened init l))
                           | _ => undefined
                           end).

  Definition open (l:loc) : transition state Σ :=
    bind (reads id) (λ rs, match rs.(world) with
                           | Closed s => bind (modify (set world (fun _ => Opened s l)))
                                             (fun _ => ret s)
                           | _ => undefined
                           end).

  Definition close : transition (RecoverableState) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s _ | Closed s => modify (fun _ => Closed s)
                           | UnInit => modify (fun _ => UnInit)
                           | _ => undefined
                           end).

  Global Instance Recoverable_inhabited : Inhabited RecoverableState := populate UnInit.
End recoverable.

Arguments RecoverableState Σ : clear implicits.
Arguments recoverable_model Σ : clear implicits.

Definition ty_ := forall (val_ty:val_types), @ty val_ty.
(* TODO: slice should not require an entire ext_ty *)
Definition sliceT_ (t: ty_) : ty_ := λ val_ty, prodT (arrayT (t _)) uint64T.
Definition blockT_: ty_ := sliceT_ (λ val_ty, byteT).

Inductive KvsOp :=
  | MakeOp
  | GetOp
  | MultiPutOp
.

Instance eq_KvsOp : EqDecision KvsOp.
Proof.
  solve_decision.
Defined.

Instance KvsOp_fin : Countable KvsOp.
Proof.
  solve_countable KvsOp_rec 5%nat.
Qed.

Definition kvs_op : ext_op.
Proof.
  refine (mkExtOp KvsOp _ _).
Defined.

Inductive Kvs_ty := KvsT.

Instance kvs_val_ty: val_types :=
  {| ext_tys := Kvs_ty; |}.

Section kvs.
  Print structRefT.
  Definition KvsSize := 10000. (*TODO *)
  (* Function that inits gmap with all 0s for ^ blocks *)
  (*Fixpoint kvs_init_helper (blk : nat) map :=
    match blk with
    | N.0 => (set map <[(Z.of_N blk) := disk.Block0]>)
    | S n => kvs_init_helper n (set map <[(Z.of_N blk) := disk.Block0]>)
                            end.*)
  Definition kvs_init : gmap u64 disk.Block.
    (*in kvs_init_helper KvsSize (GMap u64 disk.Block).*)
  Admitted.
  Definition KVPairT : ty := structRefT [uint64T; prodT (arrayT (uint64T)) uint64T].
  Existing Instances kvs_op kvs_val_ty.
  Instance kvs_ty: ext_types kvs_op :=
    {| val_tys := kvs_val_ty;
       get_ext_tys (op: @external kvs_op) :=
         match op with
         (* pair where first comp is type of inputs, sec is type of outputs *)
           (* have make take no arguments, initialize super + txn -- assume specs? *)
           (* kvs type should be opaque, but kvpair should be known by client *)
         | MakeOp => (unitT, extT KvsT)
         | GetOp => (prodT (extT KvsT) uint64T, KVPairT)
         | MultiPutOp => (prodT (extT KvsT) (prodT (arrayT KVPairT) uint64T), boolT)
         end; |}.

  Definition kvs_state := RecoverableState (gmap u64 disk.Block).

  Instance kvs_model : ffi_model := recoverable_model (gmap u64 disk.Block).

  Existing Instances r_mbind r_fmap.

  Definition read_slice (t:ty) (v:val): transition state (list val) :=
    match v with
    | PairV (#(LitLoc l)) (PairV #(LitInt sz) #(LitInt cap)) =>
      (* TODO: implement , mark as being read *)
      ret []
    | _ => undefined
    end.

  Print PairV.
  Definition read_kvpair_key (t:ty) (v:val): transition state u64:=
    match v with
    | PairV #(LitInt key) #(LitLoc _) => ret key
    | _ => undefined
    end.

  Definition read_kvpair_dataslice (t:ty) (v:val): transition state val :=
    match v with
    | PairV #(LitInt _) #(LitLoc dataloc) =>ret #(LitLoc dataloc)
    | _ => undefined
    end.

  Fixpoint update_keys (kvs : gmap u64 disk.Block) (keys : list u64) (data: list disk.Block)
    : gmap u64 disk.Block
    :=
    match keys, data with
    | k::ks, d::ds => update_keys (<[k := d]> kvs) ks ds
    | [], [] => kvs
    | _, _ => kvs
    end.

  Fixpoint tmapM {Σ A B} (f: A -> transition Σ B) (l: list A) : transition Σ (list B) :=
    match l with
    | [] => ret []
    | x::xs => b ← f x;
             bs ← tmapM f xs;
             ret (b :: bs)
    end.

  (* TODO: implement *)
  Definition to_block (l: list val): option disk.Block := None.

  Definition allocIdent: transition state loc :=
    l ← allocateN 1;
    modify (set heap <[l := Free #()]>);;
           ret l.

  Definition kvs_step (op:KvsOp) (v:val) : transition state val :=
    match op, v with
    | MakeOp, LitV LitUnit =>
      kvsPtr ← allocIdent;
      initTo (kvs_init) kvsPtr;;
             ret $ (LitV $ LitLoc kvsPtr)
    | GetOp, PairV (LitV (LitLoc kvsPtr)) (LitV (LitInt key)) =>
      openΣ ≫= λ '(kvs, kvsPtr_), (*kvs is the state *)
      check (kvsPtr = kvsPtr_);;
      b ← unwrap (kvs !! key);
      l ← allocateN 4096;
      modify (state_insert_list l (disk.Block_to_vals b));;
             ret $ #(LitLoc l)
    | MultiPutOp, PairV (LitV (LitLoc kvsPtr)) v =>
      (*convert goose representations of kvpair to coq pair of key and value, *)
      (*given list of updates, inserts into gmap *)
      (*to define spec effect of operation*)
      openΣ ≫= λ '(_, kvsPtr_),
      check (kvsPtr = kvsPtr_);;
      (* FIXME: append should be non-atomic in the spec because it needs to read
         an input slice (and the slices the input points to). *)
      (* need to mark that everything is being read so no concurrent modifications *)
      (* LYT: we might just need to check no other writers? Might need to split into two steps *)
      block_slices ← read_slice KVPairT v;
      block_keys ← tmapM (read_kvpair_key KVPairT) block_slices;
      block_dataslices ← tmapM (read_kvpair_dataslice KVPairT) block_slices;
      block_vals ← tmapM (read_slice (@slice.T _ kvs_ty byteT)) block_dataslices;
      new_blocks ← tmapM (unwrap ∘ to_block) block_vals;
      modifyΣ (λ s, update_keys s block_keys new_blocks);;
      ret $ #()
    | _, _ => undefined
    end.

  Instance kvs_semantics : ext_semantics kvs_op kvs_model :=
    {| ext_step := kvs_step;
       ext_crash := fun s s' => relation.denote close s s' tt; |}. (* everything is durable *)
End kvs.

(*
From iris.algebra Require Import auth agree excl csum.
From Perennial.program_logic Require Import ghost_var.
Inductive kvs_unopen_status := UnInit' | Closed'.

(* resource alg: append log has two: *)
(* (1) tracks status of append log (open/closed) --> anything with recoverable state*)
Definition openR := csumR (prodR fracR (agreeR (leibnizO kvs_unopen_status))) (agreeR (leibnizO loc)).
Definition Kvs_Opened (l: loc) : openR := Cinr (to_agree l).

(* Type class defn, define which algebras are availabe *)
Class kvsG Σ :=
  { kvsG_open_inG :> inG Σ openR; (* inG --> which resources are available in type class *)
    (* implicitly insert names for elements, used to tag which generation *)
    kvsG_open_name : gname;
    (* (2) exlusive/etc. algebra for list of disk blocks --> allows for ownership of entire log *)
    kvsG_state_inG:> inG Σ (authR (optionUR (exclR (leibnizO (list disk.Block)))));
    kvsG_state_name: gname;
  }.

(* without names: e.g. disk names stay same, memory ones are forgotten *)
Class kvs_preG Σ :=
  { kvsG_preG_open_inG :> inG Σ openR;
    kvsG_preG_state_inG:> inG Σ (authR (optionUR (exclR (leibnizO (list disk.Block)))));
  }.

Definition kvsΣ : gFunctors :=
  #[GFunctor openR; GFunctor (authR (optionUR (exclR (leibnizO (list disk.Block)))))].

Instance subG_kvsG Σ: subG kvsΣ Σ → kvs_preG Σ.
Proof. solve_inG. Qed.

(* Helpers to manipulate names *)
Record kvs_names :=
  { kvs_names_open: gname;
    kvs_names_state: gname; }.

Definition kvs_get_names {Σ} (lG: kvsG Σ) :=
  {| kvs_names_open := kvsG_open_name; kvs_names_state := kvsG_state_name |}.

Definition kvs_update {Σ} (lG: kvsG Σ) (names: kvs_names) :=
  {| kvsG_open_inG := kvsG_open_inG;
     kvsG_open_name := (kvs_names_open names);
     kvsG_state_inG := kvsG_state_inG;
     kvsG_state_name := (kvs_names_state names);
  |}.

Definition kvs_update_pre {Σ} (lG: kvs_preG Σ) (names: kvs_names) :=
  {| kvsG_open_inG := kvsG_preG_open_inG;
     kvsG_open_name := (kvs_names_open names);
     kvsG_state_inG := kvsG_preG_state_inG;
     kvsG_state_name := (kvs_names_state names);
  |}.

(* assert have resource that tell us that kvs is opened at l, persistent + duplicable *)
Definition kvs_open {Σ} {lG :kvsG Σ} (l: loc) :=
  own (kvsG_open_name) (Kvs_Opened l).
Definition kvs_closed_frag {Σ} {lG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO kvs_unopen_status))).
Definition kvs_closed_auth {Σ} {lG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO kvs_unopen_status))).
Definition kvs_uninit_frag {Σ} {lG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO kvs_unopen_status))).
Definition kvs_uninit_auth {Σ} {lG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO kvs_unopen_status))).

(* what blocks are in the log *)
(* kvs: more fine-grained lock? or lock entire map? (more/less useful for clients?) *)
(* precondition in spec --> assert have points-to facts (no state RA), gen_heap *)
Definition kvs_auth {Σ} {lG :kvsG Σ} (vs: list (disk.Block)) :=
  own (kvsG_state_name) (● Excl' (vs: leibnizO (list disk.Block))).
Definition kvs_frag {Σ} {lG :kvsG Σ} (vs: list (disk.Block)) :=
  own (kvsG_state_name) (◯ Excl' (vs: leibnizO (list disk.Block))).

Section kvs_interp.
  Existing Instances kvs_op kvs_model kvs_val_ty.

  (* ctx assertions map physical state to which resource assertions should be true, *)
  (* stores auth copy of fact*)
  Definition kvs_ctx {Σ} {lG: kvsG Σ} (lg: @ffi_state kvs_model) : iProp Σ :=
    match lg with
    | Opened s l => kvs_open l (*∗ kvs_auth s*)
    | Closed s => kvs_closed_auth (*∗ kvs_auth s*)
    | UnInit => kvs_uninit_auth (*∗ kvs_auth []*)
    | _ => False%I
    end.
(* When first start program, what initial resources assertions do you get
  Definition kvs_start {Σ} {lG: kvsG Σ} (lg: @ffi_state kv
s_model) : iProp Σ :=
    match lg with
    | Opened s l => kvs_open l ∗ kvs_frag s
    | Closed s => kvs_closed_frag ∗ kvs_frag s
    | UnInit => kvs_uninit_frag ∗ kvs_frag []
    | _ => False%I
    end.
 *)
(* get access to whether open/closed status
  Definition kvs_restart {Σ} (lG: kvsG Σ) (lg: @ffi_state log_model) :=
    match lg with
    | Opened s l => kvs_open l
    | Closed s => kvs_closed_frag
    | UnInit => kvs_uninit_frag
    | _ => False%I
    end.
  (*how to interpret physical state as ghost resources*)
  Program Instance kvs_interp : ffi_interp kvs_model :=
    {| ffiG := kvsG;
       ffi_names := kvs_names;
       ffi_get_names := @kvs_get_names;
       ffi_update := @kvs_update;
       ffi_get_update := _;
       ffi_ctx := @kvs_ctx;
       ffi_start := @kvs_start;
       ffi_restart := @kvs_restart;
    |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
 *)
End kvs_interp.

Section kvs_lemmas.
  Context `{lG: kvsG Σ}.

  Global Instance kvs_ctx_Timeless lg: Timeless (kvs_ctx lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance kvs_start_Timeless lg: Timeless (kvs_start lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance kvs_restart_Timeless lg: Timeless (kvs_restart _ lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance kvs_open_Persistent (l: loc) : Persistent (kvs_open l).
  Proof. rewrite /kvs_open/Kvs_Opened. apply own_core_persistent. rewrite /CoreId//=. Qed.

  Lemma kvs_closed_auth_uninit_frag:
    kvs_closed_auth -∗ kvs_uninit_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%agree_op_inv'].
    inversion Heq.
  Qed.

  Lemma kvs_uninit_auth_closed_frag:
    kvs_uninit_auth -∗ kvs_closed_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%agree_op_inv'].
    inversion Heq.
  Qed.

  Lemma kvs_uninit_auth_opened l:
    kvs_uninit_auth -∗ kvs_open l -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma kvs_closed_auth_opened l:
    kvs_closed_auth -∗ kvs_open l -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma kvs_ctx_unify_closed lg vs:
    kvs_closed_frag -∗ kvs_frag vs -∗ log_ctx lg -∗ ⌜ lg = Closed vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hclosed_frag Hstate_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_closed_auth_uninit_frag with "[$] [$]") as %[].
    - iDestruct "Hctx" as "(Hclosed_auth&Hstate_auth)".
      rewrite /kvs_frag/kvs_auth. by unify_ghost.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hclosed_frag") as %Hval.
      inversion Hval.
  Qed.

  Lemma kvs_auth_frag_unif vs vs':
    kvs_auth vs -∗ kvs_frag vs' -∗ ⌜ vs = vs' ⌝.
  Proof.
    rewrite /kvs_auth/kvs_frag. iIntros "H1 H2". by unify_ghost.
  Qed.

  Lemma kvs_open_unif l l':
    kvs_open l -∗ kvs_open l' -∗ ⌜ l = l' ⌝.
  Proof.
    rewrite /kvs_auth/kvs_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hval.
    rewrite /Kvs_Opened -Cinr_op in Hval.
    assert (l ≡ l') as Heq.
    { eapply agree_op_inv'. eauto. }
    inversion Heq. by subst.
  Qed.

  Lemma kvs_ctx_unify_uninit lg:
    kvs_uninit_frag -∗ kvs_ctx lg -∗ ⌜ lg = UnInit ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Huninit_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Huninit_frag") as %Hval.
      inversion Hval as [? Heq%agree_op_inv'].
      inversion Heq.
    - iDestruct "Hctx" as "(Hauth&Hstate_auth)".
      iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
      inversion Hval.
  Qed.

  Lemma kvs_ctx_unify_opened l lg:
    kvs_open l -∗ kvs_ctx lg -∗ ⌜ ∃ vs, lg = Opened vs l ⌝.
  Proof.
    destruct lg as [| | |  | vs l']; try eauto; iIntros "Hopen Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_open_unif with "[$] [$]") as %Heq.
      subst. iPureIntro; eexists. eauto.
  Qed.

  Lemma kvs_ctx_unify_opened' l lg vs:
    kvs_open l -∗ kvs_frag vs -∗ log_ctx lg -∗ ⌜ lg = Opened vs l ⌝.
  Proof.
    destruct lg as [| | |  | vs' l']; try eauto; iIntros "Hopen Hstate Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_open_unif with "[$] [$]") as %Heq.
      iDestruct (kvs_auth_frag_unif with "[$] [$]") as %Heq'.
      subst. eauto.
  Qed.

  Lemma kvs_uninit_token_open (l: loc):
    kvs_uninit_auth -∗ kvs_uninit_frag ==∗ log_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (Kvs_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op' Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma kvs_closed_token_open (l: loc):
    kvs_closed_auth -∗ kvs_closed_frag ==∗ log_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (Kvs_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op' Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma kvs_state_update vsnew vs1 vs2:
    kvs_auth vs1 -∗ kvs_frag vs2 ==∗ log_auth vsnew ∗ log_frag vsnew.
  Proof. apply ghost_var_update. Qed.

(* Not related to physical state yet, just updates to ghost vars*)
End kvs_lemmas.

From Perennial.goose_lang Require Import adequacy.

(* when crashes, ffi_crash_rel: hF[] = instance of type class logG *)
(* Program Instance --> define instance of type class, don't need to fill in all fields (craete goal, obligation) *)Program Instance kvs_interp_adequacy:
  @ffi_interp_adequacy kvs_model kvs_interp log_op log_semantics :=
  {| ffi_preG := kvs_preG;
     ffiΣ := kvsΣ;
     subG_ffiPreG := subG_kvsG;
     ffi_initP := λ σ, σ = UnInit;
     ffi_update_pre := @kvs_update_pre;
     ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @kvsG_state_inG _ hF1 = @kvsG_state_inG _ hF2 ∧
                                           kvs_names_state (kvs_get_names hF1) =
                                           kvs_names_state (kvs_get_names hF2) ⌝%I;
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ->). simpl.
  rewrite /kvs_uninit_auth/kvs_uninit_frag/log_frag/log_auth.
  iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (ghost_var_alloc ([]: leibnizO (list disk.Block))) as (γ2) "(H2a&H2b)".
  iExists {| kvs_names_open := γ1; kvs_names_state := γ2 |}.
  iFrame. iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
Qed.
Next Obligation.
  iIntros (Σ σ σ' Hcrash Hold) "Hinterp".
  inversion Hcrash; subst.
  monad_inv. inversion H. subst. inversion H1. subst.
  destruct x; monad_inv.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /kvs_uninit_auth/kvs_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /kvs_uninit_auth/kvs_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    rewrite /kvs_uninit_auth/kvs_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op' Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance kvs_spec_ext : spec_ext_op := {| spec_ext_op_field := kvs_op |}.
Instance kvs_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := kvs_model |}.
Instance kvs_spec_ext_semantics : spec_ext_semantics (kvs_spec_ext) (log_spec_ffi_model) :=
  {| spec_ext_semantics_field := kvs_semantics |}.
Instance kvs_spec_ffi_interp : spec_ffi_interp kvs_spec_ffi_model :=
  {| spec_ffi_interp_field := kvs_interp |}.
Instance kvs_spec_ty : ext_types (spec_ext_op_field) := kvs_ty.
Instance kvs_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := kvs_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := kvs_interp_adequacy |}.

Context `{invG Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.

Implicit Types K: spec_lang.(language.expr) → spec_lang.(language.expr).
Instance kvsG0 : kvsG Σ := refinement_spec_ffiG.

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

Lemma ghost_step_init_stuck E j K {HCTX: LanguageCtx K} σ:
  nclose sN_inv ⊆ E →
  (σ.(@world _ kvs_spec_ffi_model.(@spec_ffi_model_field)) ≠ UnInit) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ -∗
  |={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    intros ?????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv).
  }
  { solve_ndisj. }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ:
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ kvs_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ -∗
  |={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    intros ?????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
    eapply H1; eauto.
  }
  { solve_ndisj. }
Qed.

Lemma kvs_closed_init_false vs E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_closed_frag -∗
  kvs_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hentries Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_closed with "[$] [$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { congruence. }
Qed.

Lemma kvs_opened_init_false l E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (kvs_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma kvs_init_init_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step. simpl. econstructor.
      * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
        ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
        ** simpl. rewrite Heq. repeat econstructor.
      * repeat econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { simpl. congruence. }
  - iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma kvs_init_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_stuck with "Hj' Hctx H") as "[]".
    { eapply stuck_ExternalOp; first (by eauto).
      intros ?????. by repeat (inv_head_step; simpl in H2; repeat monad_inv).
    }
    { solve_ndisj. }
  - iMod (ghost_step_init_stuck with "Hj [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_init_stuck with "Hj [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma ghost_step_kvs_init E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_uninit_frag -∗
  kvs_frag [] -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #())
  ={E}=∗
  ∃ (l: loc), j ⤇ K (#l, #true)%V ∗ kvs_open l ∗ kvs_frag [].
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hvals Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_uninit with "[$] [$]") as %Heq.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step. simpl. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (kvs_uninit_token_open ((fresh_locs (dom _ σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) _ (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  rewrite loc_add_0.
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _. iFrame "H".  iFrame. iFrame "Hopen". }
  iModIntro. iExists _. iFrame "Hopen". iFrame.
Qed.

Lemma kvs_uninit_open_false vs E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_uninit_frag -∗
  kvs_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hentries Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_uninit with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { congruence. }
Qed.

Lemma kvs_opened_open_false l E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (kvs_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma kvs_open_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) ={E}=∗
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step. simpl. econstructor.
      * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
        ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
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

Lemma ghost_step_kvs_open E j K {HCTX: LanguageCtx K} vs:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_closed_frag -∗
  kvs_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #())
  ={E}=∗
  ∃ (l: loc), j ⤇ K #l%V ∗ kvs_open l ∗ kvs_frag vs.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hvals Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_closed with "[$] [$] [$]") as %Heq.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step. simpl. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (kvs_closed_token_open ((fresh_locs (dom _ σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) _ (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  rewrite loc_add_0.
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _. iFrame "H".  iFrame. iFrame "Hopen". }
  iModIntro. iExists _. iFrame "Hopen". iFrame.
Qed.

Lemma ghost_step_kvs_reset E j K {HCTX: LanguageCtx K} l vs:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_open l -∗
  kvs_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) ResetOp #l)
  ={E}=∗
  j ⤇ K #()%V ∗kvs_frag [].
Proof.
  iIntros (?) "(#Hctx&#Hstate) #Hopen Hvals Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_opened with "[$] [$]") as %Heq.
  destruct Heq as (vs'&Heq).
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step. repeat (eauto || monad_simpl || rewrite Heq || econstructor). }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (kvs_state_update [] with "[$] [$]") as "(Hvals_auth&?)".
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _. iFrame "H". iFrame. iFrame "Hopen". }
  iModIntro. iFrame.
Qed.
End

*)
