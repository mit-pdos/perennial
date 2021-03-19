From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.
From Perennial.algebra Require Import gen_heap_names.

From iris.algebra Require Import auth agree excl csum.
From Perennial.base_logic Require Import ghost_var.

Set Default Proof Using "Type".

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

  Definition openΣ : transition (state*global_state) (Σ*loc) :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Opened s l => ret (s,l)
                           | _ => undefined
                           end).

  Definition modifyΣ (f:Σ -> Σ) : transition (state*global_state) unit :=
    bind openΣ (λ '(s, l), modify (λ '(σ,g), (set world (λ _, Opened (f s) l) σ, g))).

  (* TODO: generalize to a transition to construct the initial value, using a zoom *)
  Definition initTo (init:Σ) (l:loc) : transition (state*global_state) unit :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | UnInit => modify (λ '(σ,g), (set world (fun _ => Opened init l) σ, g))
                           | _ => undefined
                           end).

  Definition open (l:loc) : transition (state*global_state) Σ :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Closed s => bind (modify (λ '(σ,g), (set world (fun _ => Opened s l) σ, g)))
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
  | OpenOp (* both open and init map to the same function (makeKVS) *)
  | InitOp
  | GetOp
  | MultiPutMarkOp
  | MultiPutCommitOp
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
  Parameter kvs_sz : nat.

  Fixpoint init_keys (keys: list u64) (sz: nat) : list u64 :=
  match sz with
  | O => keys
  | S n => init_keys ((U64 (Z.of_nat n)) :: keys) n
  end.
  Definition kvs_keys_all : list u64 := init_keys [] kvs_sz.

  Definition kvs_state_typ := gmap u64 disk.Block.
  Fixpoint init_kvs (kvs: kvs_state_typ) (sz: nat) : kvs_state_typ :=
  match sz with
  | O => kvs
  | S n => <[(U64 (Z.of_nat n)) := (inhabitant disk.Block0)]> (init_kvs kvs n)
  end.
  Definition kvs_init_s : gmap u64 disk.Block := init_kvs ∅ kvs_sz.

  Definition KVPairT : ty := structRefT [uint64T; prodT (arrayT (uint64T)) uint64T].
  Existing Instances kvs_op kvs_val_ty.

  Inductive kvs_ext_tys : @val kvs_op -> (ty * ty) -> Prop :=
  | KvsOpType op :
      kvs_ext_tys (λ: "v", ExternalOp op (Var "v"))%V
       (match op with
         (* pair where first comp is type of inputs, sec is type of outputs *)
           (* have make take no arguments, initialize super + txn -- assume specs? *)
           (* kvs type should be opaque, but kvpair should be known by client *)
         | OpenOp => (unitT, extT KvsT)
         | InitOp => (unitT, extT KvsT)
         | GetOp => (prodT (extT KvsT) uint64T, prodT (KVPairT) boolT)
         | MultiPutMarkOp => (prodT (extT KvsT) (prodT (arrayT KVPairT) uint64T), unitT)
         | MultiPutCommitOp => (prodT (extT KvsT) (prodT (arrayT KVPairT) uint64T), boolT)
         end).

  Instance kvs_ty: ext_types kvs_op :=
    {| val_tys := kvs_val_ty;
       get_ext_tys := kvs_ext_tys |}.

  Definition kvs_state := RecoverableState (gmap u64 disk.Block).

  Instance kvs_model : ffi_model := recoverable_model (gmap u64 disk.Block).

  Existing Instances r_mbind r_fmap.

  Definition mark_slice {state} (t:ty) (v:val): transition state () :=
    match v with
    | PairV (#(LitLoc l)) (PairV #(LitInt sz) #(LitInt cap)) =>
      (* TODO: implement , mark as being read *)
      ret ()
    | _ => undefined
    end.

  Definition read_slice {state} (t:ty) (v:val): transition state (list val) :=
    match v with
    | PairV (#(LitLoc l)) (PairV #(LitInt sz) #(LitInt cap)) =>
      (* TODO: implement , return contents *)
      ret []
    | _ => undefined
    end.

  Definition read_kvpair_key {state} (t:ty) (v:val): transition state u64:=
    match v with
    | PairV #(LitInt key) #(LitLoc _) => ret key
    | _ => undefined
    end.

  Definition read_kvpair_dataslice {state} (t:ty) (v:val): transition state val :=
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

  Definition allocIdent: transition (state*global_state) loc :=
    l ← allocateN 1;
    modify (λ '(σ, g), (set heap <[l := Free #()]> σ, g));;
           ret l.

  Definition kvs_step (op:KvsOp) (v:val) : transition (state*global_state) val :=
    match op, v with
    | InitOp, LitV LitUnit =>
      kvsPtr ← allocIdent;
      initTo (kvs_init_s) kvsPtr;;
      ret $ (LitV $ LitLoc kvsPtr)
    | OpenOp, LitV LitUnit =>
      logPtr ← allocIdent;
      s ← open logPtr;
      ret $ LitV $ LitLoc logPtr
    | GetOp, PairV (LitV (LitLoc kvsPtr)) (LitV (LitInt key)) =>
      openΣ ≫= λ '(kvs, kvsPtr_), (*kvs is the state *)
      check (kvsPtr = kvsPtr_);;
      b ← unwrap (kvs !! key);
      l ← allocateN 4096;
      modify (λ '(σ,g), (state_insert_list l (disk.Block_to_vals b) σ, g));;
             ret $ (PairV #(LitLoc l) #true) (*This could return false?*) 
    | MultiPutMarkOp, PairV (LitV (LitLoc kvsPtr)) v => mark_slice KVPairT v;; ret $ #()
    | MultiPutCommitOp, PairV (LitV (LitLoc kvsPtr)) v =>
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
      ret $ #true (*TODO can this return false if commit_wait fails? *)
    | _, _ => undefined
    end.

  Instance kvs_semantics : ext_semantics kvs_op kvs_model :=
    {| ext_step := kvs_step;
       ext_crash := fun s s' => relation.denote close s s' tt; |}. (* everything is durable *)
End kvs.

Inductive kvs_unopen_status := UnInit' | Closed'.

(* resource alg: append log has two: *)
(* (1) tracks status of append log (open/closed) --> anything with recoverable state*)
Definition openR := csumR (prodR fracR (agreeR (leibnizO kvs_unopen_status))) (agreeR (leibnizO loc)).

Definition Kvs_Opened (l: loc) : openR := Cinr (to_agree l).

(* Type class defn, define which algebras are available *)
Class kvsG Σ :=
  { kvsG_open_inG :> inG Σ openR; (* inG --> which resources are available in type class *)
    (* implicitly insert names for elements, used to tag which generation *)
    kvsG_open_name : gname;
    (* (2) exlusive/etc. algebra for disk blocks --> allows for ownership of blocks *)
    kvsG_state_inG :> gen_heap.gen_heapG u64 disk.Block Σ;
  }.

(* without names: e.g. disk names stay same, memory ones are forgotten *)
Class kvs_preG Σ :=
  { kvsG_preG_open_inG :> inG Σ openR;
    kvsG_preG_state_inG :> gen_heap.gen_heapPreG u64 disk.Block Σ;
  }.

Definition kvsΣ : gFunctors :=
  #[GFunctor openR; gen_heapΣ u64 disk.Block].

Instance subG_kvsG Σ: subG kvsΣ Σ → kvs_preG Σ.
Proof. solve_inG. Qed.

(* Helpers to manipulate names *)
Record kvs_names :=
  { kvs_names_open: gname;
    kvs_names_state: gen_heap_names; }.

Definition kvs_get_names {Σ} (kvs: kvsG Σ) :=
  {| kvs_names_open := kvsG_open_name; kvs_names_state := gen_heapG_get_names kvsG_state_inG|}.

Definition kvs_update {Σ} (kvs: kvsG Σ) (names: kvs_names) :=
  {| kvsG_open_inG := kvsG_open_inG;
     kvsG_open_name := (kvs_names_open names);
     kvsG_state_inG := gen_heapG_update kvsG_state_inG names.(kvs_names_state);
  |}.

Definition kvs_update_pre {Σ} (kvsG: kvs_preG Σ) (names: kvs_names) :=
  {| kvsG_open_inG := kvsG_preG_open_inG;
     kvsG_open_name := (kvs_names_open names);
     kvsG_state_inG := gen_heapG_update_pre kvsG_preG_state_inG names.(kvs_names_state);
  |}.

(* assert have resource that tell us that kvs is opened at l, persistent + duplicable *)
Definition kvs_open {Σ} {kvsG :kvsG Σ} (l: loc) :=
  own (kvsG_open_name) (Kvs_Opened l).
Definition kvs_closed_frag {Σ} {kvsG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO kvs_unopen_status))).
Definition kvs_closed_auth {Σ} {kvsG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO kvs_unopen_status))).
Definition kvs_uninit_frag {Σ} {ksG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO kvs_unopen_status))).
Definition kvs_uninit_auth {Σ} {kvsG :kvsG Σ} :=
  own (kvsG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO kvs_unopen_status))).

(* what blocks are in the kvs *)
(* kvs: more fine-grained lock? or lock entire map? (more/less useful for clients?) *)
(* precondition in spec --> assert have points-to facts (no state RA), gen_heap *)
Definition kvs_auth {Σ} {kvs :kvsG Σ} (s: gmap u64 disk.Block) := gen_heap.gen_heap_interp s.
Definition kvs_frag {Σ} {kvsG :kvsG Σ} (k : u64) (v : disk.Block) : iProp Σ :=
   (gen_heap.mapsto (L:=u64) (V:=disk.Block) k (DfracOwn 1) v)%I.

Section kvs_interp.
  Existing Instances kvs_op kvs_model kvs_val_ty.

  (* ctx assertions map physical state to which resource assertions should be true, *)
  (* stores auth copy of fact*)
  Definition kvs_ctx {Σ} {kvsG: kvsG Σ} (kvs: @ffi_state kvs_model) : iProp Σ :=
    match kvs with
    | Opened s l => kvs_open l ∗ kvs_auth s
    | Closed s => kvs_closed_auth ∗ kvs_auth s
    | UnInit => kvs_uninit_auth ∗ kvs_auth (∅ : gmap u64 disk.Block) (*  XXXX kvs_init_s *)
    | _ => False%I
    end.

  (* When first start program, what initial resources assertions do you get *)
  Definition kvs_start {Σ} {kvsG: kvsG Σ} (kvs: @ffi_state kvs_model) : iProp Σ :=
    match kvs with
    | Opened s l => kvs_open l ∗ ([∗ list] k ∈ kvs_keys_all, (∃ v, kvs_frag k v)%I)
    | Closed s => kvs_closed_frag ∗ ([∗ list] k ∈ kvs_keys_all, (∃ v, kvs_frag k v)%I)
    | UnInit => kvs_uninit_frag
    | _ => False%I
    end.

(* get access to whether open/closed status *)
  Definition kvs_restart {Σ} (kvsG: kvsG Σ) (kvs: @ffi_state kvs_model) :=
    match kvs with
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
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @kvsG_state_inG _ hF1 = @kvsG_state_inG _ hF2 ∧
                                           kvs_names_state (kvs_get_names hF1) =
                                           kvs_names_state (kvs_get_names hF2) ⌝%I;
    |}.
  Next Obligation.
    intros.
    destruct hF.
    destruct names.
    unfold kvs_update. simpl.
    destruct kvsG_state_inG0; simpl. unfold kvs_get_names; simpl.
    unfold gen_heapG_get_names; simpl.
    destruct kvs_names_state0; simpl; auto.
    Qed.
  Next Obligation. intros ? [[]] => //=.
                   unfold kvs_update; simpl.
                   destruct kvsG_state_inG0; simpl.
                   unfold kvs_get_names; simpl.
                   unfold gen_heapG_get_names; simpl.
                   auto.
  Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
End kvs_interp.

Section misc_lemmas.
  Context `{kvsG_ctx: inG Σ openR}.

  Theorem openR_frac_split γ (q1 q2 : Qp) x :
    own γ (Cinl ((q1 + q2)%Qp, x) : openR) ⊣⊢ own γ (Cinl (q1, x)) ∗ own γ (Cinl (q2, x)).
  Proof.
    rewrite -own_op.
    f_equiv.
    apply Cinl_equiv.
    apply pair_proper; simpl.
    - rewrite frac_op //.
    - rewrite agree_idemp //.
  Qed.
End misc_lemmas.

Section kvs_lemmas.
  Context `{kvsG_ctx: kvsG Σ}.


  Global Instance kvs_ctx_Timeless kvs: Timeless (kvs_ctx kvs).
  Proof. destruct kvs; apply _. Qed.

  Global Instance kvs_start_Timeless kvs: Timeless (kvs_start kvs).
  Proof. destruct kvs; apply _. Qed.

  Global Instance kvs_restart_Timeless kvs: Timeless (kvs_restart _ kvs).
  Proof. destruct kvs; apply _. Qed.

  Global Instance kvs_open_Persistent (l: loc) : Persistent (kvs_open l).
  Proof. rewrite /kvs_open/Kvs_Opened. apply own_core_persistent. rewrite /CoreId//=. Qed.

  Lemma kvs_closed_auth_uninit_frag:
    kvs_closed_auth -∗ kvs_uninit_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%to_agree_op_inv].
    inversion Heq.
  Qed.

  Lemma kvs_uninit_auth_closed_frag:
    kvs_uninit_auth -∗ kvs_closed_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%to_agree_op_inv].
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

  (* know that we're closed + know value at a particular key *)
  Notation "l k↦ v" := (gen_heap.mapsto (L:=u64) (V:=disk.Block) l (DfracOwn 1) v%V)
                              (at level 20, format "l  k↦ v") : bi_scope.
  Notation "l k↦{ q } v" := (gen_heap.mapsto (L:=u64) (V:=disk.Block) l (DfracOwn q) v%V)
                              (at level 20, q at level 50, format "l  k↦{ q }  v") : bi_scope.
  Lemma kvs_ctx_unify_closed kvs (key: u64) (val: disk.Block):
    kvs_closed_frag -∗ key k↦ val -∗ kvs_ctx kvs -∗ ∃ s, ⌜s !! key = Some val ∧ kvs = Closed s ⌝.
  Proof.
    destruct kvs; try eauto; iIntros "Hclosed_frag Hstate_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_closed_auth_uninit_frag with "[$] [$]") as %[].
    - iExists s.
      iDestruct "Hctx" as "(Hclosed_auth&Hstate_auth)".
      iPoseProof (gen_heap_valid with "Hstate_auth Hstate_frag") as "H".
      iSplit; auto.
      - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
        iDestruct (own_valid_2 with "Huninit_auth Hclosed_frag") as %Hval.
        inversion Hval.
  Qed.

  Lemma kvs_ctx_unify_closed' kvs:
    kvs_closed_frag -∗ kvs_ctx kvs -∗ ⌜∃ s, kvs = Closed s ⌝.
  Proof.
    destruct kvs; try eauto; iIntros "Hclosed_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_closed_auth_uninit_frag with "[$] [$]") as %[].
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
        iDestruct (own_valid_2 with "Huninit_auth Hclosed_frag") as %Hval.
        inversion Hval.
  Qed.

  Lemma kvs_auth_frag_unif (s : gmap u64 disk.Block) (k: u64) (v: disk.Block):
    kvs_auth s -∗ k k↦ v -∗ ∃ s', ⌜s' !! k = Some v ∧ s = s'⌝.
  Proof.
    rewrite /kvs_auth/kvs_frag. iIntros "H1 H2".
    iExists s.
    iPoseProof (gen_heap_valid with "H1 H2") as "H".
    iSplit; auto.
  Qed.

  Lemma kvs_open_unif l l':
    kvs_open l -∗ kvs_open l' -∗ ⌜ l = l' ⌝.
  Proof.
    rewrite /kvs_auth/kvs_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hval.
    rewrite /Kvs_Opened -Cinr_op in Hval.
    assert (l ≡ l') as Heq.
    { eapply to_agree_op_inv. eauto. }
    inversion Heq. by subst.
  Qed.

  Lemma kvs_ctx_unify_uninit kvs:
    kvs_uninit_frag -∗ kvs_ctx kvs -∗ ⌜ kvs = UnInit ⌝.
  Proof.
    destruct kvs; try eauto; iIntros "Huninit_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Huninit_frag") as %Hval.
      inversion Hval as [? Heq%to_agree_op_inv].
      inversion Heq.
    - iDestruct "Hctx" as "(Hauth&Hstate_auth)".
      iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
      inversion Hval.
  Qed.

  Lemma kvs_ctx_unify_opened l kvs:
    kvs_open l -∗ kvs_ctx kvs -∗ ⌜ ∃ vs, kvs = Opened vs l ⌝.
  Proof.
      destruct kvs as [| | | | vs' l']; try eauto; iIntros "Hopen Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (kvs_open_unif with "[$] [$]") as %Heq.
      subst. eauto.
  Qed.

  Lemma kvs_uninit_token_open (l: loc):
    kvs_uninit_auth -∗ kvs_uninit_frag ==∗ kvs_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (Kvs_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma kvs_closed_token_open (l: loc):
    kvs_closed_auth -∗ kvs_closed_frag ==∗ kvs_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    (*Print cmra_update. can transform facts to another fact that is compatible w/others' facts*)
    iMod (own_update _ _ (Kvs_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  (* insert updated keyval *)
  Lemma kvs_state_update s k v1 v2:
    kvs_auth s -∗ k k↦v1 ==∗ kvs_auth (<[k := v2]>s)∗ k k↦ v2.
  Proof.
    unfold kvs_auth. apply gen_heap_update.
  Qed.

(* Not related to physical state yet, just updates to ghost vars*)
End kvs_lemmas.

From Perennial.goose_lang Require Import adequacy.

(* when crashes, ffi_crash_rel: hF[] = instance of type class kvsG *)
(* Program Instance --> define instance of type class, don't need to fill in all fields (craete goal, obligation) *)Program Instance kvs_interp_adequacy:
  @ffi_interp_adequacy kvs_model kvs_interp kvs_op kvs_semantics :=
  {| ffi_preG := kvs_preG;
     ffiΣ := kvsΣ;
     subG_ffiPreG := subG_kvsG;
     ffi_initP := λ σ, σ = UnInit;
     ffi_update_pre := @kvs_update_pre;
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation.
  intros.
  unfold ffi_get_names; simpl.
  unfold kvs_get_names; unfold kvs_update_pre.
  unfold gen_heapG_get_names; simpl.
  destruct names; simpl.
  destruct kvs_names_state0; simpl; auto.
Qed.
Next Obligation.
  (*if in uninit state, can initialize algebra and give ffi start, show that ffi start can be created*)
  (* first part: status *)
  rewrite //=.
  iIntros (Σ hPre σ ->). simpl.
  rewrite /kvs_uninit_auth/kvs_uninit_frag/kvs_frag/kvs_auth.
  iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (gen_heap_name_strong_init ∅) as (names) "(Hctx&Hpts)".
  iFrame. iModIntro.
  iExists {| kvs_names_open := γ1; kvs_names_state := names |}.
  iPoseProof (openR_frac_split γ1 (1/2) (1/2) (to_agree UnInit')) as "HOpen".
  iEval (rewrite -Qp_half_half) in "H".
  iEval (rewrite -frac_op) in "H".
  iDestruct "HOpen" as "[H1 H2]".
  iDestruct ("H1" with "H") as "[H1' H2']".
  iSplitR "H1'"; auto.
  iSplitL "H2'"; auto.
Qed.

Next Obligation. (* restart, crashed to new ffi_state, Hold = old ffiG, ffi_update plugs in new names *)
  iIntros (Σ σ σ' Hcrash Hold) "Hinterp".
  inversion Hcrash; subst.
  monad_inv. inversion H. subst. inversion H1. subst.
  destruct x; monad_inv.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
    (*γ1 is new name, plug into new config name *)
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := kvs_names_state (kvs_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
    * destruct kvsG_state_inG; simpl.
      unfold gen_heapG_update; simpl.
      unfold gen_heapG_get_names; simpl.
      auto.
    * rewrite /kvs_uninit_auth/kvs_uninit_frag/kvs_frag/kvs_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := kvs_names_state (kvs_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
   * destruct kvsG_state_inG; simpl.
      unfold gen_heapG_update; simpl.
      unfold gen_heapG_get_names; simpl.
      auto.
  *
    rewrite /kvs_uninit_auth/kvs_uninit_frag/kvs_frag/kvs_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| kvs_names_open := γ1; kvs_names_state := kvs_names_state (kvs_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/kvs_restart//=.
    iFrame. rewrite comm -assoc. iSplitL ""; first eauto.
   * destruct kvsG_state_inG; simpl.
      unfold gen_heapG_update; simpl.
      unfold gen_heapG_get_names; simpl.
      auto.
   *
    rewrite /kvs_uninit_auth/kvs_uninit_frag/kvs_frag/kvs_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance kvs_spec_ext : spec_ext_op := {| spec_ext_op_field := kvs_op |}.
Instance kvs_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := kvs_model |}.
Instance kvs_spec_ext_semantics : spec_ext_semantics (kvs_spec_ext) (kvs_spec_ffi_model) :=
  {| spec_ext_semantics_field := kvs_semantics |}.
Instance kvs_spec_ffi_interp : spec_ffi_interp kvs_spec_ffi_model :=
  {| spec_ffi_interp_field := kvs_interp |}.
Instance kvs_spec_ty : ext_types (spec_ext_op_field) := kvs_ty.
Instance kvs_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := kvs_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := kvs_interp_adequacy |}.

Context `{invG Σ}.
Context `{crashG Σ}.
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
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | [ H1: context[ match world ?σ with | _ => _ end ], Heq: world ?σ = _ |- _ ] =>
          rewrite Heq in H1
        end.

Lemma ghost_step_init_stuck E j K {HCTX: LanguageCtx K} σ g:
  nclose sN_inv ⊆ E →
  (σ.(@world _ kvs_spec_ffi_model.(@spec_ffi_model_field)) ≠ UnInit) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ g -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ????? Hstep.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv).
  }
  { solve_ndisj. }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ g:
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ kvs_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗
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
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
    eapply H2; eauto.
  }
  { solve_ndisj. }
Qed.

Lemma kvs_closed_init_false E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_closed_frag -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_closed' with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  destruct Heq; subst; auto. congruence.
Qed.

Lemma kvs_opened_init_false l E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma kvs_init_init_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)". (* step one thread *)
    { apply head_prim_step. simpl. constructor 1. econstructor.
      * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
        ** apply fresh_locs_non_null; lia.
        ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
        ** econstructor.
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
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_stuck with "Hj' Hctx H") as "[]".
    { eapply stuck_ExternalOp; first (by eauto).
      apply head_irreducible_not_atomically; [ by inversion 1 | ].
      intros ??????. by repeat (inv_head_step; simpl in *; repeat monad_inv).
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
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) InitOp #())
  -∗ |NC={E}=>
  ∃ (l: loc), j ⤇ K (#l)%V ∗ kvs_open l.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hvals Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_uninit with "[$] [$]") as %Heq.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step. simpl. constructor 1. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** econstructor.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (kvs_uninit_token_open ((fresh_locs (dom (gset loc) σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) (fresh_locs (dom _ σ.(heap))) (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { rewrite //=. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  iMod (gen_heap_alloc_big ∅ kvs_init_s with "Hvals_auth") as "Hgh".
  { apply map_disjoint_empty_r. }
  { iMod ("Hclo" with "[Hσ H Hrest Hgh]") as "_".
    - iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen".
      iDestruct "Hgh" as "[Hgh Hmap]". simpl in *.
      rewrite right_id; auto. rewrite fresh_alloc_equiv_null_non_alloc; iFrame.
    - iModIntro. iExists _. iFrame "Hopen". iFrame.
  }
Qed.

Lemma kvs_uninit_open_false E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_uninit_frag -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
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
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
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
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step. simpl. constructor 1. econstructor.
      * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
        ** apply fresh_locs_non_null; lia.
        ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
        ** econstructor.
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

Lemma ghost_step_kvs_open E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_closed_frag -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) OpenOp #())
  -∗ |NC={E}=>
  ∃ (l: loc), j ⤇ K #l%V ∗ kvs_open l.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (kvs_ctx_unify_closed' with "[$] [$]") as %Heq.
  destruct Heq as [s Heq].
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step. simpl. constructor 1. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** econstructor.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (kvs_closed_token_open ((fresh_locs (dom _ σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) (fresh_locs (dom _ σ.(heap))) (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { rewrite //=. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen". rewrite fresh_alloc_equiv_null_non_alloc. iFrame. }
  iModIntro. iExists _. iFrame "Hopen". iFrame.
Qed.

(* XXX TODO how to return block?
Lemma ghost_step_kvs_get E j K {HCTX: LanguageCtx K} l k v :
  nclose sN ⊆ E →
  spec_ctx -∗
  kvs_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field kvs_spec_ext) GetOp #l #(LitInt k))
  ={E}=∗
  j ⤇ K #(LitLoc l)%V ∗ l ↦ v ∗ kvs_frag k v.
Proof.
  iIntros (?) "(#Hctx&#Hstate) #Hopen Hj".
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
Qed.*)

End spec.
