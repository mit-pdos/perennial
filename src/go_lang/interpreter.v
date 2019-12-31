From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From stdpp Require Import pretty.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.go_lang Require Export locations.
From Perennial.go_lang Require Export lang.
From Perennial Require Export Helpers.Integers.
From Perennial.go_lang Require Import prelude.
From Perennial.go_lang Require Import interpret_types.

From Perennial.go_lang.examples Require Import goose_unittest.
From Perennial.go_lang.ffi Require Import disk.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Instance pretty_u64 : Pretty Integers.u64 :=
  fun x => pretty (word.unsigned x).

Instance pretty_loc : Pretty loc :=
  fun x => pretty x.(loc_car).

(* The analog of ext_semantics for an interpretable external
operation. An ext_step isn't strong enough to let us interpret
ExternalOps. *)
Class ext_interpretable {ext: ext_op} {ffi: ffi_model} :=
  {
    (* fuel, operation, argument, starting state, returns ending val and state *)
    ext_interpret : nat -> external -> val -> StateT state Error val;
  }.

Section go_lang_int.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}
          {Ffi_interpretable: @ext_interpretable ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

(* Probably don't need these since we switched to using Error *)
Instance statet_option_bind : MBind (StateT state option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_option_ret : MRet (StateT state option) :=
  StateT_ret option option_ret.

Instance statet_error_bind : MBind (StateT state Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_error_ret : MRet (StateT state Error) :=
  StateT_ret Error Error_ret.

(* Helper Functions *)
Definition byte_val (v: val) : option byte :=
  match v with
  | LitV (LitByte b) => Some b
  | _ => None
  end.

Fixpoint state_readn (s: state) (l: loc) (n: nat) : option (list val) :=
  match n with
  | O => mret []
  | S m => v <- s.(heap) !! (loc_add l m);
          ls <- state_readn s l m;
          mret (ls ++ [v])
  end.

(* Why is this necessary? I dont understand why I had to do this to
get the types to work. *)
Definition vec_ugh (m : nat) : vec val (m + 1) -> vec val (S m).
intros.
assert ((m + 1)%nat = S m) by lia.
rewrite H in X.
exact X.
Defined.

(* (forall vs, state_readn s l n = Some vs -> length vs = n) is possible to
prove, but (exists vs, state_readn s l n = Some vs /\ length vs = n)
\/ (state_readn s l n = None) was not for some typing reasons (nonconstructive?).

It is simpler to just re-define the same function with a
vector type as state_readn_vec *)
Fixpoint state_readn_vec (s: state) (l: loc) (n: nat) : option (vec val n) :=
  match n with
  | O => mret vnil
  | S m => v <- s.(heap) !! (loc_add l m);
            vtl <- state_readn_vec s l m;
            mret (vec_ugh m $ vapp vtl (vcons v vnil))
  end.

Fixpoint commute_option_list X (a : list (option X)) : option (list X) :=
  match a with
  | [] => Some []
  | cons h t => r <- h; s <- commute_option_list _ t; mret ([r] ++ s)
  end.

Fixpoint commute_option_vec X {n: nat} (a : vec (option X) n) : option (vec X n) :=
  match a with
  | vnil => Some vnil
  | vcons h t => r <- h; s <- commute_option_vec _ t; mret (vcons r s)
  end.


Fixpoint biggest_loc_rec (s: list (prod loc val)) : loc :=
  match s with
    | [] => null
    | (cons a rest) =>
      let other_addr := (loc_car (biggest_loc_rec rest)) in
      match a with
        | (k,_) => let addr := loc_car k in
                  loc_add null (Z.max other_addr addr)
      end
  end.

Definition biggest_loc (σ: state) : loc :=
  let s := gmap_to_list σ.(heap) in
  biggest_loc_rec s.
  
(* Finds the biggest loc in state and adds 1 to it, independent of size *)
Definition find_alloc_location (σ: state) (size: Z) : loc :=
  loc_add (biggest_loc σ) 1.

Print mfail.

(* Interpreter *)
Fixpoint interpret (fuel: nat) (e: expr) : StateT state Error val :=
  match fuel with
  | O => mfail "Fuel depleted"
  | S n =>
    match e with
    | Val v => mret v
    | Var y => mfail ("Unbound variable: " ++ y)
    | Rec f y e => mret (RecV f y e)

    | App e1 e2 => 
      v1 <- interpret n e1;
      v2 <- interpret n e2;
        match v1 with
        | RecV BAnon BAnon ex => interpret n ex
        | RecV BAnon (BNamed y) ex =>
          let e3 := subst y v2 ex in
          interpret n e3
        | RecV (BNamed f) BAnon ex =>
          let e3 := subst f v1 ex in
          interpret n e3
        | RecV (BNamed f) (BNamed y) ex =>
          let e3 := subst f v1 (subst y v2 ex) in
          interpret n e3
        | _ => mfail "App applied to non-function."
        end
          
    | UnOp op e =>
      v <- interpret n e;
        (* mlift because up_op_eval returns an optional *)
        mlift (un_op_eval op v) "UnOp failed."
                   
    | BinOp op e1 e2 =>
      v1 <- interpret n e1;
      v2 <- interpret n e2;
      (* mlift because up_op_eval returns an optional *)
      mlift (bin_op_eval op v1 v2) "BinOp failed."
                    
    | If e0 e1 e2 =>
      c <- interpret n e0;
        match c with
        | LitV (LitBool true) => interpret n e1
        | LitV (LitBool false) => interpret n e2
        | _ => mfail "If applied to non-bool."
        end

    | Pair e1 e2 =>
        a <- interpret n e1;
        b <- interpret n e2;
        mret (PairV a b)
            
    | Fst e =>
      v <- interpret n e;
      match v with
      | PairV v1 v2 => mret v1
      | _ => mfail "Fst applied to non-PairV."
      end

    | Snd e =>
      v <- interpret n e;
      match v with
      | PairV v1 v2 => mret v2
      | _ => mfail "Snd applied to non-PairV."
      end
      
    | InjL e =>
      v <- interpret n e;
      mret (InjLV v)

    | InjR e =>
      v <- interpret n e;
      mret (InjRV v)

    | Case e0 e1 e2 =>
      v <- interpret n e0;
      match v with
      | InjLV v' =>
        interpret n (App e1 (Val v'))
      | InjRV v' =>
        interpret n (App e2 (Val v'))
      | _ => mfail "Case of non-inj."
      end

    | Fork e => mfail "NotImpl: fork."

    | Primitive0 (PanicOp s) => mfail ("Panic: " ++ s)

    (* In head_step, alloc nondeterministically allocates at any valid
    location. We'll just pick the first valid location. *)
    | Primitive1 AllocStructOp e =>
      structv <- interpret n e;
      s <- mget;
      let l := find_alloc_location s (length (flatten_struct structv)) in
      _ <- mput (state_insert_list l (flatten_struct structv) s);
        mret (LitV (LitLoc l))
             
    | Primitive2 AllocNOp e1 e2 =>
      initv <- interpret n e2;
      lenv <- interpret n e1;
      match lenv with
      | LitV (LitInt lenz) => 
          (* We must allocate a list of length lenz where every entry
          is initv. state_init_heap does most of the work. *)
          s <- mget;
          let l := find_alloc_location s (int.val lenz) in
          _ <- mput (state_init_heap l (int.val lenz) initv s);
          mret (LitV (LitLoc l))
      | _ => mfail "Alloc with non-integer argument."
      end
        
    | Primitive1 LoadOp e =>
      addrv <- interpret n e;
        match addrv with
        | LitV (LitInt l) =>
          mfail "Load at int instead of loc"
          | LitV (LitLoc l) =>
            (* Since Load of an address with nothing doesn't step, we
            can lift from the option monad into the StateT option
            monad here (we mfail "NotImpl" if v is None). *)
            s <- mget;
            v <- mlift (s.(heap) !! l) ("Load Failed: " ++ (pretty l));
            mret v
          | _ => mfail "Load with non-location argument."
        end
          
    | Primitive2 StoreOp e1 e2 =>
      addrv <- interpret n e1;
      val <- interpret n e2;
        match addrv with
        | LitV (LitInt l) =>
          let l' := loc_add null (int.val l) in
            s <- mget;
            _ <- mput (set heap <[l':=val]> s);
            mret (LitV LitUnit)
          | LitV (LitLoc l) => 
            s <- mget;
            _ <- mput (set heap <[l:=val]> s);
            mret (LitV LitUnit)
          | _ => mfail "Store with non-location argument."
        end
          
    | Primitive1 DecodeInt64Op e =>
      v <- interpret n e;
        l <- mlift (match v with
                   | LitV (LitLoc l) => Some l
                   | _ => None
                   end)
          "DecodeInt64Op argument not a LitLoc.";
        s <- mget;
        vs <- mlift (
             rs <- state_readn s l 8;
             commute_option_list _ (map byte_val rs)
           ) "DecodeInt64Op: Read failed.";
        (* vs is list byte *)
        mret (LitV $ LitInt (le_to_u64 vs))
            
    | Primitive2 EncodeInt64Op e1 e2 =>
      v1 <- interpret n e1;
      v2 <- interpret n e2;
      s <- mget;
      v <- mlift (match v1 with
                 | LitV (LitInt v) => Some v
                 | _ => None
                 end)
        "EncodeInt64Op 1st arg not LitInt";
      l <- mlift (match v2 with
                 | LitV (LitLoc l) => Some l
                 | _ => None
                 end)
        "EncodeInt64Op 2nd arg not LitLoc";
      (* TODO: Check all 8 places are already in the heap? *)
      _ <- mput (state_insert_list l (byte_vals $ u64_le v) s);
        mret (LitV LitUnit)

    | Primitive1 DecodeInt32Op e => mfail "NotImpl: decode."
    | Primitive2 EncodeInt32Op e1 e2 => mfail "NotImpl: encode."
                                             
    | Primitive1 ObserveOp e =>
      v <- interpret n e;
      _ <- mupdate (set trace (fun tr => tr ++ [v]));
      mret (LitV LitUnit)

    | Primitive0 _ => mfail "NotImpl: unrecognized primitive0."
    | Primitive1 _ _ => mfail "NotImpl: unrecognized primitive1."
    | Primitive2 _ _ _ => mfail "NotImpl: unrecognized primitive2."

    | ExternalOp op e =>
      v <- interpret n e;
      ext_interpret n op v

    (* Won't interpret anything involving prophecy variables. *)
    | CmpXchg e0 e1 e2 => mfail "NotImpl: cmpxchg."   (* ignore *)
    | NewProph => mfail "NotImpl: prophecy variable." (* ignore *)
    | Resolve ex e1 e2 => mfail "NotImpl: resolve."   (* ignore *)
    end
  end.

Lemma nsteps_transitive : forall L n m p1 p2 p3 l1 l2,
    @nsteps L n p1 l1 p2 ->
    @nsteps L m p2 l2 p3 ->
    @nsteps L (n + m) p1 (l1 ++ l2) p3.
Proof.
  induction n.
  { (* n = 0 *)
    intros.
    inversion H.
    simpl.
    exact H0.
  }
  { (* S n *)
    intros.
    inversion H.
    rewrite <- app_assoc.
    eapply nsteps_l.
    {
      exact H2.
    }
    eapply IHn; [exact H3|exact H0].
  }
Qed.

Lemma list_empty_surroundings : forall X (e:X) (e':X) (t1:list X) (t2:list X),
    [e] = t1 ++ e' :: t2 ->
    (t1 = []) /\ (t2 = []) /\ (e = e').
Proof.
  intros.
  assert (t1 = []).
  {
    destruct t1; [trivial|].
    inversion H.
    pose proof (app_cons_not_nil t1 t2 e').
    contradiction.
  }
  rewrite H0 in H.
  split; [exact H0|].
  assert (t2 = []).
  {
    destruct t2; [trivial|].
    inversion H.
  }
  rewrite H1 in H.
  inversion H.
  split; eauto.
Qed.

Lemma list_empty_surroundings_strong : forall X (e:X) (e':X) (t1:list X) (t2:list X) (efs:list X),
    [e] = t1 ++ e' :: t2 ++ efs ->
    (t1 = []) /\ (t2 = []) /\ (efs = []) /\ (e = e').
Proof.
  intros.
  assert (t1 = []).
  {
    destruct t1; [trivial|].
    inversion H.
    pose proof (app_cons_not_nil t1 (t2 ++ efs) e').
    contradiction.
  }
  rewrite H0 in H.
  split; [exact H0|].
  assert (t2 = []).
  {
    destruct t2; [trivial|].
    inversion H.
  }
  rewrite H1 in H.
  inversion H.
  split; eauto.
Qed.

Lemma nsteps_no_thread_destroy `{!@LanguageCtx Λ K} n ρ e σ l:
  @nsteps Λ n ρ l ([e], σ) ->
  exists e' σ', ρ = ([e'], σ').
Proof.
  generalize ρ l e σ.
  induction n.
  {
    intros.
    inversion H0.
    do 2 eexists; reflexivity.
  }
  {
    intros.
    inversion H0; try eauto.
    rewrite <- H4 in *.
    pose proof (IHn _ _ _ _ H3) as IH.
    destruct IH as (e' & IH').
    destruct IH' as (σ' & IH'').
    rewrite IH'' in H2.
    inversion H2.
    inversion H8.
    pose proof (list_empty_surroundings_strong _ _ _ _ _ _ H11) as one_thread.
    inversion one_thread.
    inversion H13.
    inversion H15.
    rewrite H10 in H7.
    rewrite H14 in H7.
    simpl in H7.
    do 2 eexists; exact H7.
  }
Qed.

Lemma nsteps_ctx `{!@LanguageCtx Λ K} n e1 e2 σ1 σ2 l:
@nsteps Λ n ([e1], σ1) l ([e2], σ2) →
@nsteps Λ n ([K e1], σ1) l ([K e2], σ2).
Proof using Ffi_interpretable ext ffi ffi_semantics. (*coq told me to do this*)
  generalize e1 e2 σ1 σ2 l.
  induction n.
  { (* n = 0 *)
    intros e e' σ σ' l' nstep_ooc; inversion nstep_ooc. (*nsteps hypothesis out-of-context*)
    apply nsteps_refl. }
  { (* S n *)
    intros e e' σ σ' l' nstep_ooc.
    inversion nstep_ooc as [|n' ρ1 ρ2 ρ3 κ κs step_ooc nstep_ooc_rest].
    pose proof (nsteps_no_thread_destroy _ _ _ _ _ nstep_ooc_rest) as intermediate_cfg_has_one_thread.
    inversion intermediate_cfg_has_one_thread as (e'' & (σ'' & P)).
    rewrite P in nstep_ooc_rest.
    pose proof (IHn _ _ _ _ _ nstep_ooc_rest) as nstep_ic_rest. (*nsteps in-context*)
    rewrite P in step_ooc.
    inversion step_ooc as [e_s σ_s e''_s σ''_s spawned_threads t1 t2 Pes Pe''s prim_step_e_e''].
    inversion Pes as [Pe].
    rewrite <- H4.
    rewrite <- H4 in prim_step_e_e''.
    pose proof (list_empty_surroundings _ _ _ _ _ Pe).
    inversion H5.
    inversion H7.
    rewrite <- H9 in prim_step_e_e''.
    inversion Pe''s as [Pe''].
    rewrite <- H10 in prim_step_e_e''.
    pose proof (list_empty_surroundings _ _ _ _ _ Pe'').
    inversion H11.
    inversion H13.
    pose proof (app_eq_nil t2 spawned_threads H14).
    inversion H16.
    rewrite <- H15 in prim_step_e_e''.
    rewrite H18 in prim_step_e_e''.
    pose proof (fill_step _ _ _ _ _ _ prim_step_e_e'') as prim_step_ic.
    eapply nsteps_l; [|exact nstep_ic_rest].
    eapply step_atomic with (t3 := []) (t4 := []); [| |exact prim_step_ic]; eauto.
  }
Qed.

(* Always apply step_atomic with t1, t2 as [] since we don't care
    about threading. *)
Ltac single_step :=
  eapply nsteps_l; [|apply nsteps_refl];
  eapply step_atomic with (t1:=[]) (t2:=[]); [simpl; reflexivity|simpl; reflexivity|apply head_prim_step].

Ltac interpret_bind :=
  match goal with
  | [H : runStateT (mbind (fun x => @?F x) ?ma) ?σ = _ |- _] =>
    match goal with
    | [ma_result : runStateT ma σ = Works _ (?v, ?σ') |- _] =>
      try rewrite (runStateT_Error_bind _ _ _ _ _ _ F ma_result) in H
    | [ma_result : runStateT ma σ = Fail _ ?s |- _] =>
      try rewrite (runStateT_Error_bind_false _ _ _ _ F s ma_result) in H; try inversion H
    | _ => fail
    end
  | _ => fail
  end.

Theorem interpret_ok : forall (n: nat) (e: expr) (σ: state) (v: val) (σ': state),
    (((runStateT (interpret n e) σ) = Works _ (v, σ')) ->
     exists m l, @nsteps heap_lang m ([e], σ) l ([Val v], σ')).
Proof.
  intros n. induction n.
  { by intros []. }

  intros e σ v σ' interp. destruct e; simpl; inversion interp; simpl.
    
  (* Val *)
  { eexists. eexists. apply nsteps_refl. }
  (* Var *)
  
  (* Rec *)
  { do 2 eexists.
    single_step.
    apply RecS.
  }
  
  (* App *)
  { pose (IHn e2 σ) as step1.
    { admit. }
  }

  (* UnOp *)
  { destruct (runStateT (interpret n e) σ) eqn:interp_e; [|interpret_bind].
    destruct v0. pose (IHn e σ v0 s interp_e) as IH.
    interpret_bind.
    inversion H0.
    destruct (un_op_eval op v0) eqn:uo_eval; inversion H1.
    destruct IH as (m & IH').
    destruct IH' as (l & e_to_v0).
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [UnOp op e] -> [UnOp op v0] *)
      eapply nsteps_ctx.
      apply e_to_v0.
    }
    {
      (* [UnOp op v0] -> [v1] *)
      single_step.
      rewrite H3.
      apply UnOpS.
      rewrite H2 in uo_eval.
      apply uo_eval.
    }
  }

  (* BinOp *)
  {
    (* If e1 doesn't work, interpret_bind finds contradiction with H0 *)
    destruct (runStateT (interpret n e1) σ) eqn:interp_e1; [|interpret_bind].
    destruct v0. pose proof (IHn e1 σ v0 s interp_e1) as IHe1.
    interpret_bind.
    (* Same for e2 *)
    destruct (runStateT (interpret n e2) s) eqn:interp_e2; [|interpret_bind].
    destruct v1. pose proof (IHn e2 s v1 s0 interp_e2) as IHe2.
    interpret_bind.
    inversion H0.
    destruct (bin_op_eval op v0 v1) eqn:bo_eval; inversion H1.
    destruct IHe1 as (m & IHe1').
    destruct IHe2 as (m' & IHe2').
    destruct IHe1' as (l & e1_to_v0).
    destruct IHe2' as (l' & e2_to_v1).
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [BinOp op e1 e2] -> [BinOp op v0 e2] *)
      pose proof (@nsteps_ctx _ (fill [(BinOpLCtx op e2)]) _ m e1 v0 σ s l e1_to_v0) as e1_to_v0_ctx.
      simpl in e1_to_v0_ctx.
      exact e1_to_v0_ctx.
    }
    { (* [BinOp op v0 e2] -> [v] *)
      eapply nsteps_transitive.
      { (* [BinOp op v0 e2] -> [BinOp op v0 v1] *)
        pose proof (@nsteps_ctx _ (fill [(BinOpRCtx op v0)]) _ m' e2 v1 s s0 l' e2_to_v1) as e2_to_v1_ctx.
        simpl in e2_to_v1_ctx.
        exact e2_to_v1_ctx.
      }
      { (* [BinOp op v0 v1] -> [v] *)
        single_step.
        rewrite H3.
        apply BinOpS.
        rewrite H2 in bo_eval.
        apply bo_eval.
      }
    }
  }

  (* If *)
  { admit. }

  (* Pair *)
  { admit. }

  (* Fst *)
  { destruct (runStateT (interpret n e) σ) eqn:interp_e; [|interpret_bind].
    destruct v0.
    pose (IHn e σ v0 s interp_e) as IH.
    interpret_bind.
    inversion H0.
    destruct (v0) eqn:v0_eval; inversion H1.
    destruct IH as (m & IH').
    destruct IH' as (l & e_to_v0).
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [Fst e] -> [Fst v0] *)
      eapply nsteps_ctx.
      apply e_to_v0.
    }
    {
      (* [Fst v0] -> [v] *)
      single_step.
      rewrite H2.
      rewrite H3.
      apply FstS.
    }
  }

  (* Snd *)
  { destruct (runStateT (interpret n e) σ) eqn:interp_e; [|interpret_bind].
    destruct v0.
    pose (IHn e σ v0 s interp_e) as IH.
    interpret_bind.
    inversion H0.
    destruct (v0) eqn:v0_eval; inversion H1.
    destruct IH as (m & IH').
    destruct IH' as (l & e_to_v0).
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [Snd e] -> [Snd v0] *)
      eapply nsteps_ctx.
      apply e_to_v0.
    }
    {
      (* [Snd v0] -> [v] *)
      single_step.
      rewrite H2.
      rewrite H3.
      apply SndS.
    }
  }
    
  }

Admitted.
     
(* First attempt at a theorem statement. Above Theorem probably better. *)
Theorem interpret_ok_2 : forall (n: nat) (e: expr) (σ: state),
    match (runStateT (interpret n e) σ) with
    | Fail _ _ => True
    (* Why are heap_lang exprs the same as expr here? They're both
    parameterized, but I don't know where heap_lang sets it to be the
    same. *)
    (* l is a list of observations, which we don't care about right now?
       m the number of steps it takes the expr to resolve using heap_lang steps. *)
    | Works _ (v, σ') => exists m l, @nsteps heap_lang m ([e], σ) l ([Val v], σ')
    end.
Proof.
Admitted.

(* Testing *)
Definition testRec : expr :=
  (rec: BAnon BAnon :=
     #3 + #3).
     
Definition literalCast: expr :=
  λ: <>,
    let: "x" := #2 in
    (Var "x") + #2.

Definition testIfStatement: expr :=
  λ: <>,
    let: "m" := #2 in
    (if: (Var "m") > #3
    then #3
    else #1).

Definition testMatch: val :=
  λ: "x",
  match: (Var "x") with
    InjL "x1" => #3 + (Var "x1")
  | InjR "x1" => #4 + (Var "x1")
  end.

End go_lang_int.

Definition startstate : state := inhabitant.

Instance statet_disk_option_bind : MBind (StateT state option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_disk_option_ret : MRet (StateT state option) :=
  StateT_ret option option_ret.

Instance statet_disk_error_bind : MBind (StateT state Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_disk_error_ret : MRet (StateT state Error) :=
  StateT_ret Error Error_ret.

Definition read_block_from_state (σ: state) (l: loc) : option Block.
  pose (vs <- state_readn σ l block_bytes; commute_option_list _ (map byte_val vs)) as maybe_list.
Abort.

Fixpoint disk_interpret (fuel: nat) (op: DiskOp) (v: val) : StateT state Error val :=
  match fuel with
    | O => mfail "Fuel depleted"
    | S n =>
      match (op, v) with
      | (ReadOp, (LitV (LitInt a))) => 
        σ <- mget;
        b <- mlift (σ.(world) !! a) ("ReadOp: No block at address " ++ (pretty a));
        let l := find_alloc_location σ 4096 in
        _ <- mput (state_insert_list l (Block_to_vals b) σ);
        mret (LitV (LitLoc l))
      | (WriteOp, (PairV (LitV (LitInt a)) (LitV (LitLoc l)))) =>
        σ <- mget;
        b <- mlift (
            (* A block must be a vec of length 4096, so we need to use
               state_readn_vec to preserve the length information *)
            (* vs : vec val 4096 *)
             vs <- state_readn_vec σ l 4096;
             (* (vmap byte_val vs) : vec (option byte) 4096 *)
               commute_option_vec _ (vmap byte_val vs)
           ) "WriteOp: Read from heap failed";
        _ <- mput (set world <[ a := b ]> σ);
          mret (LitV (LitUnit))
       | _ => mfail "NotImpl disk_interpret"
      end
  end.

Instance disk_interpretable : @ext_interpretable disk_op disk_model :=
  { ext_interpret := disk_interpret; }.

Compute (runStateT (interpret 10 (AllocN #1 (zero_val uint32T))) startstate).
Compute (runStateT (interpret 10 (useSlice2 #0)) startstate).
Compute (runStateT (interpret 10 (returnTwoWrapper #3)) startstate).

Compute (runStateT (interpret 10 (testStore #0)) startstate).
Compute (runStateT (interpret 10 (testRec #0)) startstate).

Definition runs_to (p: expr) (v: val) :=
  exists σ, runStateT (interpret 100 p) startstate = Works (val*state) (v, σ).
Notation "p ~~> v" := (ex_intro _ _ eq_refl : runs_to p v) (at level 70).

Example run_testStore := testStore #0 ~~> #3.
Example run_testRec := testRec #0 ~~> #6.

Compute (runStateT (interpret 10 ConstWithArith) startstate).
Compute (runStateT (interpret 10 (literalCast #0)) startstate).

Compute (fst <$> (runStateT (interpret 15 (useSliceIndexing #0)) startstate)).
Compute (fst <$> (runStateT (interpret 7 (testLongSlice #0)) startstate)).

(* Compute the pmap heap but not the proofs *)
Compute ((fun p => (fst p, (snd p).(heap).(gmap_car).(pmap.pmap_car))) <$> (runStateT (interpret 21 (testUInt64EncDec #3214405)) startstate)).

Compute (runStateT (interpret 10 (testIfStatement #0)) startstate).
Compute (runStateT (interpret 10 (testMatch (InjL #2))) startstate).
Compute (runStateT (interpret 10 (testMatch (InjR #2))) startstate).

Compute (runStateT (interpret 16 (useMap #0)) startstate).

Compute (runStateT (interpret 10 (ReassignVars #0)) startstate).
