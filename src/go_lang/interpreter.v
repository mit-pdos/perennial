From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From stdpp Require Import pretty.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.go_lang Require Export locations.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import prelude.
From Perennial.go_lang Require Import interpret_types.

From Perennial.go_lang.examples Require Import goose_unittest.
From Perennial.go_lang.ffi Require Import disk.
Require Import Program.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Instance pretty_u64 : Pretty Integers.u64 :=
  fun x => pretty (word.unsigned x).

Instance pretty_loc : Pretty loc :=
  fun x => pretty x.(loc_car).

(* The step relation is transitive. Doing n steps and then m steps is
the same as doing (n + m) steps.

Useful in interpret_ok for splitting goals like [If e0 e1 e2] ~~> [v]
into [If e0 e1 e2] ~~> [If #true e1 e2] and [If #true e1 e2] ~~> [v]. *)
Lemma nsteps_transitive : forall L n m p1 p2 p3 l1 l2,
    @language.nsteps L n p1 l1 p2 ->
    @language.nsteps L m p2 l2 p3 ->
    @language.nsteps L (n + m) p1 (l1 ++ l2) p3.
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
    eapply language.nsteps_l.
    {
      exact H2.
    }
    eapply IHn; [exact H3|exact H0].
  }
Qed.


(* Helper used for proving that no threads are spawned during an interpreter
step (this applies to any step except [Fork], which we don't
implement). *)
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

(* Another helper, but with efs. *)
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

(* No threads are destroyed during any number of steps in the
language. If we know that [ρ ~~> ([e], σ)] in n steps, then we know that
ρ contained a list of expressions with only one element. *)
Lemma nsteps_no_thread_destroy `{!@LanguageCtx Λ K} n ρ e σ l:
  @language.nsteps Λ n ρ l ([e], σ) ->
  exists e' σ', ρ = ([e'], σ'). (* We learn that ρ steps to something that only has one thread. *)
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

(* If we know a step is valid outside of the context, then it is valid
within a context. *)
Lemma nsteps_ctx `{!@LanguageCtx Λ K} n e1 e2 σ1 σ2 l:
@language.nsteps Λ n ([e1], σ1) l ([e2], σ2) →
@language.nsteps Λ n ([K e1], σ1) l ([K e2], σ2).
Proof.
  generalize e1 e2 σ1 σ2 l.
  induction n.
  { (* n = 0 *)
    intros e e' σ σ' l' nstep_ooc; inversion nstep_ooc. (* nsteps hypothesis out-of-context *)
    apply language.nsteps_refl. }
  { (* S n *)
    intros e e' σ σ' l' nstep_ooc.
    inversion nstep_ooc as [|n' ρ1 ρ2 ρ3 κ κs step_ooc nstep_ooc_rest].
    pose proof (nsteps_no_thread_destroy _ _ _ _ _ nstep_ooc_rest) as intermediate_cfg_has_one_thread.
    inversion intermediate_cfg_has_one_thread as (e'' & (σ'' & P)).
    rewrite P in nstep_ooc_rest.
    pose proof (IHn _ _ _ _ _ nstep_ooc_rest) as nstep_ic_rest. (* nsteps in-context *)
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
    eapply language.nsteps_l; [|exact nstep_ic_rest].
    eapply step_atomic with (t3 := []) (t4 := []); [| |exact prim_step_ic]; eauto.
  }
Qed.

(* Deals with monadic wrappers around head_trans. *)
Ltac head_step :=
  rewrite /= /head_step /=; repeat (monad_simpl; simpl).

(* Suppose we want to show that [a -> b] in 1 step. Then, nsteps
doesn't have a constructor for stepping just once. Instead we have to
use the nsteps_l constructor, which splits our goal into [a -> b] and
[b ~~> b]. We can then apply step_atomic for the first goal, and the
second is just nsteps_refl.

Note that we always apply step_atomic with t1, t2 as [] since we don't
care about threading. *)
Ltac single_step :=
  eapply language.nsteps_l; [|apply language.nsteps_refl];
  eapply step_atomic with (t1:=[]) (t2:=[]); [simpl; reflexivity|simpl; reflexivity|apply head_prim_step; head_step].

(* Given that the first part of a computation succeeds, rewrites the
hypothesis to be about the rest of the computation. If the first part
fails, deduces a contradiction. *)
Ltac runStateT_bind :=
  match goal with
  | [H : runStateT (mbind (fun x => @?F x) ?ma) ?σ = _ |- _] =>
    match goal with
    | [ma_result : runStateT ma σ = Works _ (?v, ?σ') |- _] =>
      try rewrite (runStateT_Error_bind _ _ _ _ _ _ F ma_result) in H
    | [ma_result : runStateT ma σ = Fail _ ?s |- _] =>
      (* If we're in a Fail case, inversion completes the subgoal. *)
      try rewrite (runStateT_Error_bind_false _ _ _ _ F s ma_result) in H; try inversion H
    | _ => fail
    end
  | _ => fail
  end.

Section go_lang_int.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

  (* The analog of ext_semantics for an interpretable external
     operation. An ext_op transition isn't strong enough to let us interpret
     ExternalOps, so we need an executable interpretation of them. *)
  Class ext_interpretable :=
    {
      ext_interpret_step : external -> val -> StateT state Error expr;
      ext_interpret_ok : forall (eop : external) (arg : val) (result : expr) (σ σ': state),
          (runStateT (ext_interpret_step eop arg) σ = Works _ (result, σ')) ->
          exists m l, @language.nsteps heap_lang m ([ExternalOp eop (Val arg)], σ) l ([result], σ');
    }.

  Context {ext_interpretable : ext_interpretable}.

  (* Necessary because mbind and mret implicitly need instances of
  MBind and MRet, respectively. *)
  Instance statet_error_bind : MBind (StateT state Error) :=
    StateT_bind Error Error_fmap Error_join Error_bind.
  Instance statet_error_ret : MRet (StateT state Error) :=
    StateT_ret Error Error_ret.

   (* Given a location l, reads n places from the heap starting at l
   and returns a vec.
   
   Used for disk writes. Blocks on the disk are vecs, so when we read
   something from the heap to store on the disk, we need to return it
   as a vec. *)
  Fixpoint state_readn_vec (s: state) (l: loc) (n: nat) : option (vec (nonAtomic val) n) :=
    match n with
    | O => mret vnil
    | S m => v <- s.(heap) !! l;
              vtl <- state_readn_vec s (loc_add l 1) m;
              mret (vcons v vtl)
    end.

  (* Option commuting lemmas. Note that if any element in the initial
  structure is None, we return None for the whole computation. *)
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

  Fixpoint biggest_loc_rec {X} (s: list (prod loc X)) : loc :=
    match s with
    | [] => null
    | (cons a rest) =>
      let other_addr := (loc_car (biggest_loc_rec rest)) in
      match a with
      | (k,_) => let addr := loc_car k in
                loc_add null (Z.max other_addr addr)
      end
    end.

  Lemma biggest_loc_rec_ok ps :
    forall l l' (v: nonAtomic val),
      ({| loc_car := l |}, v) ∈ ps ->
      biggest_loc_rec ps = {| loc_car := l' |} ->
      l' >= l.
  Proof.
    induction ps as [|hd].
    { (* empty list *)
      intros.
      inversion H.
    }
    { (* hd :: ps *)
      intros l l' v.
      unfold elem_of.
      unfold elem_of in IHps.
      pose ({| loc_car := l |}, v) as p.
      fold p.
      intros p_in_ps.
      pose proof (elem_of_cons ps p hd) as where_is_p.
      rewrite -> where_is_p in p_in_ps.
      destruct p_in_ps.
      { (* p :: ps *)
        rewrite <- H.
        simpl.
        intros.
        inversion H0.
        lia.
      }
      { (* hd :: (p in here) *)
        unfold p, elem_of in H.
        simpl.
        destruct (biggest_loc_rec ps) as [l_old] eqn:bloc_old.
        pose proof (IHps l l_old _ H).
        assert (l_old >= l) by (apply H0; reflexivity).
        intros.
        destruct hd.
        inversion H2.
        lia.
      }
    }
  Qed.

  Definition biggest_loc (σ: state) : loc :=
    let s := gmap_to_list σ.(heap) in
    biggest_loc_rec s.

  Lemma biggest_loc_ok (σ: state) :
    forall l l' v,
      ({| loc_car := l |}, v) ∈ gmap_to_list (heap σ) ->
      biggest_loc σ = {| loc_car := l' |} ->
      l' >= l.
  Proof using ext ffi ffi_semantics.
    intros l l' v elem bloc.
    unfold biggest_loc in bloc.
    apply (biggest_loc_rec_ok _ _ _ _ elem bloc).
  Qed.
  
  (* Finds the biggest loc in state and adds 1 to it, independent of size. *)
  Definition find_alloc_location (σ: state) (size: Z) : loc :=
    loc_add (biggest_loc σ) 1.

  (* Guarantees find_alloc_location returns a location that is the
  start of a fresh range of length 'bound'. *)
  Lemma find_alloc_location_fresh :
    forall s bound, isFreshTo bound s (find_alloc_location s bound).
  Proof using ext ffi ffi_semantics.
    intros s bound i i_gt_z i_lt_len.
    destruct (find_alloc_location s bound +ₗ i) as [l] eqn:fal.
    destruct (heap s !! {| loc_car := l |}) eqn:s_val; [|by reflexivity].
    unfold find_alloc_location in fal.
    pose proof elem_of_map_to_list (heap s) {| loc_car := l |} n as mtl_iff.
    pose proof s_val as mtl_val.
    rewrite <- mtl_iff in mtl_val.
    unfold map_to_list in mtl_val.
    destruct (biggest_loc s) as [l'] eqn:blocs.
    pose proof biggest_loc_ok s _ _ _ mtl_val blocs as blok.
    inversion fal.
    lia.
  Qed.

  Lemma find_alloc_location_ok (v0 : val) :
    ∀ s (i : Z) ,
      0 ≤ i →
      i < strings.length (flatten_struct v0) →
      heap s !! (find_alloc_location s (strings.length (flatten_struct v0)) +ₗ i) =
      None.
  Proof using ext ffi ffi_semantics.
    intros.
    pose proof (find_alloc_location_fresh s (strings.length (flatten_struct v0))).
    eauto.
  Qed.

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
        v2 <- interpret n e2;
          v1 <- interpret n e1;
          match v1 with
          | RecV f y ex =>
            let e3 := subst' y v2 (subst' f v1 ex) in
            interpret n e3
          | _ => mfail "App applied to non-function"
          end
            
      | UnOp op e =>
        v <- interpret n e;
          (* mlift because up_op_eval returns an optional *)
          mlift (un_op_eval op v) "UnOp failed"
                
      | BinOp op e1 e2 =>
        v1 <- interpret n e1;
          v2 <- interpret n e2;
          (* mlift because up_op_eval returns an optional *)
          mlift (bin_op_eval op v1 v2) "BinOp failed"
                
      | If e0 e1 e2 =>
        c <- interpret n e0;
          match c with
          | LitV (LitBool true) => interpret n e1
          | LitV (LitBool false) => interpret n e2
          | _ => mfail "If applied to non-Bool"
          end

      | Pair e1 e2 =>
        a <- interpret n e1;
          b <- interpret n e2;
          mret (PairV a b)
               
      | Fst e =>
        v <- interpret n e;
          match v with
          | PairV v1 v2 => mret v1
          | _ => mfail "Fst applied to non-PairV"
          end

      | Snd e =>
        v <- interpret n e;
          match v with
          | PairV v1 v2 => mret v2
          | _ => mfail "Snd applied to non-PairV"
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
          | _ => mfail "Case of non-Inj"
          end

      | Fork e => mfail "NotImpl: Fork"

      | Primitive0 p =>
        match p in (prim_op args0) return StateT state Error val with
        | PanicOp s => mfail ("Panic: " ++ s)
        end

      | Primitive1 p e =>
        match p in (prim_op args1) return StateT state Error val with
        | AllocStructOp =>
          (* In head_trans, alloc nondeterministically allocates at any
           valid location. We'll just pick the first valid location. *)
          structv <- interpret n e;
            s <- mget;
            let l := find_alloc_location s (length (flatten_struct structv)) in
            _ <- mput (state_insert_list l (flatten_struct structv) s);
              mret (LitV (LitLoc l))
        | PrepareWriteOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("Load Failed: " ++ (pretty l));
                match nav with
                | Reading v 0 => _ <- mupdate (set heap <[l:=Writing]>);
                                  mret (LitV LitUnit)
                | _ => mfail "Race while writing"
                end
            | _ => mfail "Load with non-location argument"
            end
        | LoadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitInt l) =>
              mfail "Load at int instead of loc"
            | LitV (LitLoc l) =>
              (* Since Load of an address with nothing doesn't step,
                 we can lift from the option monad into the StateT option
                 monad here (we mfail "NotImpl" if v is None). *)
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("Load Failed: " ++ (pretty l));
                match nav with
                | Reading v 0 => mret v
                | _ => mfail "Race while reading"
                end
            | _ => mfail "Load with non-location argument"
            end
        | InputOp =>
          v <- interpret n e;
            match v with
            | LitV selv =>
              σ <- mget;
                let x := σ.(oracle) σ.(trace) selv in
                _ <- mupdate (set trace (fun tr => [In_ev selv (LitInt x)] ++ tr));
                  mret (LitV (LitInt x))
            | _ => mfail "Input with non-literal selector"
            end
        | OutputOp =>
          v <- interpret n e;
            match v with
            | LitV v =>
              _ <- mupdate (set trace (fun tr => [Out_ev v] ++ tr));
                mret (LitV LitUnit)
            | _ => mfail "Output with non-literal value"
            end
        | StartReadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("StartReadOp Failed: " ++ (pretty l));
                match nav with
                | Reading v n => _ <- mupdate (set heap <[l:=Reading v (S n)]>);
                                  mret v
                | _ => mfail "StartReadOp: Race while writing"
                end
            | _ => mfail "StartReadOp with non-location argument"
            end
        | FinishReadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("FinishReadOp Failed: " ++ (pretty l));
                match nav with
                | Reading v (S n) => _ <- mupdate (set heap <[l:=Reading v n]>);
                                      mret (LitV LitUnit)
                | Reading v 0 => mfail "FinishReadOp: Not being read"
                | _ => mfail "FinishReadOp: Race while writing"
                end
            | _ => mfail "FinishReadOp with non-location argument"
            end
        end

      | Primitive2 p e1 e2 =>
        match p in (prim_op args2) return StateT state Error val with
        | AllocNOp =>
          lenv <- interpret n e1;
            initv <- interpret n e2;
            match lenv with
            | LitV (LitInt lenz) => 
              if (Z.leb (int.val lenz) 0) then
                mfail "AllocN with size 0 or lower"
              else
                (* We must allocate a list of length lenz where every entry
                   is initv. state_init_heap does most of the work. *)
                s <- mget;
                let l := find_alloc_location s (int.val lenz) in
                _ <- mput (state_init_heap l (int.val lenz) initv s);
                  mret (LitV (LitLoc l))
            | _ => @mfail state _ "Alloc with non-integer argument"
            end
        | FinishStoreOp =>
          addrv <- interpret n e1;
            val <- interpret n e2;
            match addrv with
            | LitV (LitLoc l) => 
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("Load failed: " ++ (pretty l));
                match nav with
                | Writing => 
                  _ <- mput (set heap <[l:=Free val]> s);
                    mret (LitV LitUnit)
                | _ => mfail "FinishStoreOp on non-writing location"
                end
            | _ => @mfail state _ "Store with non-location argument"
            end
        end

      | ExternalOp op e =>
        v <- interpret n e;
          e' <- ext_interpret_step op v;
          interpret n e'

      | CmpXchg e0 e1 e2 =>
          addrv <- interpret n e0;
            v1 <- interpret n e1;
            v2 <- interpret n e2;
            match addrv with
            | LitV (LitLoc l) =>
              s <- mget;
                nav <- mlift (s.(heap) !! l) ("CmpXchg load failed: " ++ (pretty l));
                match nav with
                | Reading vl 0 =>
                  b <- mlift (bin_op_eval EqOp vl v1) "CmpXchg BinOp failed";
                  match b with
                  | LitV (LitBool true) => _ <- mput (set heap <[l:=Free v2]> s);
                           mret (PairV vl #true)
                  | LitV (LitBool false) => mret (PairV vl #false)
                  | _ => mfail "CmpXchg EqOp did not return a boolean"
                  end
                | _ => mfail "Race while reading CmpXchg location"
                end
            | _ => mfail "CmpXchg with non-location argument"
            end

      (* Won't interpret anything involving prophecy variables. *)
      | NewProph => mfail "NotImpl: prophecy variable." (* ignore *)
      | Resolve ex e1 e2 => mfail "NotImpl: resolve."   (* ignore *)
      end
    end.

  (* For computations where the first component is an interpret call,
  destructs on runStateT of that interpret call. If it Fails,
  immediately find a contradiction with runStateT_bind. If it Works,
  apply the inductive hypothesis from interpret_ok, passed in as IHn. *)
  Ltac run_next_interpret IHn :=
    match goal with
    | [H : runStateT (mbind (fun x => @?F x) (interpret ?n ?e)) ?σ = _ |- _] =>
      let interp_e := fresh "interp_e" in
      let IHe := fresh "IHe" in
      let e_to_v := fresh "nsteps_interp" in
      let v0 := fresh "v" in
      let m := fresh "m" in
      let l := fresh "l" in
      let v := fresh "v" in
      let s := fresh "s" in
      destruct (runStateT (interpret n e) σ) as [v0|] eqn:interp_e; [|runStateT_bind];
      destruct v0 as (v & s);
      pose (IHn e σ v s interp_e) as IHe;
      destruct IHe as (m & l & e_to_v);
      runStateT_bind
    | _ => fail
    end.

  (* Given ctx_expr, a fill of some context, looks for hypotheses like
  [e ~~> v] and a goal like [ctx_expr e ~~> ctx_expr v]. Uses nsteps_ctx
  lemma to dispatch the goal. *)
  Ltac ctx_step ctx_expr :=
    match goal with
    | [ nsteps_interp : nsteps _ ([?e], ?s) _ (_, _) |- _ ] =>
      let r := eval simpl in (ctx_expr e) in
          match goal with
          | [ |- nsteps _ ([r], s) _ _ ] =>
            let H := fresh "nsteps_interp_ctx" in
            pose proof (@nsteps_ctx _ ctx_expr _ _ _ _ _ _ _ nsteps_interp) as H;
            simpl in H;
            exact H
          | _ => fail
          end
    | _ => fail
    end.

  (* For any expression e that we can successfully interpret to a
  value v, there exists some number m of steps in the heap transition
  function that steps e to v. *)
  Theorem interpret_ok : forall (n: nat) (e: expr) (σ: state) (v: val) (σ': state),
      (((runStateT (interpret n e) σ) = Works _ (v, σ')) ->
       exists m l, @language.nsteps heap_lang m ([e], σ) l ([Val v], σ')).
  Proof.
    intros n. induction n.
    { by intros []. }

    intros e σ v σ' interp. destruct e; simpl; inversion interp; simpl.
    
    (* Val *)
    { eexists. eexists. apply language.nsteps_refl. }
    (* Var *)
    
    (* Rec *)
    { do 2 eexists.
      single_step.
    }
    
    (* App *)
    { 
      run_next_interpret IHn.
      run_next_interpret IHn.
      destruct v2; simpl in H0; try by inversion H0.
      pose proof (IHn _ _ _ _ H0) as IHapp.
      destruct IHapp as (k & IHapp').
      destruct IHapp' as (l'' & app_to_v).
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [App e1 e2] -> [App e1 v1] *)
        ctx_step (fill [(AppRCtx e1)]).
      }
      eapply nsteps_transitive.
      { (* [App e1 v1] -> [App (rec f x := e) v1] *)
        ctx_step (fill [(AppLCtx v1)]).
      }
      eapply nsteps_transitive.
      {
        single_step.
      }
      exact app_to_v.
    }

    (* UnOp *)
    { run_next_interpret IHn.
      inversion H0.
      destruct (un_op_eval op v1) eqn:uo_eval; inversion H1; subst; clear H1.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [UnOp op e] -> [UnOp op v1] *)
        ctx_step (fill [(UnOpCtx op)]).
      }
      {
        (* [UnOp op v1] -> [v] *)
        single_step.
      }
    }

    (* BinOp *)
    {
      run_next_interpret IHn.
      run_next_interpret IHn.
      inversion H0.
      destruct (bin_op_eval op v2 v1) eqn:bo_eval; inversion H1.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [BinOp op e1 e2] -> [BinOp op v2 e2] *)
        ctx_step (fill [(BinOpLCtx op e2)]).
      }
      eapply nsteps_transitive.
      { (* [BinOp op v2 e2] -> [BinOp op v2 v1] *)
        ctx_step (fill [(BinOpRCtx op v2)]).
      }
      { (* [BinOp op v2 v1] -> [v] *)
        subst.
        single_step.
      }
    }

    (* If *)
    { run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l0; simpl in H0; try by inversion H0.
      destruct b.
      { (* v1 = true *)
        pose (IHn _ _ _ _ H0) as IH2.
        destruct IH2 as (m' & IH2').
        destruct IH2' as (l' & e2_to_v).
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [if e1 e2 e3] -> [if #true e2 e3] *)
          ctx_step (fill [(IfCtx e2 e3)]).
        }
        eapply nsteps_transitive.
        { (* [if #true e2 e3] -> [e2] *)
          single_step.
        }
        (* [e2] -> [v] *)
        exact e2_to_v.
      }

      { (* v1 = false *)
        pose (IHn _ _ _ _ H0) as IH3.
        destruct IH3 as (m' & IH3').
        destruct IH3' as (l' & e3_to_v).
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [if e1 e2 e3] -> [if #false e2 e3] *)
          ctx_step (fill [(IfCtx e2 e3)]).
        }
        eapply nsteps_transitive.
        { (* [if #false e2 e3] -> [e3] *)
          single_step.
        }
        (* [e3] -> [v] *)
        exact e3_to_v.
      }
    }

    (* Pair *)
    { 
      run_next_interpret IHn.
      run_next_interpret IHn.
      inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [Pair e1 e2] -> [Pair v1 e2] *)
        ctx_step (fill [(PairLCtx e2)]).
      }
      eapply nsteps_transitive.
      { (* [Pair v1 e2] -> [Pair v1 v2] *)
        ctx_step (fill [(PairRCtx v1)]).
      }
      subst.
      single_step.
    }

    (* Fst *)
    { run_next_interpret IHn.
      destruct v1; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [Fst e] -> [Fst v0] *)
        ctx_step (fill [FstCtx]).
      }
      subst.
      single_step.
    }

    (* Snd *)
    { run_next_interpret IHn.
      destruct v1; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [Snd e] -> [Snd v0] *)
        ctx_step (fill [SndCtx]).
      }
      subst.
      single_step.
    }
    
    (* InjL *)
    { run_next_interpret IHn.
      inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [InjL e] -> [InjL v1] *)
        ctx_step (fill [InjLCtx]).
      }
      {
        (* [InjL v1] -> [v] *)
        subst.
        single_step.
      }
    }

    (* InjR *)
    { run_next_interpret IHn.
      inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [InjR e] -> [InjR v1] *)
        ctx_step (fill [InjRCtx]).
      }
      {
        (* [InjR v1] -> [v] *)
        subst.
        single_step.
      }
    }

    (* Case *)
    { run_next_interpret IHn.
      destruct v1 eqn:v1_type; simpl in H0; try by inversion H0.
      { (* InjL *)
        pose proof (IHn _ _ _ _ H0) as IHe2.
        destruct IHe2 as (m' & IHe2').
        destruct IHe2' as (l' & e2_to_v).
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [Case e1 e2 e3] -> [Case (InjLV v0) e2 e3] *)
          ctx_step (fill [(CaseCtx e2 e3)]).
        }
        eapply nsteps_transitive.
        {
          single_step.
        }
        exact e2_to_v.
      }
      { (* InjR *)
        pose proof (IHn _ _ _ _ H0) as IHe3.
        destruct IHe3 as (m' & IHe3').
        destruct IHe3' as (l' & e3_to_v).
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [Case e1 e2 e3] -> [Case (InjRV v0) e2 e3] *)
          ctx_step (fill [(CaseCtx e2 e3)]).
        }
        eapply nsteps_transitive.
        {
          single_step.
        }
        exact e3_to_v.
      }
    }

    (* Primitive0 *)
    {
      (* TODO: Remove dependent destruction using
       https://jamesrwilcox.com/dep-destruct.html technique *)
      dependent destruction op.
      inversion H0.
    }

    (* Primitive1 *)
    {
      dependent destruction op.
      { (* AllocStruct *)
        run_next_interpret IHn.
        simpl in H0.
        inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [AllocStruct e] -> [AllocStruct v0] *)
          ctx_step (fill [(Primitive1Ctx AllocStructOp)]).
        }
        single_step.
        eapply relation.bind_suchThat.
        (* Must prove the location find_alloc_location found is adequate *)
        { intros i ? ?.
          eapply find_alloc_location_ok; eauto. }
        monad_simpl.
      }

      { (* PrepareWrite *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l0; simpl in H0; try by inversion H0.
        destruct (heap s !! l0) as [heap_na_val|] eqn:hv; simpl in H0; [|by inversion H0].
        destruct heap_na_val as [|heap_val n0]; simpl in H0; try by inversion H0.
        destruct n0; simpl in H0; inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [PrepareWrite e] -> [PrepareWrite #l0] *)
          ctx_step (fill [(Primitive1Ctx PrepareWriteOp)]).
        }
        rewrite <- H2.
        single_step.
      }

      { (* StartRead *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l0; simpl in H0; try by inversion H0.
        destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
        destruct n0; simpl in H0; try by inversion H0.
        inversion H0; subst; clear H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive1Ctx StartReadOp)]).
        }
        single_step.
      }

      { (* FinishRead *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l0; simpl in H0; try by inversion H0.
        destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
        destruct n0; simpl in H0; try by inversion H0.
        destruct n0; simpl in H0; try by inversion H0.
        inversion H0; subst; clear H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive1Ctx FinishReadOp)]).
        }
        single_step.
      }

      { (* Load *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l0; simpl in H0; try by inversion H0.
        destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
        destruct n0; simpl in H0; try by inversion H0.
        destruct n0; simpl in H0; try by inversion H0.
        inversion H0; subst; clear H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive1Ctx LoadOp)]).
        }
        single_step.
      }

      { (* Input *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive1Ctx InputOp)]).
        }
        single_step.
      }

      { (* Output *)
        run_next_interpret IHn.
        destruct v1; simpl in H0; inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive1Ctx OutputOp)]).
        }
        single_step.
      }
    }

    (* Primitive2 *)
    { dependent destruction op.
      { (* AllocN *)
        run_next_interpret IHn.
        run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l1; simpl in H0; inversion H0.
        destruct (int.val n0 <=? 0) eqn:n0_int; simpl in H0; inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive2LCtx AllocNOp e2)]).
        }
        eapply nsteps_transitive.
        {
          ctx_step (fill [(Primitive2RCtx AllocNOp #n0)]).
        }
        single_step.
        rewrite -> ifThenElse_if; [|(rewrite -> Z.leb_nle in n0_int; lia)].
        simpl.
        monad_simpl.
        pose proof (find_alloc_location_fresh s0 (int.val n0)) as loc_fresh.
        eapply relation.bind_suchThat.
        {
          apply loc_fresh.
        }
        monad_simpl.
      }

      { (* FinishStore *)
        do 2 run_next_interpret IHn.
        destruct v1; simpl in H0; try by inversion H0.
        destruct l1; simpl in H0; try by inversion H0.
        destruct (heap s0 !! l1) eqn:heap_at_l1; simpl in H0; try by inversion H0.
        destruct n0 eqn:n0_is_writing; simpl in H0; inversion H0.
        do 2 eexists.
        eapply nsteps_transitive.
        { (* [FinishStore e1 e2] -> [FinishStore #l1 e2] *)
          ctx_step (fill [(Primitive2LCtx FinishStoreOp e2)]).
        }
        eapply nsteps_transitive.
        { (* [FinishStore #l0 e2] -> [FinishStore #l1 v2] *)
          ctx_step (fill [(Primitive2RCtx FinishStoreOp #l1)]).
        }
        single_step.
      }
    }

    (* CmpXchg *)
    {
      do 3 run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l2; simpl in H0; try by inversion H0.
      destruct (heap s1 !! l2) as [x|] eqn:heap_at_l2; simpl in H0; try by inversion H0.
      destruct x as [|vl] eqn:x_is; simpl in H0; try by inversion H0.
      destruct n0 eqn:n0_is_0; simpl in H0; try by inversion H0.
      destruct (bin_op_eval EqOp vl v2) as [some_b|] eqn:boe; simpl in H0; try by inversion H0.
      destruct some_b; simpl in H0; try by inversion H0.
      destruct l3; simpl in H0; try by inversion H0.
      destruct b; simpl in H0; inversion H0.
      { (* CmpXchg succeeds (true case) *)
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgLCtx e2 e3])).
        }
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgMCtx #l2 e3])).
        }
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgRCtx #l2 v2])).
        }
        single_step.
        unfold bin_op_eval in boe; simpl in boe.

        destruct (decide (vals_compare_safe vl v2)) eqn:vcs; inversion boe.
        monad_simpl.
        case_bool_decide; inversion H3.
        repeat (monad_simpl; simpl).
      }
      { (* CmpXchg fails (false case) *)
        do 2 eexists.
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgLCtx e2 e3])).
        }
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgMCtx #l2 e3])).
        }
        eapply nsteps_transitive.
        {
          ctx_step (fill ([CmpXchgRCtx #l2 v2])).
        }
        single_step.
        unfold bin_op_eval in boe; simpl in boe.
        destruct (decide (vals_compare_safe vl v2)) eqn:vcs; inversion boe.
        monad_simpl.
        case_bool_decide; inversion H3.
        repeat (monad_simpl; simpl).
        constructor.
        rewrite H2.
        reflexivity.
      }
    }

    (* ExternalOp *)
    { run_next_interpret IHn.
      destruct (runStateT (ext_interpret_step op v1) s) as [e_result|] eqn:ext_interp_v1; [|runStateT_bind].
      destruct e_result as (e' & s').
      pose proof (ext_interpret_ok _ _ _ _ _ ext_interp_v1) as ei_ok.
      destruct ei_ok as (m' & (l' & nstep_ext_interp)).
      runStateT_bind.
      pose proof (IHn _ _ _ _ H0).
      destruct H as (m'' & (l'' & rest_nstep)).
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill ([ExternalOpCtx op])).
      }
      eapply nsteps_transitive.
      {
        exact nstep_ext_interp.
      }
      exact rest_nstep.
    }
  Qed.

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

(* More instances of mbind and mret, this time outside of the
go_lang_int section. *)
Instance statet_disk_option_bind : MBind (StateT state option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_disk_option_ret : MRet (StateT state option) :=
  StateT_ret option option_ret.
Instance statet_disk_error_bind : MBind (StateT state Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_disk_error_ret : MRet (StateT state Error) :=
  StateT_ret Error Error_ret.

Definition free_val {A} (x: nonAtomic A) : option A :=
  match x with
  | Reading y 0 => Some y
  | _ => None
  end.

Definition byte_val (v: val) : option byte :=
  match v with
  | LitV (LitByte b) => Some b
  | _ => None
  end.

Definition read_block_from_heap (σ: state) (l: loc) : option Block :=
  navs <- state_readn_vec σ l block_bytes;
    (* list (nonAtomic val) -> list (option val) -> option (list val) -> list val *)
    vs <- commute_option_vec _ (vmap free_val navs);
    commute_option_vec _ (vmap byte_val vs).

(* If state_readn_vec succeeds, for each i in the range requested, the
heap at l + i should be some nonatomic value and that nonatomic value
should be at the return value in index i. *)
Lemma state_readn_vec_ok : forall n σ l v,
    (state_readn_vec σ l n = Some v) ->
    (forall (i:fin n),
        match σ.(heap) !! (l +ₗ i) with
        | Some nav => nav = v !!! i
        | _ => False
        end).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction v.
    simpl in H.
    destruct (heap σ !! l) as [nav|] eqn:heap_at_l; try by inversion H.
    simpl in H.
    destruct (state_readn_vec σ (l +ₗ 1) n) as [vtl|] eqn:srv_ind; try by inversion H.
    simpl in H.
    unfold mret in H.
    inversion H.
    inv_fin i.
    {
      simpl.
      assert (l +ₗ 0%nat = l) as plus_zero.
      {
        unfold loc_add.
        rewrite Zplus_0_r.
        destruct l.
        simpl.
        reflexivity.
      }
      rewrite plus_zero heap_at_l; by exact H1.
    }
    {
      intros.
      assert (l +ₗ FS i = (l +ₗ 1) +ₗ i) as l_plus_one.
      {
        unfold loc_add.
        destruct l.
        simpl.
        replace (loc_car + S i) with (loc_car + 1 + i); [reflexivity|].
        lia.
      }
      rewrite l_plus_one.
      pose proof (IHn σ (l +ₗ 1) vtl srv_ind i).
      destruct (heap σ !! (l +ₗ 1 +ₗ i)) as [navi|] eqn:heap_at_l1i; [|contradiction].
      simpl.
      rewrite H0.
      apply Eqdep_dec.inj_pair2_eq_dec in H2.
      {
        rewrite H2; reflexivity.
      }
      exact Nat.eq_dec.
    }
  }
Qed.

Lemma commute_option_vec_ok {A} : forall n (ov: vec (option A) n) (v: vec A n),
    (commute_option_vec A ov = Some v) ->
    (forall (i:fin n), ov !!! i = Some (v !!! i)).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction ov.
    simpl in H.
    destruct h as [a|]; [simpl in H|by inversion H].
    destruct (commute_option_vec A ov) as [v'|] eqn:cov_tail; [unfold mret, option_ret in H; simpl in H|by inversion H].
    pose proof (IHn _ _ cov_tail) as IH_tail.
    inversion H.
    inv_fin i.
    {
      simpl.
      reflexivity.
    }
    {
      intros i.
      simpl.
      exact (IH_tail i).
    }
  }
Qed.

Lemma read_block_from_heap_ok (σ: state) (l: loc) (b: Block) :
  (read_block_from_heap σ l = Some b) ->
  (forall (i:Z), 0 <= i -> i < 4096 ->
            match σ.(heap) !! (l +ₗ i) with
            | Some (Reading v _) => Block_to_vals b !! Z.to_nat i = Some v
            | _ => False
            end).
Proof.
  intros.
  unfold read_block_from_heap in H.
  unfold mbind in H.
  unfold option_bind in H.
  destruct (state_readn_vec σ l block_bytes) as [navs|] eqn:vec_at_l; try by inversion H.
  unfold block_bytes in *.
  destruct (commute_option_vec val (vmap free_val navs)) as [v|] eqn:all_free; try by inversion H.

  (* Only way to convert (Z.to_nat i) to a (fin 4096) is to have
  hypothesis that says exactly this. *)
  assert ((Z.to_nat i < 4096)%nat) as fin_i by lia. 
  
  pose proof (commute_option_vec_ok _ _ _ H (fin_of_nat fin_i)) as cov_ok_v.
  pose proof (commute_option_vec_ok _ _ _ all_free (fin_of_nat fin_i)) as cov_ok_navs.
  pose proof (state_readn_vec_ok _ _ _ _ vec_at_l (fin_of_nat fin_i)) as srv_ok_l.

  destruct (heap σ !! (l +ₗ fin_of_nat fin_i)) as [nav|] eqn:heap_at_fin_i; [|rewrite heap_at_fin_i in srv_ok_l; contradiction].
  assert ((l +ₗ i) = (l +ₗ fin_of_nat fin_i)).
  {
    unfold loc_add.
    replace (loc_car l + (fin_of_nat fin_i)) with (loc_car l + i); [reflexivity|].
    pose proof (fin_to_of_nat _ _ fin_i).
    rewrite H2.
    lia.
  }
  rewrite -> H2.
  rewrite heap_at_fin_i in srv_ok_l.
  rewrite heap_at_fin_i.
  rewrite srv_ok_l.
  rewrite -> (vlookup_map free_val navs (fin_of_nat fin_i)) in cov_ok_navs.
  unfold free_val in cov_ok_navs.
  destruct (navs !!! fin_of_nat fin_i) as [|nav'] eqn:navs_at_fin_i; inversion cov_ok_navs.
  destruct n eqn:n_is_free; inversion cov_ok_navs.
  clear cov_ok_navs navs_at_fin_i heap_at_fin_i H4 H5 H2 srv_ok_l nav'
        n n_is_free nav all_free H navs vec_at_l.
  unfold block_bytes in cov_ok_v. (* block_bytes doesn't show, but is here and needs to be unfolded *)
  rewrite -> (vlookup_map byte_val v (fin_of_nat fin_i)) in cov_ok_v.
  destruct (v !!! fin_of_nat fin_i) eqn:v_at_fin_i; try by inversion cov_ok_v.
  unfold Block_to_vals.
  pose proof (list_lookup_fmap b2val b (Z.to_nat i)) as llf.
  rewrite llf.
  simpl in cov_ok_v.
  destruct l0; try by inversion cov_ok_v.
  inversion cov_ok_v as [b_at_fin_i].
  rewrite <- b_at_fin_i.
  pose proof (vlookup_lookup' b (Z.to_nat i) n) as vll.
  assert ((b : list u8) !! Z.to_nat i = Some n).
  {
    apply vll.
    exists fin_i.
    rewrite b_at_fin_i; reflexivity.
  }
  rewrite H.
  unfold b2val.
  simpl; reflexivity.
Qed.

Fixpoint disk_interpret_step (op: DiskOp) (v: val) : StateT state Error expr :=
  match (op, v) with
  | (ReadOp, (LitV (LitInt a))) =>
    σ <- mget;
      b <- mlift (σ.(world) !! int.val a) ("ReadOp: No block at address " ++ (pretty a));
      let l := find_alloc_location σ 4096 in
      _ <- mput (state_insert_list l (Block_to_vals b) σ);
        mret (Val $ LitV (LitLoc l))
  | (WriteOp, (PairV (LitV (LitInt a)) (LitV (LitLoc l)))) =>
    σ <- mget;
      _ <- mlift (σ.(world) !! int.val a) ("WriteOp: No block at write address " ++ (pretty a));
      b <- mlift (read_block_from_heap σ l) "WriteOp: Read from heap failed";
      _ <- mput (set world <[ int.val a := b ]> σ);
      mret (Val $ LitV (LitUnit))
  | (SizeOp, LitV LitUnit) =>
    σ <- mget;
      mret (Val $ LitV $ LitInt (U64 (disk_size σ.(world))))
  | _ => mfail "DiskOp: Not a valid disk op and arg"
  end.

Lemma disk_interpret_ok : forall (eop : DiskOp) (arg : val) (result : expr) (σ σ': state),
    (runStateT (disk_interpret_step eop arg) σ = Works _ (result, σ')) ->
    exists m l, @language.nsteps heap_lang m ([ExternalOp eop (Val arg)], σ) l ([result], σ').
Proof.
  intros eop arg result σ σ' H.
  destruct eop; inversion H.
  { (* ReadOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (find_alloc_location_fresh σ 4096) as fresh.
    {
      eapply relation.bind_suchThat.
      {
        simpl.
        exact fresh.
      }
      monad_simpl.
    }
  }
  { (* WriteOp *)
    destruct arg; try by inversion H1.
    destruct arg1; try by inversion H1.
    destruct l; try by inversion H1.
    destruct arg2; try by inversion H1.
    destruct l; try by inversion H1. (* takes a very long time (why?) *)
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1. (* also takes a long time *)
    destruct (read_block_from_heap σ l) eqn:block_at_l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (read_block_from_heap_ok _ _ _ block_at_l) as rbfsok.
    eapply relation.bind_suchThat; [exact rbfsok|].
    monad_simpl.
  }
  { (* SizeOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
  }
Qed.

Instance disk_interpretable : @ext_interpretable disk_op disk_model disk_semantics :=
  { ext_interpret_step := disk_interpret_step;
    ext_interpret_ok := disk_interpret_ok }.

Compute (runStateT (interpret 10 (AllocN #1 (zero_val uint32T))) startstate).
Compute (runStateT (interpret 10 (useSlice2 #0)) startstate).
Compute (runStateT (interpret 10 (returnTwoWrapper #3)) startstate).
Compute (runStateT (interpret 10 (testRec #0)) startstate).

Definition runs_to (p: expr) (v: val) :=
  (fst <$> runStateT (interpret 100 p) startstate) = Works _ v.
Notation "p ~~> v" := (eq_refl : runs_to p v) (at level 70).

Example run_testRec := testRec #0 ~~> #6.

Compute (runStateT (interpret 10 ConstWithArith) startstate).
Compute (runStateT (interpret 10 (literalCast #0)) startstate).
Compute (fst <$> (runStateT (interpret 15 (useSliceIndexing #0)) startstate)).

(*
Example run_encdec1 := testUInt64EncDec #1 ~~> #1.
Example run_encdec2 := testUInt64EncDec #256 ~~> #256.
Example run_encdec3 := testUInt64EncDec #65536 ~~> #65536.
Example run_encdec4 := testUInt64EncDec #3214405 ~~> #3214405.
*)

Compute (runStateT (interpret 10 (testIfStatement #0)) startstate).
Compute (runStateT (interpret 10 (testMatch (InjL #2))) startstate).
Compute (runStateT (interpret 10 (testMatch (InjR #2))) startstate).
Compute (runStateT (interpret 16 (useMap #0)) startstate).
Compute (runStateT (interpret 10 (ReassignVars #0)) startstate).

Definition test_case (p: expr) :=
  match (fst <$> runStateT (interpret 100 p) startstate) with
  | Works _ (LitV (LitBool true)) => true
  | _ => false
  end.

Compute (test_case (EncDec64 #333)).
Compute (test_case (EncDec32 #333)).

Definition tc1 := (test_case (EncDec64 #333)).

(* Extraction testing:

Require Coq.extraction.Extraction.
Extraction Language Haskell.
Extract Inductive bool => "GHC.Base.Bool" [ "GHC.Base.True" "GHC.Base.False" ].

Extraction "tc1.hs" tc1.

*)
