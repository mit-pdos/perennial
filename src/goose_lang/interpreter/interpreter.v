From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings gmap pretty.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers.
From Perennial.goose_lang Require Export locations lang notation.
From Perennial.goose_lang Require Import interpret_types.
From Perennial.goose_lang Require Import pretty_types.

Require Import Program.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(* The step relation is transitive. Doing n steps and then m steps is
the same as doing (n + m) steps. Useful in interpret_ok for splitting
goals like [If e0 e1 e2] ~~> [v] into [If e0 e1 e2] ~~> [If #true e1
e2] and [If #true e1 e2] ~~> [v]. *)
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
  rewrite /= /head_step /=; repeat (Transitions.monad_simpl; simpl).

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

Section interpreter.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}.
  Canonical Structure goose_ectxi_lang := (EctxiLanguage (goose_lang.goose_lang_mixin ffi_semantics)).
  Canonical Structure goose_ectx_lang := (EctxLanguageOfEctxi goose_ectxi_lang).
  Canonical Structure goose_lang := (LanguageOfEctx goose_ectx_lang).

  Definition btval := list string.
  Definition btstate := prod state btval.

  (* The analog of ext_semantics for an interpretable external
     operation. An ext_op transition isn't strong enough to let us interpret
     ExternalOps, so we need an executable interpretation of them. *)
  Class ext_interpretable :=
    {
      ext_interpret_step : external -> val -> StateT btstate Error expr;
      ext_interpret_ok : forall (eop : external) (arg : val) (result : expr) (σ σ': state) (ws ws':btval),
          (runStateT (ext_interpret_step eop arg) (σ,ws) = Works _ (result, (σ',ws'))) ->
          exists m l, @language.nsteps goose_lang m ([ExternalOp eop (Val arg)], σ) l ([result], σ');
    }.

  Context {ext_interpretable : ext_interpretable}.

  (* Necessary because mbind and mret implicitly need instances of
  MBind and MRet, respectively. *)
  Instance statet_error_bind : MBind (StateT btstate Error) :=
    StateT_bind Error Error_fmap Error_join Error_bind.
  Instance statet_error_ret : MRet (StateT btstate Error) :=
    StateT_ret Error Error_ret.

  Fixpoint print_val (v: val) : string :=
    match v with
    | LitV l => "LitV(" +:+ pretty_lit l +:+ ")"
    | RecV f x e => "RecV"
    | PairV v1 v2 => "PairV(" +:+ print_val v1 +:+ ", " +:+ print_val v2 +:+ ")"
    | InjLV v => "InjL(" +:+ print_val v +:+ ")"
    | InjRV v => "InjR(" +:+ print_val v +:+ ")"
    end.
  Instance pretty_val : Pretty val := print_val.

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

  Fixpoint print_btval (v: btval) : string :=
    match v with
    | nil => ""
    | cons h nil => h
    | cons h tl => h ++ ", " ++ (print_btval tl)
    end.
  Instance pretty_btval : Pretty btval := print_btval.

  Definition mfail_bt (msg: string) : StateT btstate Error val :=
    s <- mget;
      mfail ("[" ++ (pretty (snd s)) ++ "]:
 " ++ msg).

  Definition mlift_bt {X} (ma: option X) (msg: string) : StateT btstate Error X :=
    s <- mget;
      mlift ma ("[" ++ (pretty (snd s)) ++ "]:
 " ++ msg).
  
  (* Interpreter *)
  Fixpoint interpret (fuel: nat) (expr: expr) : StateT btstate Error val :=
    match fuel with
    | O => mfail_bt "Fuel depleted"
    | S n =>
      match expr with
      | Val v => mret v
      | Var y => mfail_bt ("Unbound variable: " ++ y)
      | Rec f y e => mret (RecV f y e)

      | App e1 e2 => 
        v2 <- interpret n e2;
          v1 <- interpret n e1;
          match v1 with
          | RecV (BNamed fname) y ex =>
            _ <- mupdate (fun bts => (fst bts, fname :: snd bts));
            let e3 := subst' y v2 (subst' (BNamed fname) v1 ex) in
            interpret n e3
          | RecV f y ex =>
            let e3 := subst' y v2 (subst' f v1 ex) in
            interpret n e3
          | _ => mfail_bt ("App applied to a non-function of type: " ++ (pretty v1))
          end
            
      | UnOp op e =>
        v <- interpret n e;
          (* mlift_bt because un_op_eval returns an optional *)
          mlift_bt (un_op_eval op v)
                ("UnOp eval on invalid type: " ++ (pretty op) ++ "(" ++ (pretty v) ++ ")")
                
      | BinOp op e1 e2 =>
        v1 <- interpret n e1;
          v2 <- interpret n e2;
          (* mlift_bt because bin_op_eval returns an optional *)
          mlift_bt (bin_op_eval op v1 v2)
                ("BinOp eval on invalid type: " ++ (pretty op) ++ "(" ++ (pretty v1) ++ ", " ++ (pretty v2) ++ ")")
                
      | If e0 e1 e2 =>
        c <- interpret n e0;
          match c with
          | LitV (LitBool true) => interpret n e1
          | LitV (LitBool false) => interpret n e2
          | _ => mfail_bt ("If applied to non-Bool of type " ++ (pretty c))
          end

      | Pair e1 e2 =>
        a <- interpret n e1;
          b <- interpret n e2;
          mret (PairV a b)
               
      | Fst e =>
        v <- interpret n e;
          match v with
          | PairV v1 v2 => mret v1
          | _ => mfail_bt ("Fst applied to non-PairV of type " ++ (pretty v))
          end

      | Snd e =>
        v <- interpret n e;
          match v with
          | PairV v1 v2 => mret v2
          | _ => mfail_bt ("Snd applied to non-PairV of type:" ++ (pretty v))
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
          | _ => mfail_bt ("Tried to Case on a non-Inj term of type " ++ (pretty v))
          end

      | Fork e => mfail_bt "Fork operation not supported"

      | Primitive0 p =>
        match p in (prim_op args0) return StateT btstate Error val with
        | PanicOp s => mfail_bt ("Interpret panic: " ++ s)
        | ArbitraryIntOp => mret (LitV (LitInt (U64 1)))
        end

      | Primitive1 p e =>
        match p in (prim_op args1) return StateT btstate Error val with
        | PrepareWriteOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              sbt <- mget;
                let s := fst sbt in
                nav <- mlift_bt (s.(heap) !! l) ("Load failed for location " ++ (pretty l));
                match nav with
                | (Reading 0, v) => _ <- mupdate (fun sbt => ((set heap <[l:=(Writing, v)]>) $ fst sbt, snd sbt));
                                  mret (LitV LitUnit)
                | _ => mfail_bt ("Race occurred during write at location " ++ (pretty l))
                end
            | _ => mfail_bt ("Attempted Load with a non-location argument of type " ++ (pretty addrv))
            end
        | LoadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitInt l) =>
              mfail_bt ("Attempted load at Int " ++ (pretty l) ++ " instead of a Loc")
            | LitV (LitLoc l) =>
              (* Since Load of an address with nothing doesn't step,
                 we can lift from the option monad into the StateT option
                 monad here (we mfail_bt "NotImpl" if v is None). *)
              sbt <- mget;
                let s := fst sbt in
                nav <- mlift_bt (s.(heap) !! l) ("Load failed at location " ++ (pretty l));
                match nav with
                | (Reading _, v) => mret v
                | _ => mfail_bt ("Race detected while reading at location " ++ (pretty l))
                end
            | _ => mfail_bt ("Attempted Load with non-location argument of type " ++ (pretty addrv))
            end
        | InputOp =>
          v <- interpret n e;
            match v with
            | LitV (LitInt selv) =>
              sbt <- mget;
                let σ := fst sbt in
                let x := σ.(oracle) σ.(trace) selv in
                _ <- mupdate (fun sbt => ((set trace (fun tr => [In_ev selv (LitInt x)] ++ tr)) $ fst sbt, snd sbt));
                  mret (LitV (LitInt x))
            | _ => mfail_bt ("Attempted InputOp with non-literal selector of type " ++ (pretty v))
            end
        | OutputOp =>
          v <- interpret n e;
            match v with
            | LitV v =>
              _ <- mupdate (fun sbt => ((set trace (fun tr => [Out_ev v] ++ tr)) $ fst sbt, snd sbt));
                mret (LitV LitUnit)
            | _ => mfail_bt ("Attempted Output with non-literal value of type " ++ (pretty v))
            end
        | StartReadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              sbt <- mget;
                let s := fst sbt in
                nav <- mlift_bt (s.(heap) !! l) ("StartReadOp failed at location " ++ (pretty l));
                match nav with
                | (Reading n, v) => _ <- mupdate (fun sbt => ((set heap <[l:=(Reading (S n), v)]>) $ fst sbt, snd sbt));
                                  mret v
                | _ => mfail_bt ("Race detected during StartReadOp at location " ++ (pretty l))
                end
            | _ => mfail_bt ("StartReadOp called with non-location argument of type " ++ (pretty addrv))
            end
        | FinishReadOp =>
          addrv <- interpret n e;
            match addrv with
            | LitV (LitLoc l) =>
              sbt <- mget;
                let s := fst sbt in
                nav <- mlift_bt (s.(heap) !! l) ("FinishReadOp failed at location " ++ (pretty l));
                match nav with
                | (Reading (S n), v) => _ <- mupdate (fun sbt => ((set heap <[l:=(Reading n, v)]>) $ fst sbt, snd sbt));
                                      mret (LitV LitUnit)
                | (Reading 0, v) => mfail_bt ("FinishReadOp attempted with no reads occurring at location " ++ (pretty l))
                | _ => mfail_bt ("Attempted FinishReadOp while writing at location " ++ (pretty l))
                end
            | _ => mfail_bt ("Attempted FinishReadOp with non-location argument of type " ++ (pretty addrv))
            end
        end

      | Primitive2 p e1 e2 =>
          v1 <- interpret n e1;
          v2 <- interpret n e2;
          sbt <- mget;
          let s := fst sbt in
          t <- mlift_bt (Transitions.interpret [] (head_trans (Primitive2 p (Val v1) (Val v2))) s) "transition.interpret failed in Primitive2";
              match t return StateT btstate Error val with
              (* hints, new state, (obs list, next expr, threads) *)
              | (hints, s', (l, expr', ts)) =>
                match expr' return StateT btstate Error val with
                | Val v =>
                  match ts with
                    | [] => _ <- mput (s', snd sbt); mret v
                    | _ => mfail_bt "Thread spawned during Primitive2 op"
                  end
                | _ => mfail_bt "Failed to interpret Primitive2 op to val"
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
              sbt <- mget;
                let s := fst sbt in
                nav <- mlift_bt (s.(heap) !! l) ("CmpXchg load failed at location " ++ (pretty l));
                match nav with
                | (Reading n, vl) =>
                  b <- mlift_bt (if decide (vals_compare_safe vl v1) then
                                  Some $ LitV $ LitBool $ bool_decide (vl = v1)
                                else
                                  None)
                    ("CmpXchg BinOp tried on invalid type: " ++ (pretty EqOp) ++ "(" ++ (pretty vl) ++ ", " ++ (pretty v1) ++ ")");
                  match b with
                  | LitV (LitBool true) =>
                    match n with
                      | S _ => mfail_bt ("CmpXchg load failed at location " ++ (pretty l) ++ "because of a race with non-atomic read")
                      | O => _ <- mput ((set heap <[l:=Free v2]> s), snd sbt);
                           mret (PairV vl #true)
                    end
                  | LitV (LitBool false) => mret (PairV vl #false)
                  | _ => mfail_bt ("Expected bool but CmpXchg EqOp returned type: " ++ (pretty b))
                  end
                | _ => mfail_bt ("Race detected while reading CmpXchg location " ++ (pretty l))
                end
            | _ => mfail_bt ("CmpXchg attempted with non-location argument of type " ++ (pretty addrv))
            end

      (* Won't interpret anything involving prophecy variables. *)
      | NewProph => mfail_bt "NotImpl: prophecy variable." (* ignore *)
      | Resolve ex e1 e2 => mfail_bt "NotImpl: resolve."   (* ignore *)
      end
    end.

  (* For computations where the first component is an interpret call,
  destructs on runStateT of that interpret call. If it Fails,
  immediately find a contradiction with runStateT_bind. If it Works,
  apply the inductive hypothesis from interpret_ok, passed in as IHn. *)
  Ltac run_next_interpret IHn :=
    match goal with
    | [H : runStateT (mbind (fun x => @?F x) (interpret ?n ?e)) (?σ, ?ws) = _ |- _] =>
      let interp_e := fresh "interp_e" in
      let IHe := fresh "IHe" in
      let e_to_v := fresh "nsteps_interp" in
      let v0 := fresh "v" in
      let m := fresh "m" in
      let l := fresh "l" in
      let v := fresh "v" in
      let s := fresh "s" in
      let ws' := fresh "ws'" in
      destruct (runStateT (interpret n e) (σ, ws)) as [v0|] eqn:interp_e; [|runStateT_bind];
      destruct v0 as (v & (s & ws'));
      pose (IHn e σ v s ws ws' interp_e) as IHe;
      destruct IHe as (m & l & e_to_v);
      runStateT_bind
    | _ => fail
    end.

  (* Given ctx_expr, a fill of some context, looks for hypotheses like
  [e ~~> v] and a goal like [ctx_expr e ~~> ctx_expr v]. Uses nsteps_ctx
  lemma to dispatch the goal. *)
  Ltac ctx_step ctx_expr :=
    repeat match goal with
    | [ nsteps_interp : language.nsteps _ ([?e], ?s) _ (_, _) |- _ ] =>
      let r := eval simpl in (ctx_expr e) in
          match goal with
          | [ |- language.nsteps _ ([r], s) _ _ ] =>
            let H := fresh "nsteps_interp_ctx" in
            pose proof (@nsteps_ctx _ ctx_expr _ _ _ _ _ _ _ nsteps_interp) as H;
            simpl in H;
            exact H
          | _ => fail
          end
    | _ => fail
    end.

  Ltac inv_works :=
    try match goal with
    | [H : Works _ _ = Works _ _ |- _] => inversion H; clear H; subst
    | [H : mret _ = Works _ _ |- _] => inversion H; clear H; subst
    | _ => fail
    end.

Ltac runStateT_inv_once :=
  match goal with
  | [H : runStateT (match ?v with _ => _ end) _ = _ |- _] =>
    destruct v eqn:?; simpl in H; try by inversion H
  | [H : runStateT _ _ = _ |- _] =>
    simpl in H; try by inversion H
  | _ => fail
  end; inv_works.

Ltac match_inv_once :=
  match goal with
  | [H : match (match ?v with _ => _ end) with | (StateFn _ _ _ _) => _ end = Works _ _ |- _] =>
    destruct v eqn:?; simpl in H; try by inversion H
  | [H : match (if ?b then _ else _) with | (StateFn _ _ _ _) => _ end = Works _ _ |- _] =>
    destruct b eqn:?; simpl in H; try by inversion H
  | [H : match ?v with | (Works _ _) => _ | (Fail _ _) => _ end = Works _ _ |- _] =>
    destruct v eqn:?; simpl in H; try by inversion H
  | [H : match ?v with | (Some _) => _ | None => _ end = Works _ _ |- _] =>
    destruct v eqn:?; simpl in H; try by inversion H
  | _ => fail
  end; inv_works.

Ltac mjoin_inv_once :=
  match goal with
    | [H : mjoin (_ <$> _ match ?v with _ => _ end) = _ |- _] =>
      destruct v eqn:?; simpl in H; try by inversion H
    | _ => fail
  end; inv_works.

Ltac runStateT_inv :=
  repeat (runStateT_inv_once || match_inv_once || mjoin_inv_once).

  (* For any expression e that we can successfully interpret to a
  value v, there exists some number m of steps in the heap transition
  function that steps e to v. *)
  Theorem interpret_ok : forall (n: nat) (e: expr) (σ: state) (v: val) (σ': state) (ws ws':btval),
      (((runStateT (interpret n e) (σ, ws)) = Works _ (v, (σ', ws'))) ->
       exists m l, @language.nsteps goose_lang m ([e], σ) l ([Val v], σ')).
  Proof using Type.
    intros n. induction n.
    { by intros []. }

    intros e σ v σ' ws ws' interp. destruct e; simpl; inversion interp; simpl.
    
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
      runStateT_inv.
      {
        pose proof (IHn _ _ _ _ _ _ H0) as IHapp.
        destruct IHapp as (k & l' & app_to_v).
        do 2 eexists.
        (* [App e1 e2] -> [App e1 v1] *)
        eapply nsteps_transitive; [ctx_step (fill [(AppRCtx e1)])|].
        (* [App e1 v1] -> [App (rec f x := e) v1] *)
        eapply nsteps_transitive; [ctx_step (fill [(AppLCtx v1)])|].
        eapply nsteps_transitive; [single_step | exact app_to_v].
      }
      { (* Named case, need to deal with modifying bt *)
        assert (runStateT (interpret n (subst' x v1 (subst s1 (rec: s1 x := e) e))) (s0, s1 :: ws'1) = Works (val * btstate) (v, (σ', ws'))) as H0 by (unfold runStateT; exact Heqe0).
        pose proof (IHn _ _ _ _ _ _ H0) as IHapp.
        destruct IHapp as (k & l' & app_to_v).
        do 2 eexists.
        (* [App e1 e2] -> [App e1 v1] *)
        eapply nsteps_transitive; [ctx_step (fill [(AppRCtx e1)])|].
        (* [App e1 v1] -> [App (rec f x := e) v1] *)
        eapply nsteps_transitive; [ctx_step (fill [(AppLCtx v1)])|].
        eapply nsteps_transitive; [single_step | exact app_to_v].
      }
    }

    (* UnOp *)
    { run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [UnOp op e] -> [UnOp op v1] *)
      eapply nsteps_transitive; [ctx_step (fill [(UnOpCtx op)])|].
      (* [UnOp op v1] -> [v] *)
      single_step.
    }

    (* BinOp *)
    {
      run_next_interpret IHn.
      run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [BinOp op e1 e2] -> [BinOp op v2 e2] *)
      eapply nsteps_transitive; [ctx_step (fill [(BinOpLCtx op e2)])|].
      (* [BinOp op v2 e2] -> [BinOp op v2 v1] *)
      eapply nsteps_transitive; [ctx_step (fill [(BinOpRCtx op v2)])|].
      (* [BinOp op v2 v1] -> [v] *)
      single_step.
    }

    (* If *)
    { run_next_interpret IHn.
      runStateT_inv;
      ( (* v1 = true or false *)
        pose proof (IHn _ _ _ _ _ _ H0) as IH';
        destruct IH' as (m' & l' & er_to_v);
        do 2 eexists;
        (* [If e1 e2 e3] -> [If #val e2 e3] *)
        eapply nsteps_transitive; [ctx_step (fill [(IfCtx e2 e3)])|];
        (* [If #val e2 e3] -> [er] and [er] -> [v] *)
        eapply nsteps_transitive; [single_step | exact er_to_v]
      ).
    }

    (* Pair *)
    { 
      run_next_interpret IHn.
      run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [Pair e1 e2] -> [Pair v1 e2] *)
      eapply nsteps_transitive; [ctx_step (fill [(PairLCtx e2)])|].
      (* [Pair v1 e2] -> [Pair v1 v2] *)
      eapply nsteps_transitive; [ctx_step (fill [(PairRCtx v1)])|].
      single_step.
    }

    (* Fst *)
    { run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [Fst e] -> [Fst v0] *)
      eapply nsteps_transitive; [ctx_step (fill [FstCtx])|].
      single_step.
    }

    (* Snd *)
    { run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [Snd e] -> [Snd v0] *)
      eapply nsteps_transitive; [ctx_step (fill [SndCtx])|].
      single_step.
    }
    
    (* InjL *)
    { run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [InjL e] -> [InjR v1] *)
      eapply nsteps_transitive; [ctx_step (fill [InjLCtx])|].
      (* [InjL v1] -> [v] *)
      subst.
      single_step.
    }

    (* InjR *)
    { run_next_interpret IHn.
      runStateT_inv.
      do 2 eexists.
      (* [InjR e] -> [InjR v1] *)
      eapply nsteps_transitive; [ctx_step (fill [InjRCtx])|].
      (* [InjR v1] -> [v] *)
      subst.
      single_step.
    }

    (* Case *)
    { run_next_interpret IHn.
      runStateT_inv.
      { (* InjL *)
        pose proof (IHn _ _ _ _ _ _ H0) as IHe2.
        destruct IHe2 as (m' & l' & e2_to_v).
        do 2 eexists.
        (* [Case e1 e2 e3] -> [Case (InjLV v0) e2 e3] *)
        eapply nsteps_transitive; [ctx_step (fill [(CaseCtx e2 e3)])|].
        eapply nsteps_transitive; [single_step | exact e2_to_v].
      }
      { (* InjR *)
        pose proof (IHn _ _ _ _ _ _ H0) as IHe3.
        destruct IHe3 as (m' & l' & e3_to_v).
        do 2 eexists.
        (* [Case e1 e2 e3] -> [Case (InjRV v0) e2 e3] *)
        eapply nsteps_transitive; [ctx_step (fill [(CaseCtx e2 e3)])|].
        eapply nsteps_transitive; [single_step | exact e3_to_v].
      }
    }

    (* Primitive0 *)
    {
      (* TODO: Remove dependent destruction using
       https://jamesrwilcox.com/dep-destruct.html technique *)
      dependent destruction op.
      - (* Panic *)
        inversion H0.
      - (* ArbitraryInt *)
        runStateT_inv.
        do 2 eexists.
        single_step.
        eapply Transitions.relation.bind_runs; [ | Transitions.monad_simpl ].
        constructor; auto.
    }

    (* Primitive1 *)
    {
      dependent destruction op.
      { (* PrepareWrite *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        (* [PrepareWrite e] -> [PrepareWrite #l0] *)
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx PrepareWriteOp)])|].
        single_step.
      }

      { (* StartRead *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx StartReadOp)])|].
        single_step.
      }

      { (* FinishRead *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx FinishReadOp)])|].
        single_step.
      }

      { (* Load *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx LoadOp)])|].
        single_step.
      }

      { (* Input *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx InputOp)])|].
        single_step.
      }

      { (* Output *)
        run_next_interpret IHn.
        runStateT_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive1Ctx OutputOp)])|].
        single_step.
      }
    }

    (* Primitive2 *)
    { do 2 run_next_interpret IHn.
      runStateT_inv.
      pose proof (Transitions.relation.interpret_sound _ _ _ Heqo).
      dependent destruction op.
      { runStateT_inv.
        destruct v2 eqn:?; simpl in H; try by inversion H.
        destruct l2 eqn:?; simpl in H; try by inversion H.
        subst.
        Transitions.monad_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive2LCtx AllocNOp e2)])|].
        eapply nsteps_transitive; [ctx_step (fill [(Primitive2RCtx AllocNOp #n0)])|].
        single_step.
        exact H.
      }
      { runStateT_inv.
        destruct v2 eqn:?; simpl in H; try by inversion H.
        destruct l2 eqn:?; simpl in H; try by inversion H.
        subst.
        Transitions.monad_inv.
        do 2 eexists.
        eapply nsteps_transitive; [ctx_step (fill [(Primitive2LCtx FinishStoreOp e2)])|].
        eapply nsteps_transitive; [ctx_step (fill [(Primitive2RCtx FinishStoreOp #l4)])|].
        single_step.
        exact H.
      }
    }

    (* CmpXchg *)
    {
      do 3 run_next_interpret IHn.
      runStateT_inv;
      ( (* CmpXchg succeeds OR fails *)
        do 2 eexists;
        eapply nsteps_transitive; [ctx_step (fill ([CmpXchgLCtx e2 e3]))|];
        eapply nsteps_transitive; [ctx_step (fill ([CmpXchgMCtx #l3 e3]))|];
        eapply nsteps_transitive; [ctx_step (fill ([CmpXchgRCtx #l3 v2]))|];
        single_step;

        destruct (decide (vals_compare_safe v0 v2)) eqn:vcs; inversion Heqo0;
        Transitions.monad_simpl;
        case_bool_decide; try by inversion H0;
        repeat (Transitions.monad_simpl; simpl)
        ).
    }

    (* ExternalOp *)
    { run_next_interpret IHn.
      destruct (runStateT (ext_interpret_step op v1) (s, ws'0)) as [e_result|] eqn:ext_interp_v1; [|runStateT_bind].
      destruct e_result as (e' & (s' & ws'1)).
      pose proof (ext_interpret_ok _ _ _ _ _ _ _ ext_interp_v1) as ei_ok.
      destruct ei_ok as (m' & (l' & nstep_ext_interp)).
      runStateT_bind.
      pose proof (IHn _ _ _ _ _ _ H0).
      destruct H as (m'' & (l'' & rest_nstep)).
      do 2 eexists.
      eapply nsteps_transitive; [ctx_step (fill ([ExternalOpCtx op]))|].
      eapply nsteps_transitive; [exact nstep_ext_interp | exact rest_nstep].
    }
  Qed.
End interpreter.
