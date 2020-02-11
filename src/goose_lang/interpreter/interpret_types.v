From Perennial.goose_lang Require Import prelude.

(* Interpreter Helper Stuff *)  
Notation "x <- p1 ; p2" := (mbind (fun x => p2) p1) 
                              (at level 60, right associativity).

Inductive Error (X: Type) : Type :=
| Works (v: X)
| Fail (s: string)
.

Instance Error_fmap : FMap Error :=
  fun A B f => (fun err => match err with
                     | Works _ x => Works _ (f x)
                     | Fail _ s => Fail _ s
                     end).

Instance Error_ret : MRet Error := Works.

(* eex : Error Error A *)
Instance Error_join : MJoin Error :=
  fun A eex => match eex with
            | Works _ (Fail _ s) => Fail _ s
            | Works _ (Works _ x) => Works _ x
            | Fail _ s => Fail _ s
            end.

Instance Error_bind : MBind Error :=
  (fun _ _ f a => mjoin (f <$> a)).

Inductive WriterT w M (A: Type) : Type :=
| makeWriterT (maws : M (prod A (list w))) (* TODO: gset instead of list? *)
.

Definition runWriterT {w M A} (wa : WriterT w M A) : M (prod A (list w)) :=
  match wa with
  | makeWriterT _ _ _ maws => maws
  end.

Definition WriterT_ret {w} M (mr : MRet M) : MRet (WriterT w M) :=
  (fun _ v => makeWriterT _ _ _ (mret (v, nil))).

Definition WriterT_fmap {w} M (mf : FMap M) : FMap (WriterT w M) :=
  (fun A B f => (fun wa => match wa with
                 | makeWriterT _ _ _ maws =>
                   makeWriterT _ _ _ $ fmap (fun p => (f (fst p), snd p)) maws
                 end)).

Definition WriterT_join {w} M (mf : FMap M) (mj : MJoin M) : MJoin (WriterT w M) :=
  (fun A wtwta => match wtwta with
             | makeWriterT _ _ _ mwtaws =>
               makeWriterT _ _ _ $
                           mjoin ((fun (p : (WriterT w M A * list w)) =>
                                     match p with
                                       | (makeWriterT _ _ _ maws, ws) =>
                                         (fun (q : (A * list w)) =>
                                            (fst q, snd q ++ ws)) <$> maws
                                     end) <$> mwtaws)
               end).

Definition WriterT_bind {w} M (mf: FMap M) (mj: MJoin M) (mb: MBind M) : MBind (WriterT w M) :=
  (let sj := WriterT_join M mf mj in
   let sf := WriterT_fmap M mf in
  (fun _ _ f a => mjoin (f <$> a))).

(* http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Lazy.html#t:StateT *)
(* This is a state monad transformer, which takes a pre-existing monad
M and produces a new monad StateT M. *)
Inductive StateT Σ M (X: Type) : Type :=
| StateFn (f : (Σ -> M (prod X Σ)))
.

(* Turns a StateT M X back into a function (input Σ) -> M (X, ending Σ) *)
Definition runStateT {Σ: Type} {M} {X: Type} (mf: StateT Σ M X) (s: Σ) : M (prod X Σ) :=
  match mf with
  | StateFn _ _ _ f => f s
  end.

(* fmap, join, bind, and ret definitions for the monad StateT M,
 * defined in terms of the corresponding monad operations for the monad M. *)
Definition StateT_fmap {Σ: Type} M (mf : FMap M) : FMap (StateT Σ M) :=
  (fun A B f => (fun sa => match sa with
                 | StateFn _ _ _ sf =>
                   StateFn _ _ _ (fun s => (mf _ _ (fun p => match p with
                                             | (x, s') => (f x, s')
                                             end))(sf s))
                 end)).

Definition StateT_join {Σ: Type} M (mf : FMap M) (mj : MJoin M) : MJoin (StateT Σ M) :=
  (fun A ssm => match ssm with
             | StateFn _ _ _ ssf =>
               StateFn _ _ _ (fun st =>
                              mjoin ((fun (p : (StateT Σ M A * Σ)%type) =>
                                        match p with
                                        | (StateFn _ _ _ sf, st') => (sf st')
                                        end) <$> (ssf st)))
             end).

Definition StateT_bind {Σ: Type} M (mf: FMap M) (mj: MJoin M) (mb: MBind M) : MBind (StateT Σ M) :=
  (let sj := StateT_join M mf mj in
   let sf := StateT_fmap M mf in
  (fun _ _ f a => mjoin (f <$> a))).

Lemma runStateT_Error_bind {Σ: Type} :
  forall X Y (ma: StateT Σ Error X) v σ σ' f,
  (runStateT ma σ = Works _ (v, σ')) ->
  runStateT (@mbind (StateT Σ Error) (StateT_bind Error Error_fmap Error_join Error_bind) X Y f ma) σ = runStateT (f v) σ'. 
Proof.
  intros. unfold runStateT.
  unfold runStateT in H.
  destruct ma as [maf].
  unfold mbind.
  unfold StateT_bind.
  unfold mjoin.
  unfold StateT_join.
  unfold fmap.
  unfold StateT_fmap.
  rewrite H.
  simpl.
  destruct (f v).
  destruct (f0 σ'); reflexivity.
Qed.

Lemma runStateT_Error_bind_false {Σ: Type} :
  forall X Y (ma: StateT Σ Error X) σ f s,
  (runStateT ma σ = Fail _ s) ->
  runStateT (@mbind (StateT Σ Error) (StateT_bind Error Error_fmap Error_join Error_bind) X Y f ma) σ = Fail _ s. 
Proof.
  intros. unfold runStateT.
  unfold runStateT in H.
  destruct ma as [maf].
  unfold mbind.
  unfold StateT_bind.
  unfold mjoin.
  unfold StateT_join.
  unfold fmap.
  unfold StateT_fmap.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Hint Resolve runStateT_Error_bind : core.

Definition StateT_ret {Σ: Type} M (mr: MRet M) : MRet (StateT Σ M) :=
  (fun _ v => StateFn _ _ _ (fun s => mret (v, s))).

Definition mfail {Σ: Type} {X: Type} (msg: string) : StateT Σ Error X :=
  StateFn _ _ _ (fun (s: Σ) => Fail _ msg).

(* Turns a normal option X into a StateT Error X *)
Definition mlift {Σ: Type} {X : Type} (err_x: option X) (msg: string) : StateT Σ Error X :=
  StateFn _ _ _ (fun (s: Σ) => match err_x with
                              | None => Fail _ msg
                              | Some x => Works _ (x, s)
                              end).

Definition mget {Σ: Type} {M} {_: MRet M} : StateT Σ M Σ :=
  StateFn _ _ _ (fun (s: Σ) => mret (s, s)).

Definition mput {Σ: Type} {M} {_: MRet M} (newstate: Σ) : StateT Σ M () :=
  StateFn _ _ _ (fun (s: Σ) => mret ((), newstate)).

Definition mupdate {Σ: Type} {M} {_: FMap M} {_: MRet M} {_: MBind M} {_: MJoin M} (f: Σ -> Σ) : StateT Σ M () :=
  let _ := StateT_bind M _ _ _ in
  s <- mget;
  mput (f s).
