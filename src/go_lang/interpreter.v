From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.go_lang Require Export locations.
From Perennial.go_lang Require Export lang.
From Perennial Require Export Helpers.Integers.
From Perennial.go_lang Require Import prelude.

From Perennial.go_lang.examples Require Import goose_unittest.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Section go_lang_int.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}
          {ffi_interpretable: @ext_interpretable ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

(* Interpreter *)  
Notation "x <- p1 ; p2" := (mbind (fun x => p2) p1) 
                              (at level 60, right associativity).

(* http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Lazy.html#t:StateT *)
(* This is a state monad transformer, which takes a pre-existing monad M and produces a new monad StateT M. *)
Inductive StateT M (X: Type) : Type :=
| StateFn (f : (state -> M (prod X state)))
.

(* Turns a StateT M X back into a function (input state) -> M (X, ending state) *)
Definition runStateT {M} {X: Type} (mf: StateT M X) (s: state) : M (prod X state) :=
  match mf with
  | StateFn _ _ f => f s
  end.

(* fmap, join, bind, and ret definitions for the monad StateT M,
 * defined in terms of the corresponding monad operations for the monad M. *)
Definition StateT_fmap M (mf : FMap M) : FMap (StateT M) :=
  (fun A B f => (fun sa => match sa with
                 | StateFn _ _ sf =>
                   StateFn _ _ (fun s => (mf _ _ (fun p => match p with
                                             | (x, s') => (f x, s')
                                             end))(sf s))
                 end)).

Definition StateT_join M (mf : FMap M) (mj : MJoin M) : MJoin (StateT M) :=
  (fun A ssm => match ssm with
             | StateFn _ _ ssf =>
               StateFn _ _ (fun st =>
                              mjoin ((fun (p : (StateT M A * state)%type) =>
                                        match p with
                                        | (StateFn _ _ sf, st') => (sf st')
                                        end) <$> (ssf st)))
             end).

Definition StateT_bind M (mf: FMap M) (mj: MJoin M) (mb: MBind M) : MBind (StateT M) :=
  (let sj := StateT_join M mf mj in
   let sf := StateT_fmap M mf in
  (fun _ _ f a => mjoin (f <$> a))).

Definition StateT_ret M (mr: MRet M) : MRet (StateT M) :=
  (fun _ v => StateFn _ _ (fun s => mret (v, s))).

(* Bind and Ret instances for StateT option, using the instance keyword so that the _ <- _ ; _ notation and mret work properly *)
Instance statet_option_bind : MBind (StateT option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_option_ret : MRet (StateT option) :=
  StateT_ret option option_ret.

Definition mfail {X: Type} : StateT option X :=
  StateFn _ _ (fun (s: state) => None).

(* Turns a normal option X into a StateT option X *)
Definition mlift {X : Type} (err_x: option X) : StateT option X :=

  StateFn _ _ (fun (s: state) => match err_x with
                              | None => None
                              | Some x => Some (x, s)
                              end).

Definition mget {M} {_: MRet M} : StateT M state :=
  StateFn _ _ (fun (s: state) => mret (s, s)).

Definition mput {M} {_: MRet M} (newstate: state) : StateT M () :=
  StateFn _ _ (fun (s: state) => mret ((), newstate)).

Definition mupdate {M} {_: FMap M} {_: MRet M} {_: MBind M} {_: MJoin M} (f: state -> state) : StateT M () :=
  let _ := StateT_bind M _ _ _ in
  s <- mget;
  mput (f s).

Fixpoint interpret (fuel: nat) (e: expr) : StateT option val :=
  match fuel with
  | O => mfail
  | S n =>
    match e with
    | Val v => mret v
    | Var y => mfail
    | Rec f y e => mret (RecV f y e)
    | App e1 e2 => 
      e1' <- interpret n e1;
        match e1' with
        | RecV BAnon BAnon ex => interpret n ex
        | RecV BAnon (BNamed y) ex =>
          v <- interpret n e2;
            let e3 := subst y v ex in
            interpret n e3
        | RecV (BNamed f) BAnon ex =>
          let e3 := subst f e1' ex in
          interpret n e3
        | RecV (BNamed f) (BNamed y) ex =>
          v <- interpret n e2;
            let e3 := subst f e1' (subst y v ex) in
            interpret n e3
        | _ => mfail
        end
          
    | UnOp op e =>
      e' <- interpret n e;
        mlift (un_op_eval op e')
                   
    | BinOp op e1 e2 =>
      e1' <- interpret n e1;
        e2' <- interpret n e2;
        mlift (bin_op_eval op e1' e2')
                    
    | If e0 e1 e2 =>
      c <- interpret n e0;
        match c with
        | LitV (LitBool true) => interpret n e1
        | LitV (LitBool false) => interpret n e2
        | _ => mfail
        end

    | Pair e1 e2 =>
        a <- interpret n e1;
        b <- interpret n e2;
        mret (PairV a b)
            
    | Fst e =>
      e' <- interpret n e;
      match e' with
      | PairV v1 v2 => mret v1
      | _ => mfail
      end

    | Snd e =>
      e' <- interpret n e;
      match e' with
      | PairV v1 v2 => mret v2
      | _ => mfail
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
      | _ => mfail
      end

    | Fork e => mfail
    | Primitive0 op => mfail
    | Primitive1 op e => mfail
    | Primitive2 op e1 e2 => mfail
    | ExternalOp op e => mfail
    | CmpXchg e0 e1 e2 => mfail
    | NewProph => mfail (* ignore *)
    | Resolve ex e1 e2 => mfail
    end
  end.

(* Testing *)
Definition TypedInt : expr := #32.
Definition ConstWithArith : expr := #4 + #3 * TypedInt.

Print ConstWithArith.

Definition testRec : expr :=
  (rec: BAnon BAnon :=
     #3 + #3).
     
Definition literalCast: expr :=
  λ: <>,
    let: "x" := #2 in
    (Var "x") + #2.

Definition ifStatement: expr :=
  λ: <>,
    let: "m" := #2 in
    (if: (Var "m") > #3
    then #3
    else #1).

Definition matchtest: val :=
  λ: "x",
  match: (Var "x") with
    InjL "x1" => #3 + (Var "x1")
  | InjR "x1" => #4 + (Var "x1")
  end.

Print literalCast.
Print testRec.

End go_lang_int.

(* test Fst and Snd *)
Compute (runStateT (interpret 10 (returnTwoWrapper #3)) inhabitant).

Compute (runStateT (interpret 10 (testRec _)) inhabitant).
Compute (runStateT (interpret 10 ConstWithArith) inhabitant).
Compute (runStateT (interpret 10 (literalCast _)) inhabitant).
Compute (runStateT (interpret 10 (useMap _)) inhabitant).
Compute (runStateT (interpret 10 (ifStatement _)) inhabitant).
Compute (runStateT (interpret 10 (matchtest (InjL #2))) inhabitant).
Compute (runStateT (interpret 10 (matchtest (InjR #2))) inhabitant).
