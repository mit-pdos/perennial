From RecordUpdate Require Import RecordSet.
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

Fixpoint Zpos_to_str (z : positive) : string :=
  match z with
  | xI p => "i" ++ (Zpos_to_str p)
  | xO p => "o" ++ (Zpos_to_str p)
  | xH => "h"
  end.

(* This is a terrible function for debugging only. *)
Definition u64_to_str (x: Integers.u64) : string :=
  let z := int.val x in
  match z with
  | Z0 => "0"
  | Zpos p => Zpos_to_str p
  | Zneg p => "-" ++ (Zpos_to_str p)
  end.

Section go_lang_int.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}
          {ffi_interpretable: @ext_interpretable ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

(* Interpreter Helper Stuff *)  
Notation "x <- p1 ; p2" := (mbind (fun x => p2) p1) 
                              (at level 60, right associativity).

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

(* http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Lazy.html#t:StateT *)
(* This is a state monad transformer, which takes a pre-existing monad
M and produces a new monad StateT M. *)
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

(* Bind and Ret instances for StateT option, using the instance
keyword so that the _ <- _ ; _ notation and mret work properly *)
Instance statet_option_bind : MBind (StateT option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_option_ret : MRet (StateT option) :=
  StateT_ret option option_ret.

Instance statet_error_bind : MBind (StateT Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_error_ret : MRet (StateT Error) :=
  StateT_ret Error Error_ret.

Definition mfail {X: Type} (msg: string) : StateT Error X :=
  StateFn _ _ (fun (s: state) => Fail _ msg).

(* Turns a normal option X into a StateT Error X *)
Definition mlift {X : Type} (err_x: option X) (msg: string) : StateT Error X :=
  StateFn _ _ (fun (s: state) => match err_x with
                              | None => Fail _ msg
                              | Some x => Works _ (x, s)
                              end).

Definition mget {M} {_: MRet M} : StateT M state :=
  StateFn _ _ (fun (s: state) => mret (s, s)).

Definition mput {M} {_: MRet M} (newstate: state) : StateT M () :=
  StateFn _ _ (fun (s: state) => mret ((), newstate)).

Definition mupdate {M} {_: FMap M} {_: MRet M} {_: MBind M} {_: MJoin M} (f: state -> state) : StateT M () :=
  let _ := StateT_bind M _ _ _ in
  s <- mget;
  mput (f s).

(* Interpreter *)
Fixpoint interpret (fuel: nat) (e: expr) : StateT Error val :=
  match fuel with
  | O => mfail "Fuel depleted"
  | S n =>
    match e with
    | Val v => mret v
    | Var y => mfail ("Unbound variable: " ++ y)
    | Rec f y e => mret (RecV f y e)
                       
    | App e1 e2 => 
      (* RtL evaluated, so interpret e2 first *)
      v <- interpret n e2;
      e1' <- interpret n e1;
        match e1' with
        | RecV BAnon BAnon ex => interpret n ex
        | RecV BAnon (BNamed y) ex =>
          let e3 := subst y v ex in
          interpret n e3
        | RecV (BNamed f) BAnon ex =>
          let e3 := subst f e1' ex in
          interpret n e3
        | RecV (BNamed f) (BNamed y) ex =>
          let e3 := subst f e1' (subst y v ex) in
          interpret n e3
        | _ => mfail "App applied to non-function"
        end
          
    | UnOp op e =>
      e' <- interpret n e;
        mlift (un_op_eval op e') "Unop failed"
                   
    | BinOp op e1 e2 =>
      e1' <- interpret n e1;
        e2' <- interpret n e2;
        mlift (bin_op_eval op e1' e2') "binop failed"
                    
    | If e0 e1 e2 =>
      c <- interpret n e0;
        match c with
        | LitV (LitBool true) => interpret n e1
        | LitV (LitBool false) => interpret n e2
        | _ => mfail "If applied to non-bool"
        end

    | Pair e1 e2 =>
        a <- interpret n e1;
        b <- interpret n e2;
        mret (PairV a b)
            
    | Fst e =>
      e' <- interpret n e;
      match e' with
      | PairV v1 v2 => mret v1
      | _ => mfail "Fst applied to non-PairV"
      end

    | Snd e =>
      e' <- interpret n e;
      match e' with
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

    | Fork e => mfail "NotImpl: fork"

    | Primitive0 (PanicOp s) => mfail ("Panic: " ++ s)

    (* In head_step, alloc nondeterministically allocates at any valid
    location. We'll just pick the first valid location *)
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
          _ <- mput (state_init_heap l (int.val n) initv s);
          mret (LitV (LitLoc l))
      | _ => mfail "Alloc with non-integer argument"
      end
        
    | Primitive1 LoadOp e =>
      addrv <- interpret n e;
        match addrv with
          | LitV (LitInt l) => 
            s <- mget;
            (* Since Load of an address with nothing doesn't step, we
            can lift from the option monad into the StateT option
            monad here (we mfail "NotImpl" if v is None). *)
            let l' := (loc_add null (int.val l)) in
            mlift (s.(heap) !! l') ("Load Failed: " ++ (u64_to_str l))
          (* head_step in lang.v says we should expect a LitLoc here,
          but the unit tests all use LitInt? *)
          | LitV (LitLoc l) => 
            s <- mget;
            v <- mlift (s.(heap) !! l) "Load Failed loc";
            mret v
          | _ => mfail "Load with non-location argument"
        end
          
    | Primitive2 StoreOp e1 e2 =>
      val <- interpret n e2;
      addrv <- interpret n e1;
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
          | _ => mfail "Store with non-location argument"
        end
          
    | Primitive1 DecodeInt64Op e => mfail "NotImpl: decode"
    | Primitive2 EncodeInt64Op e1 e2 => mfail "NotImpl: encode"
    | Primitive1 DecodeInt32Op e => mfail "NotImpl decode"
    | Primitive2 EncodeInt32Op e1 e2 => mfail "NotImpl: encode"
    | Primitive1 ObserveOp e =>
      v <- interpret n e;
      _ <- mupdate (set trace (fun tr => tr ++ [v]));
      mret (LitV LitUnit)

    | Primitive0 _ => mfail "NotImpl: unrecognized primitive0"
    | Primitive1 _ _ => mfail "NotImpl: unrecognized primitive1"
    | Primitive2 _ _ _ => mfail "NotImpl: unrecognized primitive2"

    | ExternalOp op e => mfail "NotImpl: externalop"
    | CmpXchg e0 e1 e2 => mfail "NotImpl: cmpxchg"
    | NewProph => mfail "NotImpl: prophecy variable" (* ignore *)
    | Resolve ex e1 e2 => mfail "NotImpl: resolve"
    end
  end.

(* Testing *)
Definition TypedInt : expr := #32.
Definition ConstWithArith : expr := #4 + #3 * TypedInt.

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

Compute (runStateT (interpret 10 (returnTwoWrapper #3)) inhabitant).
Compute (runStateT (interpret 10 (testStore #0)) inhabitant).
Compute (runStateT (interpret 10 (testRec #0)) inhabitant).
Compute (runStateT (interpret 10 ConstWithArith) inhabitant).
Compute (runStateT (interpret 10 (literalCast #0)) inhabitant).

Compute (runStateT (interpret 10 (testIfStatement #0)) inhabitant).
Compute (runStateT (interpret 10 (testMatch (InjL #2))) inhabitant).
Compute (runStateT (interpret 10 (testMatch (InjR #2))) inhabitant).

(* works with 16 fuel, but really slow *)
Compute (runStateT (interpret 15 (useMap #0)) inhabitant).

(* works with 10 fuel, but really slow *)
Compute (runStateT (interpret 9 (ReassignVars #0)) inhabitant).
