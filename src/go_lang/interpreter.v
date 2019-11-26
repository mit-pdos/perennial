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
          {ffi_semantics: ext_semantics ext ffi}.
          {ffi_interprable: ext_interprable ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

(* Interpreter *)  
Notation "x <- p1 ; p2" := (mbind (fun x => p2) p1) 
                              (at level 60, right associativity).

Fixpoint interpret (e: expr) (fuel: nat) : option val :=  
  match fuel with
  | O => None
  | S n =>
    match e with
    | Val v => Some v
                   
    | Var y => None
                
    | Rec f y e => Some (RecV f y e)
                       
    | App e1 e2 => 
      e1' <- interpret e1 n;
        match e1' with
        | RecV BAnon BAnon ex => interpret ex n
        | RecV BAnon (BNamed y) ex =>
          v <- interpret e2 n;
            let e3 := subst y v ex in
            interpret e3 n
        | RecV (BNamed f) BAnon ex =>
            let e3 := subst f e1' ex in
            interpret e3 n
        | RecV (BNamed f) (BNamed y) ex =>
          v <- interpret e2 n;
            let e3 := subst f e1' (subst y v ex) in
            interpret e3 n
        | _ => None
        end
          
    | UnOp op e =>
      e' <- interpret e n;
        un_op_eval op e'
                   
    | BinOp op e1 e2 =>
      e1' <- interpret e1 n;
        e2' <- interpret e2 n;
        bin_op_eval op e1' e2'
                    
    | If e0 e1 e2 =>
      c <- interpret e0 n;
        match c with
        | LitV (LitBool true) => interpret e1 n
        | LitV (LitBool false) => interpret e2 n
        | _ => None
        end

    | Pair e1 e2 =>
        a <- interpret e1 n;
        b <- interpret e2 n;
        Some (PairV a b)
            
    | Fst e =>
      e' <- interpret e n;
      match e' with
      | PairV v1 v2 => Some v1
      | _ => None
      end

    | Snd e =>
      e' <- interpret e n;
      match e' with
      | PairV v1 v2 => Some v2
      | _ => None
      end
      
    | InjL e => None
    | InjR e => None
    | Case e0 e1 e2 => None
    | Fork e => None
    | Primitive0 op => None
    | Primitive1 op e => None
    | Primitive2 op e1 e2 => None
    | ExternalOp op e => None
    | CmpXchg e0 e1 e2 => None
    | NewProph => None (* ignore *)
    | Resolve ex e1 e2 => None
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

Print literalCast.
Print testRec.

End go_lang_int.

(* test Fst and Snd *)
Eval cbv in interpret (returnTwoWrapper #3) 10.

Eval cbv in (testRec _).
Eval cbv in interpret ConstWithArith 3.
Eval cbv in interpret (literalCast _) 1000.
Eval cbv in interpret (useMap _) 100.
