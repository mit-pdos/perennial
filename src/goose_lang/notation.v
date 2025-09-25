From Perennial.program_logic Require Import language.
From Perennial.goose_lang Require Export lang.
From Perennial.Helpers Require Export ByteString.
Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Global Open Scope Z. (* Make sure everyone gets this scope. *)

(** Coercions to make programs easier to type. *)
(* integers by default turn into u64 literals

   note that we can't also make W32 a coercion because otherwise we would have
   ambiguous paths between Z and base_lit.
 *)
Coercion W64 : Z >-> w64.
Add Printing Coercion W64.

Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
(* TODO: this should be added *)
(* Coercion LitString : string >-> base_lit. *)
Coercion LitInt : u64 >-> base_lit.
Coercion LitInt32 : u32 >-> base_lit.
Coercion LitInt16 : w16 >-> base_lit.
Coercion LitByte : u8 >-> base_lit.
Coercion LitProphecy : proph_id >-> base_lit.
Notation "'str' s" := (LitString (s : byte_string)) (at level 30, format "'str'  s") : val_scope.

Definition b2val {ext: ffi_syntax}: u8 -> val := λ (b:u8), LitV (LitByte b).
Global Instance b2val_inj {ext: ffi_syntax} : Inj eq eq b2val.
Proof.
  intros b1 b2 Heq.
  inversion Heq; auto.
Qed.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
(** As of https://github.com/coq/coq/pull/15789 Coq does not require the uniform
inheritance criteria, but silencing the warning is still required. *)
#[warning="-uniform-inheritance"]
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation Alloc e := (AllocN (Val $ LitV $ LitInt (W64 1)) e).
(** Compare-and-set (CAS) returns just a boolean indicating success or failure. *)
Notation CAS l e1 e2 := (Snd (CmpXchg l e1 e2)) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).
Definition Linearize {ext:ffi_syntax}: expr := Skip.

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>
    lots of stuff bla bla bla bla bla bla bla bla
  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E) (at level 10) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E) : expr_scope.
Notation "'u_to_w64' e" := (UnOp UToW64Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w32' e" := (UnOp UToW32Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w16' e" := (UnOp UToW16Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w8' e" := (UnOp UToW8Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w64' e" := (UnOp SToW64Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w32' e" := (UnOp SToW32Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w16' e" := (UnOp SToW16Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w8' e" := (UnOp SToW8Op e%E) (at level 10) : expr_scope.
Notation "'to_u64' e" := (UnOp UToW64Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u32' e" := (UnOp UToW32Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u16' e" := (UnOp UToW16Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u8' e" := (UnOp UToW8Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_string' e" := (UnOp ToStringOp e%E) (at level 10) : expr_scope.
Notation "'StringLength' e" := (UnOp StringLenOp e%E) (at level 10) : expr_scope.
Notation "'IsNoStringOverflow' e" := (UnOp IsNoStringOverflowOp e%E) (at level 10) : expr_scope.

Notation "'StringGet'" := (BinOp StringGetOp) (at level 10) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp (OffsetOp 1) e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 `or` e2" := (BinOp OrOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `and` e2" := (BinOp AndOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `xor` e2" := (BinOp XorOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `quots` e2" := (BinOp QuotSignedOp e1%E e2%E) (at level 35) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 `rems` e2" := (BinOp RemSignedOp e1%E e2%E) (at level 35) : expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%E e2%E) : expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%E e2%E) : expr_scope.
(* models Go's &^ operator *)
Notation "e1 `and_not` e2" := (BinOp AndOp e1%E (UnOp NegOp e2%E)) (at level 40, only parsing) : expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 ≥ e2" := (BinOp LeOp e2%E e1%E) : expr_scope.
Notation "e1 > e2" := (BinOp LtOp e2%E e1%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.

Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
Definition Store {ext:ffi_syntax} : val :=
  LamV "l" (Lam "v" (Seq
                     (PrepareWrite (Var "l"))
                     (FinishStore (Var "l") (Var "v")))).
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

Definition Read {ext:ffi_syntax} : val :=
  LamV "l" ((Let "v" (StartRead (Var "l"))
                     (Seq (FinishRead (Var "l"))
                          (Var "v")))).

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%E e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
(* TODO: this notation is not hygienic because it introduces __p into e1's scope

we could do slightly better by using a variable that can't appear in Go (eg, one
with spaces), but we would probably still handle nested destructuring
incorrectly *)
Notation "'let:' ( a1 , a2 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder e2%E (Snd "__p")) (Fst "__p"))
    e1%E)
  (at level 200, a1, a2 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( a1 , a2 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( a1 , a2 ) , a3 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Fst (Fst "__p")))
    e1%E)
  (at level 200, a1, a2, a3 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( a1 , a2 ) , a3 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( a1 , a2 ) , a3 ) , a4 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Fst (Fst (Fst "__p"))))
    e1%E)
  (at level 200, a1, a2, a3, a4 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( a1 , a2 ) , a3 ) , a4 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder (Lam a5%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Snd (Fst (Fst (Fst "__p"))))) (Fst (Fst (Fst (Fst "__p")))))
    e1%E)
  (at level 200, a1, a2, a3, a4, a5 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) , a6 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder
      (Lam a5%binder (Lam a6%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Snd (Fst (Fst (Fst "__p"))))) (Snd (Fst (Fst (Fst (Fst "__p"))))))
      (Fst (Fst (Fst (Fst (Fst "__p"))))))
    e1%E)
  (at level 200, a1, a2, a3, a4, a5, a6 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) , a6 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (LitV (LitBool false))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (LitV (LitBool true)) e2%E) (only parsing) : expr_scope.

(** Notations for option *)
Notation NONE := (InjL (LitV LitUnit)) (only parsing).
Notation NONEV := (InjLV (LitV LitUnit)) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

(*
Notation ResolveProph e1 e2 := (Resolve Skip e1 e2) (only parsing).
Notation "'resolve_proph:' p 'to:' v" := (ResolveProph p v) (at level 100) : expr_scope.
*)
