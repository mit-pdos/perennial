From iris.program_logic Require Import language.
From Perennial.goose_lang Require Export lang.
Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** Coercions to make programs easier to type. *)
(* integers by default turn into u64 literals

   note that we can't also make U32 a coercion because otherwise we would have
   ambiguous paths between Z and base_lit.
 *)
Coercion U64 : Z >-> u64.

Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
(* Coercion LitInt' (x:u64_class) : base_lit := LitInt x.
Coercion LitInt32' (x:u32_class) : base_lit := LitInt32 x. *)
Coercion LitInt : u64 >-> base_lit.
Coercion LitInt32 : u32 >-> base_lit.
Coercion LitByte : u8 >-> base_lit.
Coercion LitProphecy : proph_id >-> base_lit.
Notation "'str' s" := (LitString s) (at level 30, format "'str' s") : val_scope.

Definition b2val {ext: ext_op}: u8 -> val := λ (b:u8), LitV (LitByte b).

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
(* Coercion Var : string >-> expr. *)

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation Alloc e := (AllocN (Val $ LitV $ LitInt (word.of_Z 1)) e) (only parsing).
(** Compare-and-set (CAS) returns just a boolean indicating success or failure. *)
Notation CAS l e1 e2 := (Snd (CmpXchg l e1 e2)) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).


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
Notation "'to_u64' e" := (UnOp ToUInt64Op e%E) (at level 10) : expr_scope.
Notation "'to_u32' e" := (UnOp ToUInt32Op e%E) (at level 10) : expr_scope.
Notation "'to_u8' e" := (UnOp ToUInt8Op e%E) (at level 10) : expr_scope.
Notation "'to_string' e" := (UnOp ToStringOp e%E) (at level 10) : expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp (OffsetOp 1) e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 ∥ e2" := (BinOp OrOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 & e2" := (BinOp AndOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 ^^ e2" := (BinOp XorOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%E e2%E) : expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%E e2%E) : expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 ≥ e2" := (BinOp LeOp e2%E e1%E) : expr_scope.
Notation "e1 > e2" := (BinOp LtOp e2%E e1%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.

Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
Definition Store {ext:ext_op} : val :=
  LamV "l" (Lam "v" (Seq
                     (PrepareWrite (Var "l"))
                     (FinishStore (Var "l") (Var "v")))).
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

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
Notation "'let:' ( x , y ) := e1 'in' e2" :=
  (Lam "__p"
       (Lam x%binder (Lam y%binder e2%E (Snd "__p")) (Fst "__p"))
       e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  ( x ,  y )  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
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

Notation ResolveProph e1 e2 := (Resolve Skip e1 e2) (only parsing).
Notation "'resolve_proph:' p 'to:' v" := (ResolveProph p v) (at level 100) : expr_scope.


Definition ForRange {ext:ext_op} (v:string) (bound:expr) (body:expr) : expr :=
  (rec: "__loop" v :=
     if: Var v < bound
     then body;;
          (Var "__loop") (Var v + #1)
     else #()) #0.
Notation "'for-range:' v < b := e" := (ForRange v%string b%E e%E)
  (at level 200, v at level 1, b at level 1, e at level 200,
   format "'[' 'for-range:'  v  <  b  :=  '/  ' e ']'") : expr_scope.

(* idiomatic wrappers for loop control flow *)
Definition Continue {ext:ext_op}: val := #true.
Definition Break {ext:ext_op}: val := #false.

Definition For {ext:ext_op}: val :=
  λ: "cond" "body" "post",
  (rec: "loop" <> :=
     if: (Var "cond") #()
     then let: "continue" := (Var "body") #() in
          if: (Var "continue")
          then (Var "post") #();; (Var "loop") #()
          else #()
     else #()) #().
Notation "'for:' cond ; post := e" := (For cond%E e%E post%E)
  (at level 200, cond, post at level 1, e at level 200,
   format "'[' 'for:'  cond  ;  post  :=  '/  ' e ']'") : expr_scope.

Definition Loop {ext:ext_op} (body:expr) : expr :=
  (rec: "__loop" BAnon :=
     let: "__continue" := body in
     if: (Var "__continue")
     then (Var "__loop") #()
     else #()) #().
Notation "'for:' := e" := (Loop e%E)
  (at level 200, e at level 200,
   format "'[' 'for:'  :=  '/  ' e ']'") : expr_scope.
