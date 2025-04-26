From Coq.Program Require Import Equality.
From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From Perennial.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import CountableTactics.
From Perennial.Helpers Require Import Transitions.
From Perennial.Helpers Require Import ByteString.
From Perennial.program_logic Require Export crash_lang.
From Perennial.goose_lang Require Export locations.
From Perennial Require Export Helpers.Integers.
Import RecordSetNotations.

Definition go_string := byte_string.
Delimit Scope byte_string_scope with go.
Bind Scope byte_string_scope with go_string.
Delimit Scope byte_char_scope with go_byte.

(* Formalization of the syntax in https://go.dev/ref/spec *)
Module go.

Definition type_name := go_string.

Definition identifier := go_string.

Inductive type :=
| Named : type_name → type_args → _
| TypeLit : type_lit → _

with type_args := | TypeArgs : list type → _

with type_lit :=
| ArrayType : w64 → type → _
| StructType : list field_decl → _
| PointerType : type → _
| FunctionType : signature → _
| InterfaceType : (list interface_elem) → _
| SliceType : type → _
| MapType : type → type → _
| ChannelType : option bool → type → _

with field_decl :=
| FieldDecl : (list go_string) → type → _
| EmbeddedField : bool → go_string → type_args → _

with signature := | Signature : parameters → result → _

with parameters := | ParameterList : (list parameter_decl) → _

with parameter_decl := | ParameterDecl : (list identifier) → (* variadic *) bool → _

with result :=
| ResultParameters : parameters → _
| ResultType : type → _

with interface_elem :=
| MethodElem : identifier → signature → _
| TypeElem : list type_term → _

with type_term := | TypeTerm (type : type) | TypeTermUnderlying (type : type).

Definition type_constraint := list type_term.

Inductive type_param_decl :=
| TypeParamDecl : list identifier → type_constraint → _
.

Definition type_parameters := list type_param_decl.

Inductive add_op :=
| Plus | Sub | BitwiseOr | BitwiseXor.

Inductive mul_op :=
| Mul | Div | Modulo | Shiftl | Shiftr | BitwiseAnd | BitwiseClear.

Inductive unary_op  :=
| UnaryPlus | UnarySub | UnaryNeg | UnaryXor | UnaryDeref | UnaryRef | UnaryReceive.

Inductive rel_op := Eq | Neq | Lt | Leq | Gt | Geq.

Inductive binary_op :=
| Or | And | RelOp : rel_op → _ | AddOp : add_op → _ | MulOp : mul_op → _.

Inductive top_level_decl :=
| Declaration : declaration → _
| FunctionDecl : identifier → type_parameters → signature → block → _
| MethodDecl : parameters → identifier → signature → block → _

with declaration :=
| ConstDecl : list const_spec → _
| TypeDecl : list type_spec → _
| VarDecl : list var_spec → _

with const_spec := | ConstSpec : list identifier → option type → list expression → _
with type_spec :=
| AliasDecl : identifier → type_parameters → type → _
| TypeDef : identifier → type_parameters → type → _

with var_spec :=
| VarSpec : list identifier → option type → list expression → _

with block := | Block : list statement → _

with statement :=
| DeclarationStmt : declaration → _
| LabeledStmt : identifier → statement → _
| SimpleStmt : simple_stmt → _
| GoStmt : expression → _
| ReturnStmt : list expression → _
| BreakStmt : option identifier → _
| ContinueStmt : option identifier → _
| GotoStmt : identifier → _
| FallthroughStmt : _
| BlockStmt : block → _
(* Don't permit IfStmt directly after the else *)
| IfStmt : option simple_stmt → expression → block → option block → _
| SwitchStmt : switch_stmt → _
| SelectStmt : list comm_clause → _
| ForStmt : for_cases → block → _
| DeferStmt : expression → _

with simple_stmt :=
| EmptyStmt
| ExpressionStmt : expression → _
| SendStmt : expression → expression → _
| IncDecStmt : expression → bool → _
| Assignment : list expression → option (sum add_op mul_op) → list expression → _
| ShortVarDecl : list identifier → list expression → _

with switch_stmt  :=
| ExprSwitchStmt : option simple_stmt → option expression → list expr_case_clause → _
| TypeSwitchStmt : option simple_stmt → type_switch_guard → list type_case_clause → _

with expr_case_clause :=
| ExprCaseClause : expr_switch_case → list statement → _

with expr_switch_case :=
| ExprSwitchCase : list expression → _
| ExprSwitchDefault : _

with type_switch_guard :=
| TypeSwitchGuard : option identifier → primary_expr → _

with type_case_clause :=
| TypeCaseClause : type_switch_case → list statement → _

with type_switch_case :=
| TypeSwitchCase : list type → _
| TypeSwitchDefault : _

with comm_clause :=
| CommClause : comm_case → list statement → _

with comm_case :=
| CommSendStmt : expression → expression → _
| CommRecvStmtDefine : list identifier → expression → _
| CommRecvStmtAssign : list expression → expression → _
| CommDefault : _

(* assumes normalization: [for {  }] → [for true {  }] *)
with for_cases :=
| ForCondition : expression → _
| ForClause : simple_stmt → expression → simple_stmt → _
| ForRangeClauseDefine : list identifier → expression → _
| ForRangeClauseAssign : list expression → expression → _

with expression :=
| UnaryExpr : unary_expr → _
| BinaryExpr : expression → binary_op → expression  → _

with unary_expr :=
| UnaryPrimaryExpr : primary_expr → _
| UnaryOpExpr : unary_op → unary_expr → _

with primary_expr :=
| Operand : operand → _
| Conversion : type → expression → _
| MethodExpr : type → identifier → _
| SelectorExpr : primary_expr → identifier → _
| IndexExpr : primary_expr → expression → _
| SliceExpr : primary_expr → slice → _
| TypeAssertionExpr : primary_expr → type → _
| CallExpr : primary_expr → list expression → _
| CallSpecialExpr : primary_expr → type → list expression → _

with slice :=
| Slice : option expression → option expression → _
| SliceFull : option expression → expression → expression → _

with operand :=
| Literal : literal → _
| Instantiation : identifier → type_args → _
| ParenExpr : expression → _

with literal :=
| BasicLit : basic_lit → _
| CompositeLit : literal_type → literal_value → _
| FunctionLit : signature → block → _

with basic_lit :=
| Int : Z → _ | Float : string →  _ | Imaginary : string → _
| Rune : string → _ | String : string → _

(* duplicates some [type] constructors *)
with literal_type :=
| LiteralStructType : list field_decl → _
| LiteralArrayType : option w64 → type → _
| LiteralSliceType : type → _
| LiteralMapType : type → _
| LiteralNamedType : identifier → type_args → _

with literal_value :=
| LiteralValue : list keyed_element → _

with keyed_element :=
| KeyedElement : option key → element → _

with key :=
| KeyFieldName : identifier → _
| KeyExpression : expression → _
| KeyLiteralValue : literal_value → _

with element :=
| ElementExpression : expression → _
| ElementLiteralValue : literal_value → _
.

(* TODO: technically should have package clause and importdecls *)
Definition program := list top_level_decl.

End go.

(** Note about higher order heap:
   Guarded type theory (as used by guarded interaction trees [1]) would give a
   way to put [ecomp]s on a heap. However, this requires using the later type [▶]
   modality, which seems likely to complicate the semantics.

   Another option, taken by the Iris ITree library [2], is to not directly put
   [ecomp]s on the heap, but rather a piece of syntax that can be interpreted
   into an [ecomp]. This should be sufficient for modeling a real programming
   language.

   [1]: https://iris-project.org/pdfs/2024-popl-gitrees.pdf
   [2]: https://research.ralfj.de/papers/2025-popl-itree-program-logic.pdf
 *)

Inductive ecomp (E : Type → Type) (R : Type) : Type :=
| Pure (r : R) : ecomp E R
| Effect {A} (e : E A) (k : A → ecomp E R) : ecomp E R
(* Having a separate [Bind] permits binding at pure computation steps, whereas
   binding only in [Effect] results in a shallower (and thus easier to reason
   about) embedding. *)
.

Arguments Pure {_ _} (_).
Arguments Effect {_ _ _} (_ _).

(* Definition Handler E M := ∀ (A B : Type) (e : E A) (k : A → M B), M B. *)
Fixpoint ecomp_bind {E} A B (kx : A → ecomp E B) (x : ecomp E A) : (ecomp E B) :=
  match x with
  | Pure r => kx r
  | Effect e k => (Effect e (λ c, ecomp_bind _ _ kx (k c)))
  end.
Instance ecomp_MBind E : MBind (ecomp E) := ecomp_bind.

Instance ecomp_MRet E : MRet (ecomp E) := (@Pure E).

(* | FunctionDecl : identifier → type_parameters → signature → block → _ *)

Inductive literal_val :=
| LZ (z : Z)
.

Inductive heap_val :=
| HW64 (w : w64)
| HW32 (w : w32)
| HW8 (w : w8)
| HBool (b : bool)
| HFun (fname : string).

Definition val := list heap_val.

Inductive goE : Type → Type :=
| SuchThat {A} (pred : A → Prop) : goE A
| Load (l : loc) : goE heap_val
| Store (l : loc) (v : heap_val) : goE unit
| Assume (b : Prop) : goE unit
| Assert (b : Prop) : goE unit
| Panic (msg : go_string) : goE False
.

Fixpoint interpret_expr (e : go.expression) : ecomp goE (list val) :=
  match e with
  | go.UnaryExpr (go.UnaryPrimaryExpr p) => interpret_primary_expr p
  | _ => Effect (Panic "unsupported expression"%go) (λ (x : False), match x with end)
  end
with interpret_primary_expr (e : go.primary_expr) : ecomp goE (list val) :=
       match e with
       | go.Operand operand => interpret_operand operand
       | _ => Effect (Panic "unsupported primary expression"%go) (λ (x : False), match x with end)
       end
with interpret_operand (e : go.operand) : ecomp goE (list val) :=
       match e with
       | go.Literal l => interpret_literal l
       | _ => Effect (Panic "unsupported operand"%go) (λ (x : False), match x with end)
       end
with interpret_literal (l : go.literal) : ecomp goE (list val) :=
       match l with
       | go.BasicLit l => interpret_basic_lit l
       | _ => Effect (Panic "unsupported literal"%go) (λ (x : False), match x with end)
       end
with interpret_basic_lit (l : go.basic_lit) : ecomp goE (list val) :=
       match l with
       | _ => Effect (Panic "unsupported basic literal"%go) (λ (x : False), match x with end)
       end
with interpret_expr_addr (e : go.expression) : ecomp goE (list val) :=
       match e with
       | _ => Effect (Panic "unsupported expr address"%go) (λ (x : False), match x with end)
       end.

(* TODO: encoders+decoders to better types (e.g. [loc]). *)

Definition interpret_stmt (a : go.statement) k : ecomp goE (list val) :=
  match a with
  | go.SimpleStmt (go.Assignment [l] None [r]) =>
      addr ← interpret_expr_addr l ;
      Effect (Store addr) ;;
      k
  | _ => Effect (Panic "unsupported statement"%go) (λ (x : False), match x with end)
  end
.

Axiom go_denotes : ∀ {A R} (a : goAst) (e : A → ecomp goE R), Prop.

Record state :=
  mk {
    heap : gmap loc heap_val;
    funcs : gmap string goAst;
  }.
Global Instance settable : Settable _ :=
  settable! mk <heap; funcs>.

Definition Handler (E M : Type → Type) := ∀ A (e : E A), M A.

Definition handle_goE : Handler goE (relation.t state) :=
  λ A e,
    match e with
    | SuchThat pred => λ σ σ' a, pred a ∧ σ' = σ
    | Load l => λ σ σ' v, σ' = σ ∧ σ.(heap) !! l = Some v
    | Store l v => λ σ σ' _, σ' = (σ <| heap := <[l := v]> σ.(heap) |>)
    | GetFun fname => λ σ σ' f, σ' = σ ∧ σ.(funcs) !! fname = Some f
    | _ => λ σ σ' _, False
    end.

Definition test_program : loc → ecomp goE (w64 → ecomp goE unit) :=
  λ l, Pure (λ v, Effect (Store l (HW64 v)) Pure).

Definition try_loading : string → ecomp goE (w64 → ecomp goE unit) :=
  λ fname, Effect (GetFun fname) (λ gast, ).

Polymorphic Inductive plist (A : Type) :=
| nil : plist A
| cons : A -> plist A -> plist A.

Instance i : Inhabited Type. constructor. exact unit. Qed.

Definition type_context :=
  gmap go.identifier (go.type_parameters * go.type).

(** Difficult to define an easy to use canonical Gallina [Type] given a [go.type]. *)
Inductive is_val_type {Γ : type_context} : go.type → Type → Prop :=
(* Doesn't handle generics *)
| named_type n t T (Hctx : Γ !! n = Some ([], t)) (Hty : is_val_type t T) :
  is_val_type (go.Named n (go.TypeArgs [])) T
| uint64_type :
  is_val_type (go.Named "uint64"%go (go.TypeArgs [])) w64
| array_type n elem elemT (Helem : is_val_type elem elemT) :
  is_val_type (go.TypeLit $ go.ArrayType n elem) (vec elemT (uint.nat n))
| pointer_type elem :
  is_val_type (go.TypeLit $ go.PointerType elem) loc
| slice_type elem :
  is_val_type (go.TypeLit $ go.SliceType elem) (loc * Z * Z)
| struct_type field_decls T (Fs : list Type) (proj : ∀ n, T → (Fs !!! n)) :
  (* (Hfields : Forall2 is_val_type field_decls.*1  *)
  (* How to handle named types? Maybe refer to a global typing context? *)
  (* need to have projections that line up with the field decls *)
  is_val_type (go.TypeLit $ go.StructType field_decls) T.
