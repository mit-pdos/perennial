From New.golang Require Import defn.
From New.proof Require Import grove_prelude.
From New.code.go_etcd_io.raft Require Import v3.
Import Ltac2.

Module expr.

Inductive t :=
| RawExpr (e : expr)
| Named (n : string)
| App (f : t) (args : list t)
| Val {V:Type} `{!IntoVal V} (v : V)
| Rec (f x : binder) (body : t)
| Var (x : string)
| BinOp (o : bin_op) (e1 e2 : t)
| UnOp (o : un_op) (e : t)
| If (e0 e1 e2 : t)
| Fst (e : t)

| RefTy (g : go_type)
| LoadTy (g : go_type)
| StoreTy (g : go_type)
| SliceElemRef (g : go_type)
| SliceLiteral (g : go_type)
| SliceForRange (g : go_type)
| MapMake (kt vt : go_type)
| InterfaceMake (mset : list (string*val))
.

Definition ctx : Type := (gmap string val).

Fixpoint interp (Γ : ctx) (e : t) {struct e} : expr :=
  match e with
  | RawExpr e => e
  | Named n => goose_lang.Val (default (LitV LitPoison) (Γ !! n))
  | App f args => fold_left goose_lang.App ((interp Γ) <$> args) (interp Γ f)
  | Val v => (goose_lang.Val #v)
  | Rec f x e => goose_lang.Rec f x (interp Γ e)
  | Var x => goose_lang.Var x
  | BinOp o e1 e2 => goose_lang.BinOp o (interp Γ e1) (interp Γ e2)
  | UnOp o e => goose_lang.UnOp o (interp Γ e)
  | If e0 e1 e2 => goose_lang.If (interp Γ e0) (interp Γ e1) (interp Γ e2)
  | Fst e => goose_lang.Fst (interp Γ e)

  | RefTy t => ref_ty t
  | LoadTy t => load_ty t
  | StoreTy t => store_ty t
  | SliceElemRef t => slice.elem_ref t
  | SliceLiteral t => slice.literal t
  | SliceForRange t => slice.for_range t
  | MapMake kt vt => map.make kt vt
  | InterfaceMake mset => interface.make mset
  end.

Ltac2 Type exn ::= [
    Reify_unsupported (string, constr) |
    Reify_unsupported_kind (Constr.Unsafe.kind) |
    Reify_unsupported_ident (ident)
  ].

Ltac2 rec reify (e : constr) (Γ : constr) : (constr * constr) :=
  Control.once_plus (fun () => Std.unify (Constr.type e) '(@expr _))
    (fun _ => Control.zero (Reify_unsupported "Expected expression to have type [expr]" (Constr.type e)));
  lazy_match! e with
  | @goose_lang.App _ ?e1 ?e2 => let (e1, Γ) := reify e1 Γ in
                                let (e2, Γ) := reify e2 Γ in
                                ('(App $e1 [$e2]), Γ)
  | @goose_lang.Val _ (@to_val _ ?vt ?h ?v) => ('(@Val $vt $h $v), Γ)
  | @goose_lang.Val _ (ref_ty ?t) => ('(@RefTy $t), Γ)
  | @goose_lang.Val _ (load_ty ?t) => ('(@LoadTy $t), Γ)
  | @goose_lang.Val _ (store_ty ?t) => ('(@StoreTy $t), Γ)
  | @goose_lang.Val _ (slice.elem_ref ?t) => ('(@SliceElemRef $t), Γ)
  | @goose_lang.Val _ (slice.literal ?t) => ('(@SliceLiteral $t), Γ)
  | @goose_lang.Val _ (slice.for_range ?t) => ('(@SliceForRange $t), Γ)
  | @goose_lang.Val _ (map.make ?kt ?vt) => ('(@MapMake $kt $vt), Γ)
  | @goose_lang.Val _ (interface.make ?mset) => ('(@InterfaceMake $mset), Γ)
  | @goose_lang.Val _ (?x ?ext) =>
      if (Constr.equal (Constr.type ext) '(ffi_syntax)) then ()
      else Control.zero (Reify_unsupported "expected val's first argument to be an [ffi_syntax]" e);
      let i := match (Constr.Unsafe.kind x) with
               | Constr.Unsafe.Constant c _ =>
                   (List.last (Env.path (Std.ConstRef c)))
               | _ => Control.zero (Reify_unsupported_kind (Constr.Unsafe.kind x))
               end in
      let n := (string_ident.IdentToString.ident_to_string i) in
      let Γ := '(<[$n := ($x grove_op)]> $Γ) in
      ('(Named $n), Γ)
  | @goose_lang.Rec _ ?f ?x ?e => let (e, Γ) := reify e Γ in
                                 ('(Rec $f $x $e), Γ)
  | @goose_lang.Var _ ?x => ('(Var $x), Γ)
  | @goose_lang.BinOp _ ?o ?e1 ?e2 =>
      let (e1, Γ) := reify e1 Γ in
      let (e2, Γ) := reify e2 Γ in
      ('(BinOp $o $e1 $e2), Γ)
  | @goose_lang.UnOp _ ?o ?e =>
      let (e, Γ) := reify e Γ in
      ('(UnOp $o $e), Γ)
  | @goose_lang.If _ ?e0 ?e1 ?e2 =>
      let (e0, Γ) := reify e0 Γ in
      let (e1, Γ) := reify e1 Γ in
      let (e2, Γ) := reify e2 Γ in
      ('(If $e0 $e1 $e2), Γ)
  | @goose_lang.Fst _ ?e => let (e, Γ) := reify e Γ in ('(Fst $e), Γ)
  | _ => Control.zero (Reify_unsupported "" e)
  end
.

Notation e := (
  rec: "newNetworkWithConfigInit" "configFunc" "peers" :=
    exception_do (let: "peers" := (ref_ty sliceT "peers") in
    let: "configFunc" := (ref_ty funcT "configFunc") in
    let: "size" := (ref_ty intT #(default_val w64)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "peers") in
    slice.len "$a0") in
    do:  ("size" <-[intT] "$r0");;;
    let: "peerAddrs" := (ref_ty sliceT #(default_val slice.t)) in
    let: "$r0" := (let: "$a0" := (![intT] "size") in
    idsBySize "$a0") in
    do:  ("peerAddrs" <-[sliceT] "$r0");;;
    let: "npeers" := (ref_ty (mapT uint64T stateMachine) #(default_val loc)) in
    let: "$r0" := (map.make uint64T stateMachine #()) in
    do:  ("npeers" <-[mapT uint64T stateMachine] "$r0");;;
    let: "nstorage" := (ref_ty (mapT uint64T ptrT) #(default_val loc)) in
    let: "$r0" := (map.make uint64T ptrT #()) in
    do:  ("nstorage" <-[mapT uint64T ptrT] "$r0");;;
    do:  (let: "$range" := (![sliceT] "peers") in
    slice.for_range stateMachine "$range" (λ: "j" "p",
      let: "j" := ref_ty uint64T "j" in
      let: "p" := ref_ty stateMachine "p" in
      let: "id" := (ref_ty uint64T #(default_val w64)) in
      let: "$r0" := (![uint64T] (slice.elem_ref uint64T (![sliceT] "peerAddrs") (![intT] "j"))) in
      do:  ("id" <-[uint64T] "$r0");;;
      (if: (![stateMachine] "p") = #interface.nil
      then
        let: "$r0" := (let: "$a0" := ((let: "$sl0" := (let: "$a0" := (![sliceT] "peerAddrs") in
        withPeers "$a0") in
        slice.literal testMemoryStorageOptions ["$sl0"])) in
        newTestMemoryStorage "$a0") in
        do:  (map.insert (![mapT uint64T ptrT] "nstorage") (![uint64T] "id") "$r0");;;
        let: "cfg" := (ref_ty ptrT #(default_val loc)) in
        let: "$r0" := (let: "$a0" := (![uint64T] "id") in
        let: "$a1" := #(W64 10) in
        let: "$a2" := #(W64 1) in
        let: "$a3" := (interface.make MemoryStorage__mset_ptr (goose_lang.Fst (map.get (![mapT uint64T ptrT] "nstorage") (![uint64T] "id")))) in
        newTestConfig "$a0" "$a1" "$a2" "$a3") in
        do:  ("cfg" <-[ptrT] "$r0");;;
        (if: (![funcT] "configFunc") ≠ #func.nil
        then
          do:  (let: "$a0" := (![ptrT] "cfg") in
          (![funcT] "configFunc") "$a0")
        else do:  #());;;
        let: "sm" := (ref_ty ptrT #(default_val loc)) in
        let: "$r0" := (let: "$a0" := (![ptrT] "cfg") in
        newRaft "$a0") in
        do:  ("sm" <-[ptrT] "$r0");;;
        let: "$r0" := (interface.make raft__mset_ptr (![ptrT] "sm")) in
        do:  (map.insert (![mapT uint64T stateMachine] "npeers") (![uint64T] "id") "$r0")
      else
        let: "$r0" := (![stateMachine] "p") in
        do:  (map.insert (![mapT uint64T stateMachine] "npeers") (![uint64T] "id") "$r0"))));;;
    return: (ref_ty network (let: "$peers" := (![mapT uint64T stateMachine] "npeers") in
     let: "$storage" := (![mapT uint64T ptrT] "nstorage") in
     let: "$dropm64" := (map.make connem uint64T #()) in
     let: "$ignorem" := (map.make raftpb.MessageType boolT #()) in
     return: #()
     ))))%E.

Definition x : (t * ctx)%type.
  Time unshelve (let (x, Γ):=(reify 'e '(∅ : ctx)) in
            refine '($x, $Γ));
  try ltac1:(tc_solve).
Defined.

Check eq_refl : (interp x.2 x.1 = e).

End expr.

Module iprop.

Inductive t :=
| heap_points_to (x : loc) (v : w64)
.
Section def.
Context `{!heapGS Σ}.
Definition interp (a : t) : iProp Σ :=
  match a with
  | heap_points_to x v => x ↦ v
  end
.
End def.
End iprop.

Module proof_state.
Record t :=
  mk {
      hyps : list (iprop.t);
      prg : expr
    }.

Section def.
Context `{!heapGS Σ}.
Definition interp (a : t) : Prop :=
  ([∗ list] p ∈ a.(hyps), iprop.interp p) -∗
  WP a.(prg) {{ _, True }}.
End def.
End proof_state.

Section checker_proof.

Axiom checker : val.
Context `{!heapGS Σ}.

(* Axiom own_Expr : ∀ (l : loc) (e : expr), iProp Σ. *)
Axiom own_ProofState : ∀ (l : loc) (e : proof_state.t), iProp Σ.

End checker_proof.
