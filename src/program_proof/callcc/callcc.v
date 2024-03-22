From Perennial.program_proof Require Import grove_prelude.

Section proof.

Axiom call_cc : goose_lang.val.
Axiom throw: goose_lang.val.
Axiom cont : (list ectx_item) -> goose_lang.val.

Axiom nclwp : ∀ { PROP EXPR VAL A : Type } `{Wp PROP EXPR VAL A}, A → coPset → EXPR → (VAL → PROP) → PROP.

Notation "'NCLWP' e {{ Φ } }" := (nclwp NotStuck top e Φ).

Context `{!heapGS Σ}.

Axiom nclwp_bind :
  ∀ K (e:goose_lang.expr) Φ,
  WP e {{ λ v, NCLWP (fill' K (Val v)) {{ Φ }} }} -∗
  NCLWP (fill K e) {{ Φ }}
.

Axiom nclwp_call_cc :
  ∀ K Φ f,
  NCLWP (fill K (App f (cont K))) {{ Φ }} -∗
  NCLWP (fill K (App call_cc f)) {{ Φ }}
.

Axiom nclwp_throw :
  ∀ K Kt (v:goose_lang.val) Φ,
  NCLWP (fill Kt (Val v)) {{ Φ }} -∗
  NCLWP (fill K (App (App throw (Val v)) (cont Kt))) {{ Φ }}
.

Notation "'return:' x" := (throw x "retK") (at level 20).

Definition earlyReturnTest: val :=
  rec: "earlyReturnTest" "x" :=
    let: "x" := call_cc (λ: "retK",
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      return: #()
    )
    ) in
    "x"
.

Definition earlyReturnTest2: expr :=
    call_cc (λ: "retK",
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      return: #()
    )
    )%E
.

Lemma wp_earlyReturnTest :
  ∀ Φ,
  True -∗
  (True -∗ Φ #()) -∗
  NCLWP earlyReturnTest2 {{ Φ }}
.
Proof.
  iIntros (?) "_ HΦ".
  rewrite /earlyReturnTest2.
  Print reshape_expr.
  replace (call_cc (λ: "retK", for: (λ: <>, #true) ; (λ: <>, Skip) := λ: <>, throw #() "retK")%E)
    with
    (fill [] (call_cc (λ: "retK", for: (λ: <>, #true) ; (λ: <>, Skip) := λ: <>, throw #() "retK")%E))
    by done.
  iApply nclwp_call_cc.
  simpl.
  Locate "let:".

  lazymatch goal with
  | |- envs_entails _ (nclwp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' => iApply nclwp_bind K)
  | _ => fail "not a NCLWP"
  end
  .
  Search reshape_expr.
  iApply nclwp_call_cc.

  wp_rec.
  iApply (nclwp_bind _ ).

End proof.
