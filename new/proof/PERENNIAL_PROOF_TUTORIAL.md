# Perennial Proof Tutorial

Quick guide for writing program proofs in Perennial. Every tactic is listed
here; for detailed proof state examples and advanced patterns, use
`/perennial-tactics`.

## Proof Structure

```coq
Section proof.
Context `{hG: !heapGS Σ} {sem : go.Semantics} {package_sem : mypkg.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_MyFunc (x: w64) :
  {{{ is_pkg_init mypkg ∗ ⌜some_precondition x⌝ }}}
    @! mypkg.MyFunc #x
  {{{ (r: w64), RET #r; ⌜some_postcondition r⌝ }}}.
Proof.
  wp_start as "%Hpre".
  wp_auto.
  (* ... proof body ... *)
  wp_end.
Qed.
```

- **Hoare triple**: `{{{ P }}} e {{{ v, RET pat; Q }}}`.
- **Function call**: `@! pkg.Func #arg1 #arg2`; method:
  `l @! (go.PointerType pkg.Struct) @! "Method" #arg`.
- **`#` coercion**: Converts Gallina values (`w64`, `w32`, `w8`, `bool`, `loc`,
  `slice.t`, `()`) to GooseLang values.
- **`is_pkg_init`**: Required in preconditions; `wp_start` handles it
  automatically.

## WP Tactics

| Tactic | Syntax | Use when |
|:--|:--|:--|
| `wp_start` | `wp_start as "ipat"` | Begin proof. Introduces `"HΦ"`, destructs precondition. |
| `wp_auto` | `wp_auto` | Straight-line code (pures, loads, stores, allocs). |
| `wp_apply` | `wp_apply (lem with "[$H]") as "ipat"` | Function/method calls. |
| `wp_if_destruct` | `wp_if_destruct` | Conditionals. Case-splits on boolean. |
| `wp_for` | `wp_for` | Loops. Set up invariant with `iAssert` first. |
| `wp_for_post` | `wp_for_post` | End of loop body (do/continue/break/return). |
| `wp_end` | `wp_end` | End of function/branch. Applies `"HΦ"`, tries `iFrame; word`. |
| `wp_if_join` | `wp_if_join asn` | If-else producing a value. Joins branches. |
| `wp_alloc` | `wp_alloc l as "H"` | Explicit allocation (usually automatic). |
| `wp_load` | `wp_load` | Explicit load (usually automatic). |
| `wp_store` | `wp_store` | Explicit store (usually automatic). |
| `wp_pure` | `wp_pure` / `wp_pures` | Single/repeated pure steps (usually automatic). |
| `wp_call` | `wp_call` | Function application (usually automatic). |
| `wp_bind` | `wp_bind e` | Focus on subexpression (usually automatic). |

Variants: `wp_start_folded` (no unfold), `wp_auto --lc n` (later credits),
`wp_apply ... --no-auto`, `wp_call_lc "Hlc"`.

## Struct Tactics

| Tactic | Syntax | Description |
|:--|:--|:--|
| `iStructNamed` | `iStructNamed "H"` | Split struct into per-field `l.[S.t, "f"] ↦ v`. |
| `iStructNamedPrefix` | `iStructNamedPrefix "H" "pfx"` | Same but prefixes names. |
| `iPersist` | `iPersist "H"` | Move to persistent context (`↦□`). |

## IPM Tactics

For the full Iris proof mode reference, search `new/proof/IRIS_PROOF_MODE.md`
for a tactic.

| Tactic | Description |
|:--|:--|
| `iIntros "ipat"` / `iIntros (x)` | Introduce from goal |
| `iDestruct "H" as "ipat"` / `as (x) "ipat"` | Destruct / existential |
| `iNamed "H"` | Destruct named propositions (`∷` notation) |
| `iNamedSuffix "H" "_sfx"` | `iNamed` with suffix on all names |
| `iApply "H"` / `iApply (lem with "spat")` | Apply wand or lemma |
| `iFrame` / `iFrame "H"` / `iFrame "#∗"` | Cancel hypotheses with goal |
| `iSplitL "H1 H2"` / `iSplitR` | Split `∗` goal |
| `iExists x` | Witness for existential |
| `iPureIntro` | Switch to proving pure `⌜P⌝` |
| `iAssert P with "spat" as "ipat"` | Assert intermediate proposition |
| `iModIntro` | Introduce modality |
| `iMod "H" as "ipat"` | Eliminate fancy update |
| `iInv "H" as "ipat" "Hclose"` | Open an invariant |
| `iCombine "H1 H2" as "H"` | Combine fractional resources |
| `iClear "H"` / `iRename "H1" into "H2"` | Remove / rename hypothesis |
| `iExact "H"` / `iExactEq "H"` | Exact match |

### Intro Patterns

`"[H1 H2]"` (destruct `∗`), `"[H1 | H2]"` (destruct `∨`),
`"(H1 & H2 & H3)"` (nested), `"%H"` (pure → Rocq), `"#H"` (persistent),
`"$"` (frame), `"_"` (discard), `"-"` (clear), `"!>"` (modality),
`">H"` (strip later).

### Specialization Patterns

`"[$]"` (auto-frame all), `"[$H1 H2]"` (auto-frame + explicit),
`"[H1 H2]"` (give specific hypotheses).

## Stdpp / Rocq Tactics

| Tactic | Description |
|:--|:--|
| `done` | Solve trivial goals (combines `trivial`, `assumption`, `reflexivity`, etc.) |
| `naive_solver` | Automated first-order logic and set solver |
| `f_equal` | Congruence: prove `f x = f y` from `x = y` |
| `trans y` | Transitivity: prove `x R z` via `x R y` and `y R z` |
| `inv H` | Inversion on inductive hypothesis |
| `destruct_and` | Recursively destruct all `∧` hypotheses |
| `destruct_or` | Recursively destruct all `∨` hypotheses |
| `case_match` | Case split on a `match` in the goal |
| `case_guard` | Case split on a `guard` in the goal |
| `case_decide` | Case split on a `decide` in the goal |
| `opose proof as pat` | Like `pose proof` but with stdpp intro patterns |
| `odestruct` | Destruct with stdpp intro patterns |
| `ospecialize` | Specialize with stdpp intro patterns |
| `simplify_eq/=` | Simplify equalities and substitute |
| `simplify_option_eq` | Simplify `option` equalities |
| `simplify_map_eq/=` | Simplify map equalities |
| `list_simplifier` | Simplify list operations |
| `set_solver` | Automated solver for set goals |

## Specification Lemmas

**Sync**: `wp_Mutex__Lock`, `wp_Mutex__Unlock`, `init_Mutex`,
`wp_Mutex__TryLock`, `wp_Cond__Wait`, `wp_Cond__Signal`,
`wp_Cond__Broadcast`, `wp_WaitGroup__Add`, `wp_WaitGroup__Done`,
`wp_WaitGroup__Wait`

**Slices**: `wp_slice_literal`, `wp_slice_append`, `wp_load_slice_index`,
`wp_store_slice_index`, `wp_load_slice_elem`, `wp_store_slice_elem`,
`own_slice_len`, `own_slice_wf`

**Maps**: `wp_map_make1`, `wp_map_make2`, `wp_map_insert`, `wp_map_lookup2`,
`wp_map_delete`

**Goroutines**: `std.wp_Spawn`, `wp_JoinHandle__Join`

**Assertions**: `wp_Assert`, `wp_AngelicExit`

## Arithmetic

`word` (machine words), `omega`/`lia` (linear arithmetic), `len` (length
rewrites), `split_and!` (split `∧`).

## Common Proof Patterns

### Simple function
```coq
Proof.
  wp_start as "%H". wp_auto. wp_end. word.
Qed.
```

### Function with pointer arguments
```coq
Proof.
  wp_start as "[Hx Hy]". wp_auto. iApply "HΦ". iFrame.
Qed.
```

### Loop with invariant
```coq
  wp_start as "%Hpre". wp_auto.
  iAssert (∃ (i acc: w64),
    "i" ∷ i_ptr ↦ i ∗
    "acc" ∷ acc_ptr ↦ acc ∗
    "%Hinv" ∷ ⌜invariant_holds i acc⌝
  )%I with "[$i $acc]" as "IH".
  { iPureIntro. (* prove initial *) ... }
  wp_for; iNamed "IH"; wp_auto.
  - (* body *) wp_for_post. iFrame. iPureIntro. ...
  - (* exit *) wp_end. ...
```

### Struct allocation
```coq
  wp_alloc l as "Hl".
  iStructNamed "Hl". simpl.
  iPersist "immutable_field".
```

### Named propositions (∷)
```coq
Definition my_inv l : iProp Σ :=
  ∃ (x: w64),
    "Hx" ∷ l ↦ x ∗
    "%Hbound" ∷ ⌜uint.Z x < 100⌝.
(* iNamed "Hinv" gives: "Hx": l ↦ x, Hbound: uint.Z x < 100 *)
```
