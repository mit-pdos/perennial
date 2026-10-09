# Perennial Proof Reference (Lean)

Detailed reference for the GooseLang/Go proof tactics, the
Perennial-specific proof mode helpers, and the main specification lemmas. For a
guided introduction see [`PERENNIAL_PROOF_TUTORIAL.md`](PERENNIAL_PROOF_TUTORIAL.md);
for the generic Iris proof mode see [`IRIS_PROOF_MODE.md`](IRIS_PROOF_MODE.md).
Lean blocks are copied from [`TutorialExamples.lean`](TutorialExamples.lean),
which is checked with `lake env lean docs/TutorialExamples.lean`.

Source locations are given as files plus the tactic or lemma name (grep for
`"wp_auto"`, `theorem wp_mapInsert`, ...). The docstrings in those files are
authoritative.

---

## 1. Specifications

### Texan triples

```
{{ P }} e {{ (x : T) (y : U), RET v; Q }}
{{ P }} e @ s; E {{ RET v; Q }}          -- with stuckness and mask
```

is notation (from iris-lean's `Iris/BI/WeakestPre.lean`) for

```
⊢ ∀ Φ, P -∗ ▷ (∀ x y, Q -∗ Φ v) -∗ WP e {{ Φ }}
```

Inside `iprop(...)` (e.g. as an argument of another spec) a triple means
`□ (∀ Φ, ...)`, so a triple is persistent. Some proofs state specs directly in
the wand form, which `wp_start` handles too (`Perennial/Proof/sync_proof/sema.lean`):

```
⊢ ∀ Φ : val → IProp GF, iprop(isPkgInit pkg_id.sync ∗ isSema sema γ N) -∗
    (|={⊤ \ ↑N,∅}=> ...) -∗ WP (App (Val (@! runtime_Semacquire)) (Val #sema)) {{ Φ }}
```

### Expressions

| Lean | Meaning |
|:--|:--|
| `@! F` | `#(functions F [])`, the function `F` (a `GoString` like `go!"sort.Search"`) |
| `r @!! T @!! go!"m"` | `#(methods T go!"m" #r)`, method `m` of `r : T` |
| `(App (App (Val f) (Val #x)) (Val #y))` | the call `f x y` |
| `#x` | `intoVal x`: Lean value to GooseLang `val` |
| `PairV #a #b` | multiple return values `(a, b)` |
| `gl(let: "x" := e1 in e2)` | GooseLang term syntax (see `Perennial/GooseLang/Notation.lean`) |
| `![t] e`, `e1 <-[t] e2` | typed load and store |

### Points-to and resources

| Notation | Meaning | File |
|:--|:--|:--|
| `l ↦ v`, `l ↦{dq} v`, `l ↦□ v` | typed points-to (`typedPointsto l v dq`) | `Golang/Theory/PostLifting.lean` |
| `l.[S, go!"f"]` | address of field `f` of the struct at `l` | `Golang/Defn/PostLang.lean` |
| `s ↦* vs`, `s ↦*{dq} vs` | slice points-to (`ownSlice`) | `Golang/Theory/Slice.lean` |
| `ownSliceCap V s dq` | ownership of the capacity beyond the length | `Golang/Theory/Slice.lean` |
| `m ↦$ mv`, `m ↦${dq} mv`, `m ↦$□ mv` | map points-to (`ownMap`), `mv : gmap K V` | `Golang/Theory/Map.lean` |
| `isPkgInit (PROP := IProp GF) pkg` | package `pkg` is initialized | `Golang/Theory/Pkg.lean` |
| `"H" ∷ P` | named proposition (for `iNamed`) | `Helpers/NamedProps.lean` |

### Words, maps, lists

`w64 = BitVec 64` etc.; `W64 3` is a literal; `uint.Z x = (x.toNat : Int)`,
`sint.Z x = x.toInt`, `uint.nat`, `sint.nat`. Maps are `Perennial.gmap K V`
(`m !! k`, `<[k := v]> m`, `{[k := v]}`, `GMap.delete k m`); on lists, `l !! i`
is `l[i]?` and `<[i := v]> l` is `l.set i v`. `go!"abc"` is a `GoString` (a
`List w8`). See `README.md`.

### Sealing

Sealed (opaque) definitions are written

```
def isMutexDef (m : Loc) (R : IProp GF) : IProp GF := isLock m R
@[irreducible] def isMutex (m : Loc) (R : IProp GF) : IProp GF := isMutexDef m R
theorem isMutex_unseal : @isMutex = @isMutexDef := by funext; with_unfolding_all rfl
```

(`Perennial/Proof/sync_proof/mutex.lean`) and unfolded in proofs with
`simp only [isMutex_unseal, isMutexDef]`. Typeclass facts (`Persistent`,
`Timeless`) are proved by unsealing and `infer_instance`.

---

## 2. WP tactics

All of these work on an Iris proof mode goal whose conclusion is a GooseLang
`WP`. They fail (never leave a `sorry`) when an argument does not elaborate.

### `wp_start`, `wp_start as pat`, `wp_start_folded as pat`

`Perennial/Golang/Theory/Auto.lean`. Begin the proof of a Texan triple (or of
the wand form above):

1. `iintro %Φ Hpre HΦ` (after an `imodintro` if the goal is `□ ...`);
2. move the `isPkgInit` conjuncts at the front of `Hpre` to the intuitionistic
   context, named `Hpkg`, `Hpkg2`, ... (used by `iPkgInit`);
3. destruct the rest with `pat` (an iris-lean cases pattern), or keep it as
   `Hpre`;
4. `wp_start` only: unfold the called function (`wp_func_call`) or method
   (`wp_method_call`) and take the call step (`wp_call`).

Use `wp_start_folded` to prove a spec of a closure or a function value that
should not be unfolded (e.g. `predImplements_adapt` in
`Perennial/Proof/sort_proof/search.lean`).

Proof state of `S.wp_writeB'` before `wp_start as Hs`:

```
⊢ ⊢
    ∀ Φ,
      isPkgInit pkg ∗ s ↦ v -∗
        ▷ (s ↦ { a' := v.a', b' := two, c' := v.c' } -∗ Φ #()) -∗
          WP (#(methods S.PointerType [119#8, 114#8, 105#8, 116#8, 101#8, 66#8] #s) #two) {{ Φ }}
```

after it:

```
  ∗HΦ : s ↦ { a' := v.a', b' := two, c' := v.c' } -∗ Φ #()
  □Hpkg : isPkgInit pkg
  ∗Hs : s ↦ v
  ⊢
  WP
    (exceptionDo
      (let: "s" := (GoAlloc S.PointerType) #s in
        let: "two" := (GoAlloc TwoInts) #two in
          (exceptionSeq (Lam BAnon (return: #())))
            (Let (BNamed "$r0") (![TwoInts] "two")
              (do: (StructFieldRef S [98#8]) ![S.PointerType] "s" <-[TwoInts] "$r0"))))
    {{ Φ }}
```

and after `wp_auto`:

```
  ∗HΦ : s ↦ { a' := v.a', b' := two, c' := v.c' } -∗ Φ #()
  □Hpkg : isPkgInit pkg
  ∗Hs : s ↦ { a' := v.a', b' := two, c' := v.c' }
  ⊢ Φ #()
```

(`GoString` literals are displayed as byte lists: `[98#8]` is `go!"b"`.)

### `wp_func_call`, `wp_method_call`

`Auto.lean`. Rewrite the next `#(functions f ts)` (resp. `#(methods t m v)`)
with its `FuncUnfold` (resp. `MethodUnfold`) instance from the package's
`Assumptions`. `wp_func_call` only rewrites the WP expression, choosing the
innermost call in evaluation position (else the first occurrence). Follow with
`wp_call`. Use them to step into a function that has no spec.

### `wp_auto`, `wp_auto_lc n`

`Auto.lean`. Repeatedly: pure steps (`wp_pures`), loads (`wp_load`), stores
(`wp_store`) and allocations bound by `let:` (`wp_alloc_auto`, naming Go
variable `x`'s cell `x_ptr` and its points-to `x`); when the expression becomes
a value, continue in the postcondition. At the end it clears the points-to
facts of local variables that no longer occur. **Fails if no progress is
made.** `wp_auto_lc n` also produces later credits `Hlc1 ... Hlcn` from the
first `n` pure steps (fails if there are fewer).

It stops at: calls of functions (use `wp_apply`, or `wp_func_call; wp_call`),
`if:` on a non-literal condition (`wp_if_destruct`), loops (`wp_for`),
and anonymous allocations (`wp_alloc`, `wp_alloc_anon`). With `goose.wp.extras`
(the default) it also stores function literals, unfolds blocking package
constants and steps into calls of implementation constants `Foo.impl v` (as left
by `wp_method_call`/`wp_func_call`). It only clears the points-to facts of Go
local variables (`x_ptr`), not of other locations.

### `wp_pures`, `wp_pure [pat]`, `wp_pure_lc H`, `wp_expr_simp`

`Perennial/Golang/Theory/ProofMode.lean`. `wp_pures` takes all pure steps
(`PureWp` instances: beta, `if:` on literals, pair projections, deterministic
Go instructions, `exceptionSeq`, ...) and simplifies substitutions; never
fails. An array literal `[n]T{v₀, v₁, ...}` whose elements are all values of the
element type `T` becomes `#(array.mk n [v₀, v₁, ...])` (padded with zero values
up to `n`) in one step (`pure_wp_array_lit`, `Golang/Theory/ArrayLit.lean`). `wp_pure` takes one step, leaving unsolved side conditions as goals;
`wp_pure (if: _ then _ else _)` steps a redex matching a GooseLang pattern.
`wp_pure_lc H` keeps the later credit as `H : £ 1`. `wp_expr_simp` only
simplifies the expression.

### `wp_call`, `wp_call_lc H`

`ProofMode.lean`. Beta-reduce the application `fv v` at the head, where `fv`
unfolds to a `rec:`/`λ:` (e.g. a `F.impl` constant), then `wp_pures`.

### `wp_bind [pat]`

`ProofMode.lean`. `wp_bind e` focuses `WP K[e'] {{ Φ }}` on the outermost
subexpression `e'` in evaluation position matching the pattern `e` (holes `_`),
giving `WP e' {{ v, WP K[v] {{ Φ }} }}`; e.g. `wp_bind (CmpXchg _ _ _)` before
opening an invariant. Without argument: the next "interesting" operation. `wp_apply` binds automatically.

### `wp_apply lem $$ spats as pats`

`Auto.lean`. Options, written right after `wp_apply`: `wp_apply +noauto lem ...`
(introduce `pats` but do not run `wp_auto`: the goal is `WP K[v] {{ Φ }}` right
after the call, e.g. to `imod` an update the spec returns; to eliminate an update
in the spec's own postcondition first `iapply wp_fupd`), `wp_apply (lc := n) lem
...` (the final `wp_auto` produces `n` credits `Hlc1 ... Hlcn`, and fails if there
are fewer pure steps). `with` is a synonym of `as`.

1. Apply `lem` (a Lean lemma, possibly with explicit arguments, or an Iris
   hypothesis) to the first subexpression in evaluation position where it fits,
   binding the context. If it does not fit, run
   `wp_pures` and try again.
2. Strip a leading `▷` from the premise goals and close trivial ones; solve
   `isPkgInit` premises (`iPkgInit`); close pure side conditions without
   metavariables (e.g. a bounds check `0 ≤ 0`) with `decide` or `word`. If the
   spec does not apply because an argument is a function literal `RecV ..` where
   the spec expects a `GoFunc`, it is retried after `wp_func_lits`.
3. Introduce `pats` (iris-lean intro patterns) in the continuation (the
   introduced hypotheses are simplified with the WP simp set, so that they agree
   with the expression, e.g. `W64 (go.arrayLiteralSize [..])`) and run
   `wp_auto` on it.

Premise goals created by `[...]` spec patterns come before the continuation:

```
wp_apply wp_load_slice_index s (sint.Z i) vs _ x Hi.1 $$ [Hs] with Hs
· iframe; ipureintro; exact Hx_lookup        -- the precondition
-- continuation, with `Hs` reintroduced
```

Specialization patterns are iris-lean's (see `IRIS_PROOF_MODE.md`) except the
`[H] as name` form. To pass Lean arguments to an Iris hypothesis `IH`, use pure
patterns: `wp_apply IH $$ %x %y [H]`. If the continuation still contains
metavariables (e.g. an output not yet determined), `as` patterns may not be
introduced; then `iintro` by hand (see `wp_wrapUnwrapInt` in
`Perennial/Proof/.../examples/unittest.lean`). If the spec closes the goal, use
`wp_apply_core`.

### `wp_apply_core lem $$ spats`

`ProofMode.lean`. Step 1 only: no `isPkgInit` solving, no introduction, no
automation. The last goal is the continuation `∀ x, Q -∗ WP K[v] {{ Φ }}`.

### `wp_load`, `wp_store`, `wp_alloc l as H`, `wp_alloc_auto`

`Perennial/Golang/Theory/Mem.lean`. `wp_load` performs `![t] #l` using a
hypothesis `l ↦{dq} v` or one from which it can be accessed (an `Access`
instance, e.g. the struct points-to for a field address). `wp_store` needs full
ownership and updates the hypothesis. `wp_alloc l as H` introduces `l` and
`H : l ↦ v`. `wp_alloc_auto` names a `let:`-bound allocation after its
variable, and otherwise does an anonymous allocation with inaccessible names.

### `wp_if_destruct`

`Auto.lean`. Case split on the condition of the `if:` at the head of the
expression — a `decide P` or a Boolean variable `#b` — then `wp_pures`,
`cleanup_bool_decide` and `wp_auto`. For `decide P` the case hypothesis is
`Hif : P` / `Hif : ¬P` (accessible). An equation `x = e` (or `e = x`) between a
variable `x` and a term `e` that is not a variable (e.g. `x = W64 0`) is
substituted; an equation between two variables (`i = n`) is kept as `Hif` (use
`subst Hif` if wanted). For `#b` it does `cases b`. If there is no head `if:`, it falls
back to the first `decide` in the expression, then in the goal.

### `wp_join R`, `wp_join_done`

`Perennial/Golang/Theory/Join.lean`. Prove the code after a case split once.
After `wp_if_destruct` (or `cases s`, `by_cases`, ...) every goal contains the
rest of the function and re-verifies it; `wp_join R` instead binds the head
`if:` (or another subexpression, see `at`), asks for a common intermediate
assertion `R : IProp GF` (may be `∃ x, ...`), and leaves

1. the cases of the bound expression only, with postcondition
   `fun v => ⌜v = v₀⌝ ∗ R` (`v₀ = executeVal` for an `if` statement that falls
   through; `(v := #false)` for an expression such as a `&&`);
2. the continuation `R -∗ WP K[v₀] {{ Φ }}`, proved once.

```
wp_join R with [H1 H2] as pats       -- H1 H2 go to the cases ([-HΦ]: all but HΦ)
wp_join with [v w delta]             -- frame mode: R := the listed hypotheses, unchanged
wp_join (v := #false) R ...          -- the join value
wp_join (Q := fun v => ...) ...      -- general postcondition (continuation ∀ v, Q v -∗ ...)
wp_join R at (pat) ...               -- bind the outermost match of a goose pattern
wp_join R at next ... / at next 3    -- bind the next statement / next 3 statements
```

With the default binding it runs `wp_if_destruct` on the `if:` and then
`wp_join_done` in every case that reached the join value: `wp_join_done` turns
`⌜v₀ = v₀⌝ ∗ R` (or `True ∗ R`) into `R` and closes it when `iframe` does, so
the remaining case goals are those that need work (`iexists ..; iframe;
ipureintro; ...`, or more code ending in `wp_join_done`). With `at`, no case
split is done: case split yourself inside the bound goal — this is how a case
split on ghost or pure state (`cases s`, `rcases`) is joined before a common
tail. With `as pats` (or in frame mode) the continuation introduces `R` and
runs `wp_auto`. Statements are left-nested (`(s₁ ;;; s₂) ;;; s₃`), so `at next n`
binds `s₁ … sₙ`; a declaration `x := e` scopes over the rest of its block and
ends the statements that can be bound.

Example (`docs/TutorialExamples.lean`, `wp_ifJoinDemo'`): the first `if` of
`ifJoinDemo` is joined at "`arr` is some slice", so the second `if` is proved
once:

```
wp_join iprop(∃ (sl : GoSlice) (xs : List w64),
    arr_ptr ↦ sl ∗ sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1))
  with [arr Hz Hzcap] as ⟨%sl1, %xs, arr, Hz, Hzcap⟩
· append_lit          -- `arg1 = true`; the `false` case was closed by `iframe`
  wp_join_done
wp_if_destruct        -- the rest of the function, once
...
```

Other uses: `WaitGroup.wp_Add` (frame mode, the `w != 0 && delta > 0 && ...`
panic checks), `wp_siftDownCmpFunc` (existential witness `c` from three cases).
Where to join: after a case split whose cases fall through to the same code
(`if` statements without `return`, `&&`/`||` conditions, `switch` cases that
do not return). It does not help when every case runs its own code to the end
of the function (e.g. a `switch` whose cases all `return`, as in the channel
model's `TryReceive`): there is no common tail.
`wp_if_join asn with [pat]` (`Perennial/Golang/Theory/IfJoin.lean`) takes a
general `asn : val → IProp`; prefer `wp_join R` when it applies.

### `wp_for`, `wp_for HI`, `wp_for_post`

`Auto.lean`, `Perennial/Golang/Theory/Loop.lean`. `wp_for` binds the `doFor`
loop at the head and applies `wp_for` with the **whole spatial context** as the
invariant (`iNamedAccu`), then `wp_auto` and `cleanup_bool_decide`. The goal is
then

```
if decide (cond) = true then WP body {{ forPostcondition ... }} else Φ executeVal
```

so the next step is usually `wp_if_destruct`. `wp_for HI` also `iNamed`s `HI`,
the hypothesis holding your loop invariant (`ihave HI : (∃ i, ...) $$ [..]`).
Hypotheses you do not want in the invariant must be cleared or framed away
before `wp_for`.

`wp_for_post` proves a `forPostcondition` goal at the end of an iteration with
`wp_for_post_do` (fall-through: then the post statement runs, e.g. `i++`),
`wp_for_post_continue`, `wp_for_post_break` or `wp_for_post_return`, then runs
`wp_auto`. After it, re-establish the invariant (`iframe; iexists ...; ...`).

Range loops are `for:` loops too: `slice.forRange`, and for arrays
`array.forRange n t` (over an array value), `array.forRangePtr n t` (over a
pointer to an array) and `array.forRangeIndex n` (no value variable), unfold to
their `for:` loop by `wp_auto` (`Theory/Array.lean`), whose counter is an extra
`int` points-to in the context. A `break` in a case body of a `switch`, type
switch or `select` ends that statement: Goose wraps such a statement in
`catchBreak`, which `wp_auto` steps through (`break:` becomes `do:`; the
`pure_catch_break_*` instances in `Theory/Loop.lean`).

Each iteration of a loop has its own iteration variables. Goose shares one
variable among the iterations unless that is observable, that is, unless the
loop captures the variable in a function literal or takes its address (`&x`,
slicing an array, a pointer-receiver method call). A range loop then allocates
its variables in the body, so each iteration has a fresh points-to. A
three-clause loop keeps the current iteration's variable `x` in a cell
`«$iter_x»` (a pointer to a pointer), which the condition, body and post
statement read; before the post statement it allocates the next iteration's
copy, so the invariant quantifies over the current pointer (`∃ p, «$iter_x_ptr»
↦ p ∗ p ↦ v`), and earlier iterations' variables stay in the context
(`wp_testLoopVarCapture`, `semantics_proof/loopvars.lean`).

Proof state of `wp_intSliceLoop'` after `wp_for HI` (abbreviated):

```
Hlen : vs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len
i : w64
Hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len
⊢
  ∗HΦ : s ↦* vs -∗ Φ #(sum_w64 vs)
  ∗Hs : s ↦* vs
  ∗xs : xs_ptr ↦ s
  ∗i : i_ptr ↦ i
  ∗sum : sum_ptr ↦ sum_w64 (List.take (sint.nat i) vs)
  ⊢
  if decide (sint.Z i < sint.Z s.len) = true then
    WP (... loop body ...)
      {{ forPostcondition Stuckness.NotStuck ⊤ (λ: <>, do: #i_ptr <-[go.int] ...)
            iprop("HΦ" ∷ ... ∗ "Hs" ∷ s ↦* vs ∗ "xs" ∷ xs_ptr ↦ s ∗ "HI" ∷ ∃ i, ...)
            fun v => WP (exceptionDo (v ;;; return: ![go.uint64] #sum_ptr)) {{ Φ }} }}
  else ...
```

### `wp_end`

`Auto.lean`. `wp_pures`, `imodintro`s, then `iapply HΦ` (or `HPost`), then try
`iframe; done`, `itrivial`, `ipureintro; trivial`. If applying `HΦ` fails, its
error is reported; otherwise remaining goals are left to you (often
`ipureintro; word`).

### Options

| Option | Default | Effect |
|:--|:--|:--|
| `goose.wp.extras` | `true` | `wp_auto` stores function literals as `#(func.mk ..)` and unfolds blocking package constants; `wp_pures`/`wp_auto` reduce `match`es on constructors and projections of constructors (`(zero_val S).f'`, `(interface.mk t v).v`, `zero_val` of base types), stop at slice composite literals (the list of `[]T{a, b}` comes out as `[a, b]`) and use the `goose_wp_simp_extra` simp set (`decide` with classical instances, `#a = #b` for injective `intoVal`, `go.GoType` equalities, `ite` on closed conditions, ...); `wp_func_call` finds `FuncUnfold f (List.replicate n t)` for `[t, .., t]` |
| `goose.wp.fvAnnot` | `true` | `wp_auto` annotates the continuations of the function with their free variables (`fvClosed`, removed before the goal is shown), so that substituting a `let:`-bound temporary is proved in constant size instead of by a proof of the size of the rest of the function (linear instead of quadratic kernel time in the length of a function) |
| `goose.wp.letRun` | `2` | `wp_pures`/`wp_auto` step through a run of at least this many `let:`s (or `;;`s) of values at once, extending an environment (`substEnv`, `Golang/Theory/SubstEnv.lean`) in constant size per `let:` and substituting it into the body after the run once (instead of substituting each `let:` into the rest of the run); `0` disables this |
| `goose.wp.unfoldSliceLiterals` | `false` | let `wp_pures` step slice composite literals instead of stopping (normally use `wp_slice_literal`) |

Use them as `set_option goose.wp.extras false in` before a declaration (to get
the old behaviour).

---

## 3. Perennial proof mode helpers

| Tactic | Description | File |
|:--|:--|:--|
| `iNamed H` | destruct existentials and the `∗`-spine of named conjuncts of `H`, naming them; unfolds the head definition unless `@[irreducible]` (but never an `if`/`match`: case split first); works under a `▷` (e.g. after `iinv`; the conjuncts keep the `▷`); `"*"` destructs a conjunct recursively; the unnamed rest keeps the name `H` unless a conjunct is called `H` (then `Hrest`) | `Helpers/NamedProps.lean` |
| `iNamed 1` | introduce the premise of a wand and `iNamed` it | same |
| `iNamedPrefix H "pre"`, `iNamedSuffix H "suf"` | `iNamed`, renaming | same |
| `iNamedDestruct H` | `iNamed` without destructing existentials | same |
| `iNamedAccu` | solve a metavariable goal with the named spatial context | same |
| `iFrameNamed` | frame each named conjunct with the hypothesis of the same name | same |
| `iExactEq H` | prove `Q` from `H : P`, leaving `P = Q` | same |
| `iStructNamed H` | split `H : l ↦{dq} (v : S)` into field points-tos named after the fields | `Golang/Theory/PostLifting.lean` |
| `iStructNamedPrefix H "p"`, `iStructNamedSuffix H "s"` | with renaming | same |
| `ipersist H` | turn `H : l ↦ v` (or anything with `UpdateIntoPersistently`) into persistent `H : l ↦□ v`; needs an update in the goal (a WP is fine) | `GooseLang/IPersist.lean` |
| `iPkgInit` | solve an `isPkgInit` goal or the `isPkgInit` conjuncts at the front of a `∗` goal from the intuitionistic context | `Golang/Theory/Pkg.lean` |
| `solve_pkg_init` | solve one `isPkgInit pkg` goal (also through the dependencies of other packages' `isPkgInit`) | same |
| `isPkgInit_unfold`, `is_pkg_init_finish` | unfold `isPkgInit` in the goal; finish a `wp_initialize'` proof | `Golang/Theory/Auto.lean` |
| `cleanup_bool_decide` | simplify `if decide (#(decide P) = #true)` and friends | `Golang/Theory/Auto.lean` |
| `solve_ndisj` | prove namespace mask conditions (`↑(N.@"a") ⊆ ⊤ ∖ ↑(N.@"b")`, `⊤ ∖ ↑N ⊆ ⊤ ∖ ↑(N.@x)`, `↑(N.@"a") ## ↑(N.@"b")`, using mask hypotheses); `iinv` discharges its mask side condition with it | `Golang/Theory/IrisTactics.lean` |
| `iinv H with pat Hclose` | iris-lean's `iinv`, re-implemented: mask side conditions by `solve_ndisj`, no `simp [*]` (no deep recursion with word facts), an error (suggesting `wp_bind`) on a non-atomic WP | same |
| `wp_func_lits` | rewrite function literal values `RecV f x e` in the WP expression to `#(func.mk f x e)` (`wp_apply` tries it when a spec does not apply, e.g. `wp_mapInsert` of a closure) | `Golang/Theory/Auto.lean` |
| `wp_alloc_anon` | an allocation not bound by `let:` (e.g. `&S{..}`), inaccessible names | `Golang/Theory/Mem.lean` |
| `wp_if_angelic` | for the head `if: #(decide P) then e else AngelicExit #()`: continue with `e` under a hypothesis `P` (introduce it with `iintro %H`) | `Golang/Theory/Auto.lean` |
| `no_sorry tac` | run `tac` without error recovery and fail if the proof would contain `sorry` (used by `word`, `list_solver`) | `Std/Word/Automation.lean` |
| `word_lit_simp` | evaluate `sint.Z`/`uint.Z`/`sint.nat`/`uint.nat` of word literals everywhere (`sint.Z (W64 7)` to `7`), keeping `W64 n` (a bare `simp` turns `W64 n` into `n#64`, which then no longer matches `W64 n` for `iframe`) | `Golang/Theory/TacticsSimp.lean` |
| `word`, `word_simp`, `len`, `list_elem l i as x` | arithmetic and lists (below) | `Std/Word/Automation.lean`, `Std/ListLen.lean` |

The generated files also use `solve_into_val_typed_struct` (one `wp_auto` pass, stepping
the field checks `if: .. else AngelicExit #()`), `solve_pointsto_access_struct` (linear in the
number of fields: the field is focused in the unfolded struct points-to, no framing),
`solve_typed_pointsto_dfractional`, `solve_typed_pointsto_timeless`,
`solve_typed_pointsto_agree` (instances for structs) and `solve_atomic_wps`.

### Arithmetic

```lean
example (x : w64) (h : uint.Z x < 10) : uint.Z (x + W64 1) = uint.Z x + 1 := by word
example (x y : w64) (h : sint.Z x ≤ sint.Z y) (h' : 0 ≤ sint.Z x) : 0 ≤ sint.Z y := by word
example (l : List Nat) (n : Nat) (h : n ≤ l.length) : (l.take n ++ [3]).length = n + 1 := by len
example (l : List w64) (h : 2 < l.length) : True := by
  list_elem l 2 as y          -- `y : w64` and `Hy_lookup : l[2]? = some y`
  trivial
```

* `word`: unfolds `uint.Z`, `sint.Z`, `W64` and `@[word_unfold]` definitions,
  adds `toInt`/`toNat` relations, rewrites `toNat` of BitVec operations to `Nat`
  arithmetic modulo `2^n`, and calls `omega`; then tries `bv_decide`. Closes the
  goal or fails. Good at linear arithmetic, treats products as atoms.
* `word_simp`: non-terminal; rewrites `uint.Z` of operations to `Int`
  arithmetic, discharging no-overflow side conditions with `word`.
* `len`: `simp only [len, uint.nat, uint.Z]` (the `@[len]` set) on hypotheses and
  goals that do not mention Iris entailments, then `word`; never fails. Extend
  with `attribute [len] foo_length`.
* `list_elem l i as x`: `x` and `Hx_lookup : l[i]? = some x`, the bound proved by
  `len`; `i : Nat` (write `sint.nat i` for a word index).

---

## 4. Specification lemmas

Specs take `isPkgInit` of their package; `wp_apply` discharges it.

### Memory (`Golang/Theory/Mem.lean`, `PostLifting.lean`)

| Lemma | |
|:--|:--|
| `wp_alloc`, `wp_store`, `IntoValTyped.wp_load` | typed allocation/store/load (used by the tactics; `wp_load` is not exported, write `IntoValTyped.wp_load`) |
| `wp_cmpxchg_suc`, `wp_cmpxchg_fail`, `wp_atomic_load`, `wp_atomic_swap` | atomic operations on typed points-to (`AtomicWps`) |
| `typedPointsto_split` | struct points-to to fields (used by `iStructNamed`) |
| `wp_AngelicExit` | unreachable code |
| `wp_GoPrealloc`, `wp_GlobalAlloc` | low level allocation |

### Slices (`Golang/Theory/Slice.lean`)

| Lemma | |
|:--|:--|
| `ownSlice_len` | `s ↦*{dq} vs ⊢ ⌜vs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝` |
| `ownSlice_wf`, `ownSliceCap_wf` | `0 ≤ len ≤ cap` |
| `ownSlice_nil`, `ownSlice_empty`, `ownSlice_agree`, `ownSlice_persist` | |
| `ownSlice_split`, `ownSlice_combine`, `ownSlice_slice`, `ownSlice_elem_acc` | splitting and element access |
| `wp_load_slice_index s i vs dq v (hpos : 0 ≤ i)` | `{{ s ↦*{dq} vs ∗ ⌜vs[i.toNat]? = some v⌝ }} ![t] #(sliceIndexRef V i s) {{ RET #v; s ↦*{dq} vs }}` |
| `wp_store_slice_index` | `{{ s ↦* vs ∗ ⌜0 ≤ i ∧ i < vs.length⌝ }} ... {{ RET #(); s ↦* vs.set i.toNat v' }}` |
| `wp_slice_make2`, `wp_slice_make3` | `make([]T, n)`, `make([]T, n, c)` |
| `wp_slice_append`, `wp_slice_copy`, `wp_slice_clear` | `append`, `copy`, `clear` |
| `wp_slice_literal` | `[]T{...}` (`wp_auto` stops before it) |

### Maps (`Golang/Theory/Map.lean`)

| Lemma | |
|:--|:--|
| `wp_map_make1`, `wp_map_make2` | `make(map[K]V)`; give `(K := ..) (V := ..)` |
| `wp_mapInsert` | `{{ l ↦$ m }} ... {{ RET #(); l ↦$ <[k := v]> m }}` (needs `SafeMapKey`) |
| `wp_map_lookup1`, `wp_map_lookup2` | `m[k]`, `v, ok := m[k]`; the result is `(m !! k).getD (zero_val V)` (and `decide (m !! k).isSome`) |
| `wp_mapDelete`, `wp_map_clear`, `wp_map_for_range` | |

Simplify lookups with `lookup_insert_eq`, `lookup_insert_ne`, `GMap.insert_empty`.

### Control (`Golang/Theory/Loop.lean`, `Defer.lean`, `Assume.lean`, `GooseLang/Lifting.lean`)

| Lemma | |
|:--|:--|
| `wp_for`, `wp_for_post_do/continue/break/return` | loops (used by the tactics) |
| `wp_with_defer` | functions with `defer` (introduce `%defer Hdefer`, see `Once.wp_doSlow`) |
| `wp_fork` | `go` statements: `▷ WP e {{ True }} -∗ ▷ Φ #() -∗ WP (Fork e) {{ Φ }}` |
| `wp_assume`, `wp_sumAssumeNoOverflow`, ... | `primitive.Assume*` |
| `wp_package_init` | package initialization (in `wp_initialize'`) |

### `sync` (`Perennial/Proof/sync_proof/*.lean`, `Perennial/Proof/sync/atomic.lean`)

| Lemma | |
|:--|:--|
| `sync.init_Mutex R E m` | `m ↦ zero_val Mutex -∗ ▷ R ={E}=∗ isMutex m R` |
| `sync.Mutex.wp_Lock`, `Mutex.wp_Unlock`, `Mutex.wp_TryLock` | `Lock`: `{{ isMutex m R }} {{ ownMutex m ∗ R }}`; `Unlock` takes `ownMutex m ∗ ▷ R` |
| `sync.Mutex_is_Locker` | a `*Mutex` implements `Locker` |
| `sync.wp_NewCond`, `Cond.wp_Wait`, `Cond.wp_Signal`, `Cond.wp_Broadcast` | condition variables |
| `sync.init_Once`, `Once.wp_Do` | `sync.Once` |
| `sync.wp_RWMutex__*` | `RWMutex` |
| `sync.wp_runtime_Semacquire`, `wp_runtime_Semrelease` | runtime semaphores (atomic-update style specs) |
| `sync.atomic.wp_*` (`Uint64.wp_Load`, `Bool.wp_Store`, `wp_CompareAndSwapInt32`, ...) | `sync/atomic` |

### Other proved packages

`Perennial/Proof/{sort,slices,math,bytes,strings,errors,cmp,unsafe}.lean` and
their `*_proof` directories (`wp_Search`, `wp_SearchInts`, `wp_Find`, the
`pdqSort` family, ...); `Perennial/Proof/math/big.lean` (`math.big.ownInt`,
`wp_NewInt`, `wp_Int64`).

---

## 5. Patterns

### Specs for function arguments

A Go function value `f : GoFunc` is specified by a persistent Texan triple about
`App (Val #f) (Val #i)`; see `predImplements` in
`Perennial/Proof/sort_proof/search.lean`, where the caller proves the triple for
a closure with `iintro %i; wp_start as ...; wp_auto; ...` and the callee uses it
with `wp_apply Hf $$ [I] with %r ⟨I, %Hf_result⟩`.

### Locks

```lean
/-- `func DoSomeLocking(l *sync.Mutex) { l.Lock(); l.Unlock() }`, for any lock
invariant `R`. -/
theorem wp_DoSomeLocking' [sync.Assumptions] (l : Loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.isMutex l R }}
      (App (Val (@! DoSomeLocking)) (Val #l))
    {{ RET #(); True }} := by
  wp_start as #Hm
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, HR⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked $HR]
  wp_end
```

### Goroutines

````lean
/-- ```go
func simpleSpawn() {
	l := new(sync.Mutex)
	v := new(uint64)
	go func() {
		l.Lock(); x := *v; if x > 0 { Skip() }; l.Unlock()
	}()
	l.Lock(); *v = 1; l.Unlock()
}
``` -/
theorem wp_simpleSpawn' [sync.Assumptions] :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! simpleSpawn)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  -- both `new` allocations are bound to `$r0` by goose, so the mutex's location
  -- and points-to are inaccessible: name them (by position, then by type)
  rename_i mu_ptr
  irename : (mu_ptr ↦ zero_val Bool : IProp GF) => Hmu
  imod sync.init_Mutex iprop(∃ x : w64, «$r0_ptr» ↦ x) ⊤ mu_ptr $$ Hmu [«$r0»] with #Hlock
  · inext; iexists _; iexact «$r0»
  -- the local variables `l` and `v` are read by both goroutines
  ipersist l
  ipersist v
  wp_apply wp_fork $$ []
  · -- the spawned goroutine
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, ⟨%x, Hx⟩⟩
    wp_if_destruct
    · wp_func_call   -- `Skip()`: unfold the function and step through it
      wp_call
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hx]
      · iexists _; iexact Hx
      itrivial
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hx]
      · iexists _; iexact Hx
      itrivial
  -- the main goroutine
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, ⟨%x, Hx⟩⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hx]
  · iexists _; iexact Hx
  wp_end
````

### Ghost state and invariants

```lean
/-- The invariant owns half of a ghost variable `γ` holding a counter; the
other half is held by a client. (An `abbrev`, so that `iexists`/`icases` see
through it; for a `def`, `unfold counter_inv` first.) -/
abbrev counter_inv (γ : GName) : IProp GF :=
  iprop(∃ n : Nat, ghostVar γ (1 : Qp).half n)

theorem counter_alloc (N : Namespace) (E : CoPset) :
    ⊢ |={E}=> ∃ γ, inv N (counter_inv γ) ∗ ghostVar γ (1 : Qp).half (0 : Nat) := by
  imod ghostVar_alloc (0 : Nat) with ⟨%γ, Hv⟩
  icases ghostVar_split γ (0 : Nat) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod inv_alloc N E (counter_inv γ) $$ [Hv1] with #Hinv
  · inext; iexists 0; iexact Hv1
  imodintro
  iexists γ
  iframe # ∗

theorem counter_incr (N : Namespace) (γ : GName) (n : Nat) :
    inv N (counter_inv γ) ∗ ghostVar γ (1 : Qp).half n ⊢
      |={⊤}=> ghostVar γ (1 : Qp).half (n + 1) := by
  iintro ⟨#Hinv, Hv⟩
  iinv Hinv with ⟨%m, >Hv'⟩ Hclose
  icombine Hv Hv' gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (n + 1) γ n n $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv'] with _
  · inext; iexists _; iexact Hv'
  imodintro
  iexact Hv
```

Inside a WP: `wp_bind` the atomic instruction, `iinv`, `wp_apply_core` the
atomic spec, `iintro` its postcondition, `imodintro`, close the invariant
(`isplitl [..]` against the closing conjunct, as `wp_runtime_Semacquire` in
`sema.lean` does, or `imod Hclose $$ [..]`), and continue with `wp_auto`.

### Later credits

`wp_auto_lc n` (or `wp_apply (lc := n) ...`, `wp_pure_lc H`, `wp_call_lc H`) yields
`£ 1` hypotheses. Use them to strip a later from a non-timeless hypothesis under
a fancy update: `imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi`
(`once.lean`), or `inext 1 credit: Hlc1` (iris-lean).

### Löb induction

`iloeb as IH generalizing %x H` (see `wp_Assume` in
`Perennial/Proof/github_com/goose_lang/primitive.lean` and the proof of
`wp_for` in `Loop.lean`).

### Time receipts

Time receipts (Mével, Jourdan, Pottier, "Time credits and time receipts in
Iris", ESOP 2019) let a proof assume that a program runs for fewer than `N`
steps, for a bound `N` that the proof does not fix, e.g. to show that a 64-bit
counter that is incremented once per call never overflows (given the premise
`N ≤ 2^64`). Files:
`Perennial/GooseLang/BoundedLang.lean` (semantics),
`Perennial/GooseLang/Receipts.lean` (ghost state and laws),
`Perennial/GooseLang/Lifting.lean` (`wp_GoInstruction_receipt`),
`Perennial/GooseLang/Adequacy.lean` (adequacy),
`Perennial/ProgramLogic/TimeReceiptsTest.lean` (laws and the paper's clock).

**The bound `N`.** `N` is the field `receiptBound GF : Nat` of the receipt
ghost state (with `receiptBound_pos : 0 < receiptBound GF`):

```
class ReceiptGS (GF : BundledGFunctors) where
  receiptAllG : AllG GF
  receiptTokName : GName
  receiptLbName : GName
  receiptBound : Nat
  receiptBound_pos : 0 < receiptBound
```

The receipts use only the generic ghost libraries. The step counter is a
`mono_nat` (`receiptLbName`), and `⧖ n` is its lower bound `n` plus `⌜n < N⌝`.
Each counted step `k` also issues an exclusive `ghost_map` token `k ↪ ()`
(`receiptTokName`), and `⧗ n` is `n` such tokens, each with `⧖ (k + 1)`.
Tokens are distinct steps, so the latest of `n` of them gives `⧖ n`; this is how
the snapshot rule and `⧗ n ⊢ ⌜n < N⌝` hold without the authoritative counter.
`receiptAllG` is an instance only inside `Receipts.lean`; elsewhere proofs keep
their own `[AllG GF]`.

`ReceiptGS` is a field of `GooseGlobalGS`, hence available from `HeapGS`, so a
proof can write `receiptBound GF` without new section variables. Nothing else
depends on `N`: the language instance, `PureExec`/`Atomic` instances and the
receipt camera (`ReceiptGpreS`, `GooseGpreS`) are the same for every `N`. A
proof that needs `N` to be small states it as a premise, e.g.
`(Hbound : receiptBound GF ≤ 2 ^ 64)`, and every caller passes the premise on;
the client discharges it when it picks `N` at adequacy time (below). Prefer to
put the premise only where it is needed: if the code is safe for every `N` and
only some resource of the postcondition depends on the bound, make that resource
conditional (a postcondition `⌜receiptBound GF ≤ 2 ^ 64⌝ -∗ R`) rather than
the whole spec.

**Semantics.** The trusted `BaseStep` is unchanged. The registered language
instance `goose_ectxi_lang` is a layer on top of it whose state is
`CfgState × Nat`; the number is a *fuel* for *Go instruction* steps
(`App (Val (GoInstruction op)) (Val v)`: function/method resolution, typed
loads, stores and allocations, struct operations, ...). With fuel `f + 1` a Go
instruction takes its real step and leaves fuel `f`; with fuel `0` it
*stutters* (expression and state unchanged), the paper's "`tick` diverges at
the limit". All other steps are real steps that leave the fuel alone. The
adequacy theorems start with fuel `N - 1`, and the state interpretation owns
`receiptFuel f`, the authoritative receipt counter `receiptAuth (N - (f + 1))`.
Only Go instructions are counted because a step that can stutter is neither
pure (`PureExec`) nor atomic (`Language.Atomic`), and the heap primitives must
stay atomic for invariant opening; Go instructions have a single lifting lemma
(`wp_GoInstruction`) that handles the stutter by Löb induction.

**Assertions and laws.** `⧗ n` (`receipt n`): `n` exclusive receipts; `⧖ n`
(`preceipt n`): persistent, "at least `n` counted steps happened". Below,
`N = receiptBound GF`.

| law | lemma |
|-----|-------|
| `⧗ (m + n) ⊣⊢ ⧗ m ∗ ⧗ n` | `receipt_add` |
| `⊢ \|==> ⧗ 0`, `⧗ n ⊢ ⧗ 0 ∗ ⧗ n` | `receipt_zero`, `receipt_zero_of` |
| `⧖ n` persistent, `⧖ (max m n) ⊣⊢ ⧖ m ∗ ⧖ n`, `⧖ n ⊢ ⧖ m` (`m ≤ n`), `⊢ \|==> ⧖ 0` | `preceipt_persistent`, `preceipt_max`, `preceipt_mono`, `preceipt_zero` |
| `⧗ n ⊢ \|==> (⧗ n ∗ ⧖ n)` (snapshot) | `receipt_snapshot` |
| `⧗ N ⊢ False`, `⧖ N ⊢ False` (hence `\|={E}=> False` for any `E`) | `receiptBound_elim`, `preceipt_bound_elim`, `receiptBound_fupd` |
| `⧗ n ⊢ ⌜n < N⌝`, `⧖ n ⊢ ⌜n < N⌝`, `⧗ 1 ∗ ⧗ n ⊢ ⌜n + 1 < N⌝ ∗ ⧗ (n + 1)` | `receipt_lt`, `preceipt_lt`, `receipt_add_one_lt` |

`⧗ N ⊢ False` holds without any invariant or mask (the paper needs
`TRInv` and its namespace): a receipt fragment records `N` and is only valid
below it.

**Getting receipts.** Every Go instruction step yields `⧗ 1` (and turns a
`⧖ m` into `⧖ (m + 1)`):

* `wp_GoInstruction_receipt` / `wp_GoInstruction_preceipt` (`Lifting.lean`),
  the general lifting lemmas;
* `wp_go_step_receipt K`, `wp_go_step_receipt'` (empty context),
  `wp_go_step_preceipt` (`PostLifting.lean`), for deterministic pure Go
  instructions (`⟦i, v⟧ ⤳ e`): `▷ (⧗ 1 -∗ £ 1 -∗ WP K[e] {{ Φ }}) ⊢ WP K[i v] {{ Φ }}`.
  Since `wp_auto` takes such steps silently, take the step by hand:
  `wp_bind (App (Val (GoInstruction (GoZeroVal _))) (Val _))`,
  `iapply wp_go_step_receipt'`, `inext`, `iintro Hr _`;
* `sync.atomic.wp_AddUint64_receipt`: `wp_AddUint64` for the unresolved call
  `atomic.AddUint64(addr, v)` as goose emits it; resolving the function is a
  Go instruction, and the atomic update receives its `⧗ 1`.

The heap primitives (`wp_load`, `wp_atomic_add`, `wp_cmpxchg_*`, ...) do not
produce receipts (they must stay atomic); every Go-level operation reaches them
through at least one Go instruction (a call or a typed access), whose receipt
can be used instead.

**Adequacy: picking `N`.** `goose_adequacy` (and
`grove_ffi_single_node_adequacy`, `disk_adequacy`, `goose_invariance`) is
stated for the real semantics and every bound `N`: the WP premise `Hwp` is
proved under the hypothesis `receiptBound GF = N`, and the conclusion is about
executions of fewer than `N` steps:

```
theorem goose_adequacy [hPre : GooseGpreS ffi GF] (N : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2)
```

A client chooses `N` and discharges the premises its proof makes about it from
`HN : receiptBound GF = N`. For a program that calls `wp_clock_incr`,
`N = 2^64` (or anything smaller) works (`TimeReceiptsTest.lean`):

```
  goose_adequacy (2 ^ 64) e σ g φ Hinitg Hinit
    (@fun hG HN Hlctx => Hwp (hG := hG) (Nat.le_of_eq HN) Hlctx) n κs t2 σ2 Hsteps Hn
```

where `Hwp` is the client's WP proof under the premise `receiptBound GF ≤ 2 ^ 64`.
The result holds for executions of fewer than `2^64` steps. Since there is
nothing to gain from a smaller `N`, a client takes the largest `N` that all the
premises allow. `RealNsteps`/`RealNotStuck` are iris-lean's
`Language.NSteps`/`NotStuck` for `gooseRealEctxiLang`. The proof applies
iris-lean adequacy to the bounded language started with fuel `N - 1`
(`goose_adequacy_blang N hN`) and the simulation `bounded_nsteps_of_real` (a
real execution of at most `f` steps is a bounded one from fuel `f`; no Go
instruction stutters) and `realNotStuck_of_bounded` (every bounded step is
backed by a real one).

**Example.** `TimeReceiptsTest.lean` verifies the paper's clock
(`wp_clock_incr`, premise `receiptBound GF ≤ 2 ^ 64`): the invariant owns one
receipt per increment, and `receipt_add_one_lt` gives the bound on the counter
when the increment opens it.

### Package initialization

```lean
-- The two instances every package proof defines (here as `example`s, since
-- `sync_proof/base.lean` already declares them for `sync`):
example : IsPkgInit (IProp GF) pkg_id.sync := define_is_pkg_init iprop(True)
example : GetIsPkgInitWf (IProp GF) pkg_id.sync := build_get_is_pkg_init_wf

-- The initialization proof: run `package.init`, initialize the imported
-- packages in order, and conclude `isPkgInit`.
example (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sync get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply internal.synctest.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsynctest⟩
  wp_apply internal.race.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hrace⟩
  wp_apply sync.atomic.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  iframe Hown
  is_pkg_init_finish
```
