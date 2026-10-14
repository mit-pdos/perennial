# Candidate cases (provisional)

These are past commits to the Go semantics and goose, not on the current
branch. An agent labelled them automatically, and the user has not reviewed
them yet. Where `examples.md` records a decision by the user, that decision
overrides the label here. When the user rules on a candidate, move it to
`examples.md`.

Labels: **COUNTEREXAMPLE**: the mechanism is a carve-out, so do not redo it.
**KEEP-IDEA**: the commit fixes a real bug and the idea is worth redoing simply.
**MIXED**: the commit has some of each.

| sha | subject | label |
|---|---|---|
| 114b847ff | goose: range over an integer | KEEP-IDEA |
| bf935cbd5 | float64(n) of an integer, an uninterpreted function | KEEP-IDEA |
| 3fbe65749 | Panics and recover on the exception monad | COUNTEREXAMPLE |
| 97da3725e | the bit clear operator `&^` | KEEP-IDEA |
| 2cb0f7810 | converting untyped nil to unsafe.Pointer | KEEP-IDEA |
| 8fcfd9fa4 | uint32 division and remainder are unsigned | KEEP-IDEA |
| 3859a488b | division by zero panics; shift counts; ^x | MIXED |
| 4020291cc | a shift count of a type-parameter type is unsupported | COUNTEREXAMPLE |
| 84edc3ea5 | eval order for s[a:], multiple assignment, select sends | MIXED (len($s) taken: examples.md Case 2) |
| d676d3851 | string slicing; a negative string index panics | KEEP-IDEA (string_slice taken: examples.md Case 1) |
| 20708027d | a trusted init function | MIXED |
| d80ae18bc | shifts carry both operand types (GoShift o t count_t) | KEEP-IDEA |
| 51e94d6e0 | a parenthesized panic statement; no panic as a for post | COUNTEREXAMPLE |
| e37e28e07 | panic(nil) is stuck | KEEP-IDEA |
| 9d575b230 | x op= y evaluates x's operands once, reads x after y | MIXED |
| 14065cae5 | x op= y reads x's variables after y when x has no call | COUNTEREXAMPLE |
| 6ccfa9d0f | a function that defers returns results after the deferred calls | KEEP-IDEA |
| 94123213b | a method value saves its receiver when evaluated | KEEP-IDEA |
| 782bb043e | reject recover() in a deferred literal that defers a recover | COUNTEREXAMPLE |
| 09596dd26 | x[i], x[lo:hi] read x after the index's calls | COUNTEREXAMPLE |
| d2327af70 | a field reference through a nil pointer panics | KEEP-IDEA |
| add4d9411 | goose/order: one evaluation order (normal form, rewriter) | MIXED |
| 58d809c28 | goose: translate in Perennial's order, check normal form | MIXED |
| 21877fd21 | goose/order: panicking operations are order-sensitive | COUNTEREXAMPLE |
| 4cba97cc9 | goose/order: make, unsafe.Slice, iface methods, type params | COUNTEREXAMPLE |
| 110aa6ed5 | goose/order: map-literal keys, promoted methods, &p[c] | COUNTEREXAMPLE |
| 4704cc981 | goose/order: strict left-to-right, only translated code | KEEP-IDEA (the rule), MIXED (the machinery) |
| ea1cf23ab | Byte-addressed memory and package unsafe | MIXED |
| 5bc34ea91 | Review round 6: no ProphId type args; reinterpretable ≤ 16 bytes | COUNTEREXAMPLE |
| ceca57591 | Review round 5: struct sizes; no non-zero blank fields; no *ProphId | MIXED |
| 257e76236 | negative tests for stack-moving uintptr operands, MaxInt index | COUNTEREXAMPLE |

Counts: KEEP-IDEA 12, MIXED 8, COUNTEREXAMPLE 11. 4704cc981 is counted as
KEEP-IDEA.

---

## 114b847ff — goose: range over an integer (Go 1.22), as the three-clause loop it stands for
**Bug it addressed:** `for i := range n` was refused, and etcd's mvcc needs it. This was a missing feature, not unsoundness.
**What it did:** It added one new `rangeStmt` case (+49 lines) that desugars to the existing `for` loop with a `$range_i` cell. A kind switch builds the literal `1` per width (64/32/8 only, so int16/uint16 and type parameters are refused). Untyped `n` gets its own branch. No semantics change.
**Provisional label:** KEEP-IDEA
**Why:** Desugaring to the three-clause loop is the right, sibling-shaped idea. The per-kind `one` switch is a type-dependent choice made in goose. Simple version: emit the untyped constant 1 (and 0) and let the semantics' `Convert` fix the type. Then one desugaring covers every integer type, type parameters included.

## bf935cbd5 — Go semantics: float64(n) of an integer, an uninterpreted function
**Bug it addressed:** `float64(n)` for an integer `n` was stuck (etcd metrics). Missing rule, sound.
**What it did:** It added `Convert` rules from int/int64/uint/uint64/int32/uint32 to float64. The rules step to 4 new uninterpreted functions in `FloatOps`. Semantics +26 lines, no goose change.
**Provisional label:** KEEP-IDEA
**Why:** It is a sibling of the existing opaque float operations (a float is an opaque bit pattern). Simple version: one rule for every integer type, which widens to 64 bits by sign or zero extension and then applies one of two uninterpreted functions. That avoids a per-source-type list that leaves out int8 and int16.

## 3fbe65749 — Panics and recover on the exception monad; no GooseLang primitives
**Bug it addressed:** None in Go terms. It is a redesign: it replaced the primitive-language panics (PanicV/Catch/unwinding HeadStep, present at c46da895a) with a third exception-monad outcome `("panic", v)`, to remove the not-a-panic side conditions from the logic.
**What it did:** Under the redesign, a panic exists only where `;;;` threads it, so `panic(..)` became a syntactic statement. It added 3 goose branches (bare emission of an ExprStmt panic, a refusal of `defer panic`, a refusal of `go panic`) and 1 negative test. A panic no longer crosses a function boundary: it is stuck at `exceptionDo`, and the tests of recovery two calls down were deleted. Semantics: Defer/Exception rewritten, Lang −126 lines.
**Provisional label:** COUNTEREXAMPLE
**Why:** It is not compositional. A panic means something only in statement position, which spawned 51e94d6e0 (parenthesized panic, for-post panic), e37e28e07 (panic(nil)) and 782bb043e (nested recover). Every outcome-dropping context became a carve-out. The primitive panic, which works as an expression anywhere, is the uniform scheme.

## 97da3725e — Go semantics: the bit clear operator `&^` on integer types
**Bug it addressed:** `GoOp GoBitClear` had no rule (`time.Time.Add` was stuck). Sound but incomplete.
**What it did:** It defined `x &^ y` as `x & ^y` at each integer type, in Predeclared (+33/−22). No goose change.
**Provisional label:** KEEP-IDEA
**Why:** This completes the uniform operator table with a sibling rule. Better still, state it once, generically over integer types, as `and x (complement y)`, rather than per type.

## 2cb0f7810 — Go semantics: converting untyped nil to unsafe.Pointer
**Bug it addressed:** `unsafe.Pointer(nil)` was stuck (time.AfterFunc to runtime newTimer).
**What it did:** It added one `Convert go.untypedNil unsafe.Pointer` rule that gives the null pointer (+5 lines).
**Provisional label:** KEEP-IDEA
**Why:** It is an exact sibling of the other nil conversions and completes the scheme.

## 8fcfd9fa4 — Go semantics: uint32 division and remainder are unsigned
**Bug it addressed:** `div_uint32`/`remainder_uint32` used `sdiv`/`srem`, so `uint32(0x80000000)/2` gave `0xC0000000`. Unsound (a wrong defined value).
**What it did:** It changed 2 rules to `/` and `%` on w32, like the other unsigned types (+2/−3), and added tests in Theory/Test.
**Provisional label:** KEEP-IDEA
**Why:** It is a pure bug fix that makes uint32 a true sibling of the other unsigned types. It argues for writing the rules generically by signedness, so that a copy-paste slip like this cannot happen.

## 3859a488b — Go semantics, goose: division by zero panics; shift counts are not truncated; ^x
**Bug it addressed:** There were three. `x/0` gave a total BitVec value where Go panics. Shift counts were converted to x's type, so `uint8(1) << uint64(256)` gave 1 where Go gives 0, and a negative count did not panic. `^x` was translated as boolean `GoNot`.
**What it did:** Division by zero: each `div_*`/`remainder_*` rule now has `if v2 = 0 then Panic`. Shifts: the count is taken as w64, and goose chooses per count type between a zero extension to uint64 and a new `go.shiftCount` (2 goose branches). `^x`: a one-line routing through the general unary path.
**Provisional label:** MIXED
**Why:** The division-by-zero panic and the `^x` fix are simple refinements and worth keeping. The shift-count part makes a type-dependent choice in goose (signedness of the count), which later required the 4020291cc refusal. d80ae18bc is the simple version of the shift part.

## 4020291cc — goose: a shift count of a type-parameter type is unsupported
**Bug it addressed:** goose's shiftCount read signedness from `Underlying()` as a `*types.Basic`. A type-parameter count `T ~int8` was therefore treated as unsigned, and `Shl[int8](1,-1)` gave 0 where Go panics.
**What it did:** It added a refusal of shift counts of type-parameter type (1 goose branch, 1 negative test).
**Provisional label:** COUNTEREXAMPLE
**Why:** The refusal names a case. It exists only because goose was making a type-dependent choice. The fix is to move the choice into the semantics (d80ae18bc), not to fence off the cases goose cannot decide.

## 84edc3ea5 — goose: Go's evaluation order for s[a:], multiple assignment and select sends
**Bug it addressed:** There were three. `f()[1:]` evaluated `f` twice, because the high bound was `len(x)`. In `i, a[i] = 1, 9`, the target address was computed after the earlier stores. A select send evaluated its value before its channel.
**What it did:** `len($s)`, a one-line change, taken as examples.md Case 2 (110478a07). For multiple assignment it added a 3-way branch (identifier / map index / other), active only when `multi`, which binds `$l<i>` or `$lm<i>`/`$lk<i>` first. For select it reordered two lets.
**Provisional label:** MIXED (len($s): done; select reorder: KEEP-IDEA; multi-assign: redo simply)
**Why:** The multi-assign fix is right about Go but adds a single-vs-multi case and an identifier case. Simple version: every assignment binds each non-identifier target (address, or map and key) before the right-hand sides, the same way for one LHS or many, using one helper shared with op=.

## d676d3851 — StringSemantics: string slicing; a negative string index panics
**Bug it addressed:** `s[lo:hi]` on a string was stuck, which is why strings.HasPrefix and others had models. `s[-1]` read `s[0]`, because `sint.nat` clamps to 0, where Go panics. That second bug was unsound.
**What it did:** It added a `string_slice` rule with Go's bounds panic, and added `0 <= i` to `string_index` (String.lean +19).
**Provisional label:** KEEP-IDEA (string_slice: taken as examples.md Case 1 (6f38ab75f); the negative-index guard is still to redo)
**Why:** Both changes complete the scheme with a sibling rule that has the same bounds-panic shape as slices. Neither touches goose.

## 20708027d — goose: a trusted init function
**Bug it addressed:** `internal/bytealg`'s init sets `MaxLen` from a CPUID bit that no translation computes. An untranslated init was silently dropped.
**What it did:** It let `trusted = ["init"]` emit `init.impl` in the init's place. That is 1 goose branch plus an "at most one trusted init" refusal, and +13 lines in goose.
**Provisional label:** MIXED
**Why:** Treating init as a trustable declaration like any other is uniform. The "at most one" rule and the special name are a case. The silent drop of an untrusted, untranslated init (the real gap) was left open. Simple version: an init that is neither translated nor trusted is an error, and trusted inits are referenced by index, like any trusted declaration.

## d80ae18bc — Go semantics, goose: shifts carry both operand types (GoShift o t count_t)
**Bug it addressed:** The same shift-count bugs as 3859a488b and 4020291cc, without goose deciding per type. A type-parameter count becomes defined.
**What it did:** It added a new instruction `GoShift o t count_t` (Lang, Countable, Notation), resolved through `go_shift_underlying`, with per-count-type `shift_count_*` rules (Predeclared +101/−53). goose emits both operand types unchanged (−25/+14) and removes its type switch and the refusal. The negative test becomes a unit test.
**Provisional label:** KEEP-IDEA
**Why:** It moves the type-dependent choice out of goose into Lean, and goose becomes purely compositional. The cost is a new instruction, so check whether the op's type field could carry the pair, to avoid a sibling of `GoOp`. The idea is the model fix for type-dependent operands.

## 51e94d6e0 — goose: a parenthesized panic statement is a panic; no panic as a for post
**Bug it addressed:** Under 3fbe65749's design, `(panic("x"))` went under `do:`, and `for ...; panic("p") {}` dropped the panic. Both made programs that Go kills verify as returning.
**What it did:** It added `ast.Unparen` in isBuiltinCall, a refusal of panic as a for-post statement (1 goose branch, 1 negative test) and a unit test.
**Provisional label:** COUNTEREXAMPLE
**Why:** These are the textbook context-dependent cases ("when parenthesized", "as a for post") that a fuzzer finds one at a time. They exist only because panic was syntactic. The fix is to drop the design that needs them.

## e37e28e07 — Go semantics: panic(nil) is stuck
**Bug it addressed:** `wrapDeferRecover` reads a nil `$panic` cell as "recovered". So `defer func(){ if err != nil { recover() } }(); panic(nil)` returned normally, where Go 1.21+ panics with a PanicNilError. The same nil check exists in c46da895a's Catch-based wrapper.
**What it did:** It made `panic.impl` stuck on a nil argument (one guard, +11 in Predeclared) and removed one PureWp lemma.
**Provisional label:** KEEP-IDEA
**Why:** It is one general rule in the semantics with no goose change, less defined than Go and never different. It also applies to the c46da895a design. An alternative is to make panic(nil) panic with a fixed non-nil value, as Go does, but stuck is acceptable.

## 9d575b230 — goose: x op= y and x++ evaluate x's operands once, and read x after y
**Bug it addressed:** `a[f()] += 1` called `f` twice, because the translation built `x = x op y` from the same AST. In `x += f()` with `f` setting x, x was read before `f` ran.
**What it did:** It added `updateStmt`: it binds `$opa` (address) or `$opm`/`$opk` (map), then `$opy`, then load/op/store. It has special cases for an identifier target (not bound), a constant y (not bound) and a map target. `x++` becomes `x += 1` through goose's constant encoder, removing a kind switch. +90/−53 in goose.
**Provisional label:** MIXED
**Why:** Evaluating the target once and reading after y are real Go facts, and routing `x++` through `x += 1` removes a case. The ident/const/map shortcuts are optimizations that turn into cases. Simple version: one shape, `let a := addr(x) in let v := y in a <- !a op v` (map: `let m, k`), always, sharing the target binder with multiple assignment.

## 14065cae5 — goose: x op= y reads x's variables after y when x's operands have no call
**Bug it addressed:** After 9d575b230, the target was bound before y. In `a[i] += f()` with `f` setting i, gc updates the new `a[i]`. The spec leaves this order unspecified, but gc reads after.
**What it did:** It made the order depend on `hasCallOrRecv(x)`: y first if x has no call, target first otherwise (+35 in goose). It documents a remaining spec-allowed and gc-divergent case.
**Provisional label:** COUNTEREXAMPLE
**Why:** The translation of `x op= y` depends on whether its subexpressions contain calls, so it is not compositional. It chases gc's unspecified order case by case. The evaluation-order question belongs to one global rule (see 4704cc981), not to per-construct heuristics.

## 6ccfa9d0f — Go semantics: a function that defers returns its results after the deferred calls
**Bug it addressed:** `defer func(){ r = 2 }(); return 1` returns 2 in Go and returned 1 in the model. A deferred literal also read the stale `r`. Unsound.
**What it did:** In functions that defer, results get cells `$res<i>`, and `return e…` stores into them and then does `return: #()`. `with_defer:` takes a results thunk. +123/−67 in goose, and Defer.lean rewritten. A function without defer keeps the old return translation.
**Provisional label:** KEEP-IDEA
**Why:** The bug is real and the result-cell idea matches Go's spec ("return assigns the results"). But `return` now has two translations, chosen by whether the body defers, which is context-dependent. Simple version: every function holds its results in cells, `return` always stores into them, and the wrapper (`exception_do` or `with_defer`) reads them at the end.

## 94123213b — goose: a method value saves its receiver when it is evaluated
**Bug it addressed:** For `f := t.Get; t.x = 2; f()` (and `defer t.Get()`), goose emitted `MethodResolve (*T) "Get" &t`, which loads `*&t` only at the call, so the later mutation was seen. Go saves the receiver at the selector. Unsound.
**What it did:** It rewrote the MethodVal case: it evaluates the receiver along the embedded path from `selection.Index()` with the shared field-selection code, then applies auto-&/auto-* as the type checker fixed it, and resolves M on that type (+41/−18). It has one `nope` (pointer method on a non-addressable value).
**Provisional label:** KEEP-IDEA
**Why:** It is a genuine soundness fix, and the shape (receiver value computed once at the selector, form taken from the type checker) is compositional. Keep the version that follows Go's own desugaring `x.M = (x.f1…fk).M` with the implicit `&`/`*`. Avoid the haveAddr/needAddr 2×2 matrix where a single "receiver value" helper would do.

## 782bb043e — goose: reject recover() in a deferred literal that itself defers a recover
**Bug it addressed:** A deferred literal D that calls recover() and also defers a recover-calling literal gets its own `with_defer_recover:`. The fresh `$panic` cell shadows the outer one, so D's recover() missed the panic: Go returns 1, the model returned 10. Unsound.
**What it did:** It added a refusal (`callsRecoverDirectly && defersRecover`, +25 in goose, 1 negative test).
**Provisional label:** COUNTEREXAMPLE
**Why:** The refusal names a case. The bug is a scoping bug in how `$panic` is bound: the same name is reused for two cells. Simple version: recover() in a deferred literal reads the cell of the frame that deferred it, either passed explicitly to the deferred literal or bound under a non-shadowable name. The nesting then works without a rule.

## 09596dd26 — goose: x[i] and x[lo:hi] read x's variables after the index's calls
**Bug it addressed:** In `s[f()]` with `f` reassigning s, gc indexes the new s and the model indexed the old one. The spec leaves the order unspecified.
**What it did:** It added `indexFirst`, bound bounds, and `mayAssignVars`: the index is bound before x only when x has no call and the index has one. +114/−20 in goose, over 3 sites (Index, IndexRef, Slice).
**Provisional label:** COUNTEREXAMPLE
**Why:** It is the same pattern as 14065cae5. The translation of `x[i]` depends on a call-containment analysis of both operands, so it is not fuzzable compositionally. It mimics gc's unspecified choice per construct.

## d2327af70 — Go semantics: a field reference through a nil pointer panics
**Bug it addressed:** `StructFieldRef t f null` stepped to an address, so `var p *E; _ = &p.T` (and `p.PGet` through an embedded value) returned 1 where Go panics. Unsound.
**What it did:** It changed one step in PostLang (on null, `Panic "nil pointer dereference"`) and added 2 abstract-address properties (`structFieldRef_null`, `_null_inv`) to CoreSemantics. There is no goose change. The proof-side cost is large: atomic specs take `u ≠ null`, and tactics discharge it.
**Provisional label:** KEEP-IDEA
**Why:** It is one rule that refines a defined step to stuck, mirroring `arrayIndexRef`, with goose untouched. This is how a fix should look. The proof-automation burden is outside the trusted base.

## add4d9411 — goose/order, cmd/perennial-order: one evaluation order for verification and compilation
**Bug it addressed:** The spec orders only calls and receives, and gc differs from gc -race. goose's fixed order might not be the compiled one.
**What it did:** It added a trusted normal-form checker (`IsNormal`: every read a call could affect is spec-ordered with every event) and an untrusted source rewriter that hoists events into temporaries. A `-toolexec` wrapper compiles everything through the rewriter. This is 2149 new lines in goose/order and goose/cmd.
**Provisional label:** MIXED
**Why:** Fixing one order and making the compiled code agree is the right global answer, rather than per-construct heuristics (09596dd26, 14065cae5). But the trusted definition of the normal form is a list of order-sensitive node kinds, which grew in three later review rounds. Rewriting the whole toolchain's compilation is a large cost. Count it against a simpler goal.

## 58d809c28 — goose: translate in Perennial's evaluation order, checking the normal form
**Bug it addressed:** goose still translated unrewritten source.
**What it did:** goose now loads, rewrites, reloads from an overlay and checks `CheckFile` on each translated statement (+62 in interface.go). Translations gain `_orderN` temporaries.
**Provisional label:** MIXED
**Why:** Making the trusted part only "the normal-form definition plus this check" is a good trust split. Its value is tied to add4d9411's machinery, and the generated code gets noisier.

## 21877fd21 — goose/order: operations that can panic are ordered with the events too
**Bug it addressed:** A statement like `x/y + f()` was accepted as normal, but a compiler could panic on the division before `f` runs.
**What it did:** It added order-sensitive nodes: index/slice bounds, nil deref, type assertion, division by a variable, signed shift count, interface comparison, slice-to-array conversion, `len` of a map, and `string(b)`. normal.go +106, with tests.
**Provisional label:** COUNTEREXAMPLE
**Why:** It grows an enumerated case list found by review, the carve-out pattern this skill avoids. Simple version: treat every non-trivial operation as order-sensitive (only variables and constants are free), or adopt 4704cc981's strict order, so that no list is needed.

## 4cba97cc9 — goose/order: make, unsafe.Slice/String, interface methods and type parameters are order-sensitive
**Bug it addressed:** More operations that can panic were missing from the normal form: `make(n)`, `unsafe.Slice`, interface method values, unhashable map-literal keys, type-parameter operands.
**What it did:** It added five more node kinds to normal.go (+51) and a `@file` refusal in perennial-order.
**Provisional label:** COUNTEREXAMPLE
**Why:** It is a second round of the same list, which shows the definition was not closed under a general rule. Each round is a new negative-test family.

## 110aa6ed5 — goose/order: map-literal keys, promoted methods and fields, &p[c] are order-sensitive
**Bug it addressed:** A third round: map-literal keys hashed per entry, promoted pointer methods through embedded fields, `&pa[c]` on a pointer to an array, promoted fields on an LHS.
**What it did:** It added 4 more cases (normal.go +13, stmt.go +6).
**Provisional label:** COUNTEREXAMPLE
**Why:** The list grew again. A rule that needs a fourth review round to enumerate is a carve-out list, not a rule.

## 4704cc981 — goose/order: strict left-to-right evaluation, applied only to translated code
**Bug it addressed:** Under add4d9411, the meaning of `x` in `x + f()` depended on its right neighbour, because calls ran first. Rewriting all of std also broke code relying on gc's order (crypto/x509.ParseOID).
**What it did:** The order became strict left-to-right: each operand is evaluated completely before the next. The normal form gained the `&&`/`||` ordering. Only translated declarations are rewritten (`-code DIR`). rewrite.go +414/−109, perennial-order +92.
**Provisional label:** KEEP-IDEA (the order rule); MIXED (the machinery)
**Why:** Strict left-to-right is the compositional rule: the meaning of e depends only on its subexpressions, which is exactly the fuzzability principle, and goose's natural translation already follows it. The open question for the user is enforcement. The rewriter, the toolexec wrapper and the normal-form list remain a large trusted or operational cost.

## ea1cf23ab — Byte-addressed memory and package unsafe, sound for bbolt
**Bug it addressed:** It is a feature. bbolt needs package unsafe, and the heap was not byte-addressed.
**What it did (high level):** Memory became byte cells with multi-cell, race-detecting typed accesses. Atomics are stuck unless aligned. gc's linux/amd64 struct layout is emitted by goose. It added the unsafe semantics: Sizeof/Offsetof, uintptr congruent mod 8, an exact pointer difference only within one call-free expression, and unsafe.Slice checks. 6400 lines changed, about 1250 of them in Lifting and about 300 in Lang.
**Provisional label:** MIXED
**Why:** A byte-addressed heap is a uniform foundation worth having. The unsafe layer encodes gc implementation details as special rules: the "call-free expression" window, the stack-moving refusals and the 16-byte limit in 5bc34ea91. These attracted review-round carve-outs. Simple version: land the byte heap alone, and admit only the unsafe patterns that follow from one general rule, leaving the rest stuck.

## 5bc34ea91 — Review round 6: no ProphId in type arguments; reinterpretable aggregates at most 16 bytes
**Bug it addressed:** First, ProphId is 0 bytes in gc but not in the model, so it diverged when substituted for a type parameter. Second, gc copies values over 16 bytes in a forward loop, so overlapping reinterpreted views corrupt where the model copies whole.
**What it did:** It added a refusal of type arguments that mention ProphId (1 goose branch, 1 negative test) and a new class `SizeAtMost16` as a premise of `Reinterpretable`. A blank type-parameter field is now refused, where goose crashed before. autotypes +81.
**Provisional label:** COUNTEREXAMPLE
**Why:** It chases one named type through generics, and it hard-codes a gc copy strategy (16 bytes) into the semantics. Simple versions: give ProphId gc's size of 0 in the model, so that no refusal is needed. Make overlapping copies stuck in general rather than bounding the size.

## ceca57591 — Review round 5: struct sizes from field types; no non-zero blank fields; no *ProphId
**Bug it addressed:** `Reinterpretable`'s "no padding" check accepted an arbitrary list of sizes, so a padded struct could pass, which is unsound. Blank fields' bytes are ignored by Go's `==`, but the model keeps them. gc gives every `*ProphId` the same address.
**What it did:** The struct case now sums the fields' own `typeSize` (`StructSize`). goose refuses blank fields of non-zero size and refuses `*ProphId` (2 goose branches, 2 negative tests). It regenerated runtime.
**Provisional label:** MIXED
**Why:** Computing the size from the field types is a real fix of a proof obligation that had no content (KEEP). The blank-field and `*ProphId` refusals are named carve-outs. The ProphId ones disappear if the model matches gc's 0 size. Blank-field `==` belongs in the semantics of struct equality, not in a goose refusal.

## 257e76236 — goose: negative tests for the stack-moving uintptr operands and the MaxInt literal index
**Bug it addressed:** The refusals from the unsafe work had no tests: an `unsafe.Pointer(uintptr(p) + off())` whose offset contains a call or a map index ("may move the stack"), and `[]byte{MaxInt: 1}` ("gc miscompiles it").
**What it did:** It added 3 negative tests, with no code change.
**Provisional label:** COUNTEREXAMPLE
**Why:** Each test pins a refusal that names a case. "Offset contains a call", "offset contains a map index" and "literal index MaxInt" are compiler details, not a general rule. A simple rule would be: a uintptr derived from a pointer is meaningful only as an immediate operand of unsafe.Pointer(…) with no event between them (one rule, one test). A gc miscompile is not something the model should special-case.
