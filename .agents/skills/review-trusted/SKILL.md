---
name: review-trusted
description: Review a change to Perennial's trusted base (the Go semantics in GooseLang/Golang/Defn, the goose translator, trusted models in TrustedCode, goose .toml trust lists, adequacy theorem statements, assume/axiom/sorry) for soundness and for trust that should not have been added (above all, trusted models of Go that goose translates or could be extended to translate: trust is only for irreducible primitives, shown by a goose run on the real source), and optionally fix it. Use before committing or merging any change that touches those files, when asked to review a commit, range or PR for trust/soundness, or when asked whether a model assumption or trusted model is acceptable.
argument-hint: "[commit | A..B | (nothing: branch + working tree)] [--fix]"
---

# Review a change to the trusted base

Perennial's theorems are only as good as what they rest on. The question this
review answers for a change is: **does it add trust, is each addition
necessary, and is each addition true of Go?** The reviewer's default is no:
new trust must earn its place. `cases.md` (next to this file) has graded past
changes; read it once before reviewing, and compare the change against them
(if it is missing, say so under "Skipped" and proceed). Precedent does not
lower a grade: a merged change of the same shape means that change also needs
rework, not that this one is fine (say both).

Tiers (what the helper script reports):

| tier | what | files |
|---|---|---|
| 0 | **semantics** (the model of Go) | `Perennial/GooseLang/{Lang,BoundedLang,Adequacy,Threads,Receipts,Locations}.lean`, `GooseLang/Ffi/**`, `Perennial/Golang/Defn/**`, `{Grove,Disk}Prelude.lean` |
| 0 | **translator** | `goose/**` (`*.go`), gold files `goose/testdata/**/*.gold.lean`, Go models `goose/model/**` |
| 0 | **trusted models** | `Perennial/TrustedCode/**` |
| 0 | **goose configuration** | `Perennial/Code/**/*.toml` (`trusted`, `translate`, `!p`, `trust_proofgen`) |
| 1 | generated (trusted only through goose) | `Perennial/Code/**/*.lean`, `Perennial/GeneratedProof/**` |
| 2 | logic and libraries (proved, but can hide trust) | `GooseLang/Lifting.lean`, `Golang/Theory/**`, `Std`, `Algebra`, `Ghost`, `IrisLib`, `Helpers` |
| 3 | proofs, docs, tooling | `Perennial/Proof/**`, `ProgramLogic/**`, `docs/`, `README.md`, `etc/` |

Also trusted wherever they appear: `axiom`, `sorry` outside `Perennial/Proof`,
`opaque`, `partial def`, `native_decide`/`bv_decide`/`ofReduceBool`,
`implemented_by`/`@[extern]`, the *statements* of `goose_adequacy*` and
`goose_invariance*` and the hypotheses they put on the client.

## Procedure

1. **Get the trust delta.** From the repo root (plain commands; keep scratch
   files in a scratch directory, not in the repo):

   ```
   python3 etc/trusted-delta.py [TARGET]
   ```

   `TARGET` is a commit, a range `A..B`, or nothing (the branch's commits plus
   the working tree, against the merge base with `origin/<primary>`). The report
   lists changed files by tier, flags *signal* lines (assume, axiom, sorry,
   Panic, step rules, trusted `.impl`s, trust lists, ...), shows the
   before/after of the goose trust lists, and for each new trusted model prints
   the Go code its docstring claims to model next to the real Go source
   (`go doc -src`). Read the tier-0 diffs in full; `--full` prints the other
   tiers. Also read, outside the report, the specs and proofs that *use* each
   new trusted item (`grep` for its name under `Perennial/Proof`,
   `Golang/Theory`): R4 and R7 cannot be applied from the model alone. If
   there is no tier-0 change and no signal in tiers 1-2, say so and stop: this
   review is about trust, `/code-review` is about bugs. `git show TARGET`
   gives the rest of the change (README, docs, proofs) that steps 2 and R8
   need.

2. **Read the commit message / PR description for the *why*.** A trusted
   change must say what it adds to the trusted base and which lower rung of R1
   it rejected. No *why* at all for new tier-0 trust: REWORK (R8). A *why*
   without the rejected alternative: NOTE (R8), unless R1 finds the
   alternative was the right one, in which case R1 carries the finding.

3. **Classify every tier-0 item** as one of: new semantics rule; changed
   semantics rule; new/changed trusted model; new model assumption (`assume`,
   `AngelicExit`, stuck `Panic`); trust-list change; translator change;
   adequacy-statement change; new axiom/sorry/opaque. Then apply the rules
   below to each. Do not skip an item because it looks routine: the two
   calibration failures in `cases.md` both looked routine.

4. **Verify, do not infer.** Each rule says how. At minimum:
   - compare a trusted model with the *real* Go source (the report's
     `go doc -src` output, or the Go module source) line by line; `go doc -u`
     shows unexported helpers (`genSplit`, ...);
   - for **every** trusted entry the change adds or touches (a `trusted` name,
     a `"!Name"` in `translate`, a hand-written `.impl`, a `Name.underlying`
     in `TrustedCode`), run goose on the **real** Go source with the entry
     moved from `trusted` to `translate`, and record what goose says (R2).
     Copy the configuration so the repo is untouched:
     `cp -r Perennial/Code <scratch>/cfg` (a few MB),
     edit `<scratch>/cfg/<pkg>.toml`, then
     `<scratch>/goose -out <scratch>/out -configdir <scratch>/cfg -dir goose <pkg>`
     (standard-library packages are translated from `-dir goose`, as in
     `etc/update-goose-new.py`). If goose translates it, the entry is
     unjustified. Then do the same for each callee the translation leaves
     axiomatized (a `FuncResolve` of a name that is neither translated nor
     trusted): move it to `translate` and rerun, until each remaining callee
     is one goose rejects. Those callees, and only those, may be trusted.
     If goose fails on the entry itself, record the exact construct and the
     function it names. Then classify each failure as *irreducible* or a
     *missing feature* (R2): only the former may stay trusted;
   - when a docstring says the model "is goose's translation of" some Go,
     check that claim: put the quoted Go in a scratch module and run goose on
     it, then diff the generated `.impl` against the committed one. Build
     goose from the repo root with `go build -o <scratch>/goose ./goose/cmd/goose`
     (offline is fine: `GOPROXY=off`), then
     `<scratch>/goose -out <scratch>/out -configdir Perennial/Code -dir <scratch>/mod ./<pkg>`.
     Every line that differs is a hand edit the docstring must name;
   - for every `assume`/`AngelicExit`/stuck branch, try to write the Go
     program that reaches it (a few lines; run it with `go run` from a
     scratch directory when the answer is not obvious);
   - for a semantics or translator change, find the Go spec sentence it
     implements (`go doc`, the Go language spec) and check the edge cases
     (zero values, nil, empty, bounds, overflow, evaluation order);
   - `lake build` the touched modules and `#print axioms` the new theorems
     (look for `sorryAx` and anything beyond `propext`, `Classical.choice`,
     `Quot.sound`). `lake build Perennial` skips some modules: build the
     touched ones by name. If a build is impossible (no `.lake`, no disk),
     say so under "Skipped" and downgrade nothing: an unbuilt change is
     unreviewed, not OK.
   For a non-trivial trusted model or semantics rule, additionally spawn one
   subagent (`Agent`, general-purpose) as an adversary. Its brief: the model
   (or rule) and the Go it claims to model; the real Go source; `cases.md`;
   the semantics facts it needs so it does not chase non-divergences (strings
   are byte lists, an out-of-range index or slice is a stuck `Panic`,
   `append`'s new capacity is arbitrary, `append`'s length above `2^63` is
   assumed away (a known reachable assumption, already reported: do not
   re-report it), a model may be *less* defined than Go but not *more*); the
   toolchain (`/usr/local/go/bin/go`), a scratch directory, and the rules of
   the sandbox (no edits to the repo, no `lake`, no git). Its task: a Go
   program, as short as possible, on which Go and the model disagree
   (Go panics or returns something the model does not, or vice versa), with
   the run's output; if it finds none after trying the zero/empty/nil/bounds/
   overflow/concurrency cases, say which cases it tried. The point of a
   separate agent is that it has not read the author's justification: the
   counterexample to case 1 in `cases.md` is two lines of Go, and the people
   who had accepted the author's framing did not look for it.

5. **Report** in the format below. Then, with `--fix`, apply the playbook.

6. **Record the verdict for landing.** When the final verdict is OK (every
   BLOCK and REWORK fixed and committed, or no trusted change at all) and the
   target was the current branch, run `etc/land.sh mark-reviewed`: it records
   the branch's reviewed changes, and `etc/land.sh push` (the `/land` skill)
   refuses to move the primary branch without it. Never record with an open BLOCK or
   REWORK, and never for a review of some other commit or range.

## Rules

Each finding cites a rule. Severity: **BLOCK** (unsound, or forbidden by
`README.md`), **REWORK** (sound but adds trust that should not exist, or adds
it in the wrong place), **NOTE** (accepted trust to record, or a doc gap).

**R1. The trust ladder: trust is a last resort.**
For each new trusted item, ask what the *least trusted* way to get the same
thing is, in this order, and require the change to be on the lowest rung that
works:

1. prove it (a theorem in `Golang/Theory` or `Proof`);
2. translate the real Go source with goose (add the package/function to
   `translate`);
3. **extend goose or the Go semantics** so that the real source translates
   (a goose change with a unit test and gold file; a new rule in the right
   `*Semantics` class in `Golang/Defn` with its lifting lemma in
   `Golang/Theory`);
4. write the model *in Go* under `goose/model/` and translate it, so the
   trusted artifact is readable Go;
5. hand-write GooseLang in `TrustedCode`;
6. `assume` (R3);
7. `axiom` (needs prior discussion per `README.md`: BLOCK without it).

Rungs 4 and 5 are allowed only under R2. Every finding about *where* trust
sits names the rung the change should be on.

**R2. Trusted code must be irreducible: translate the real source, and if goose
cannot, make goose able to.**
By default goose translates the real source of every Go function. A trusted
entry is any `trusted` name, any `"!Name"` in `translate`, any hand-written
`.impl`, and any `Name.underlying` in `TrustedCode`. It is justified only when
both of these hold:

- *Evidence.* There is a goose run on the real source that fails (step 4), at
  the innermost function where it fails. The trusted unit is the smallest one
  that contains what fails, and everything around it is translated. A reason
  written in a docstring is not evidence.
- *Irreducibility.* What fails is something that no reasonable extension of
  goose or of the semantics would express as plain Go:
  - assembly, or a `go:linkname`/external function with no Go body
    (`runtime_procPin`, `stopTimer`, `bytealg.IndexString`);
  - `unsafe` code that reinterprets memory layout
    (`(*efaceWords)(unsafe.Pointer(v))`, `unsafe.String(unsafe.SliceData(b), n)`);
  - behaviour the runtime gives an object and that plain Go code cannot
    give it: a timer channel whose `cap` and `len` are 0, `sync.Mutex`'s
    runtime semaphores, a racy lock-free fast path whose races goose would
    expose.

A *missing feature* is not a justification. Examples:
- goose reports an unsupported construct of ordinary Go (a statement form, a
  builtin, a conversion, a range form);
- the translation is stuck on a missing semantics rule (string slicing,
  `&^`, a numeric conversion).

The fix for a missing feature is rung 3: extend goose (unit test, gold file)
or add the semantics rule (with its lifting lemma, R5), then translate the
real function. This holds even when only one program needs the feature.
Never write a model of that one function instead. The telltale case is a
docstring that quotes Go which is not the real source, "because the
semantics/goose has no X": the fix is to add X.

Grading:
- **No goose run recorded: REWORK.** Do the run yourself. Never accept
  "goose does not support X" or "it uses `unsafe`" without one.
- **The real source translates, or would once a callee is trusted: REWORK.**
  Translate it and trust the callee (`strings.Join` over `Builder.String`'s
  `unsafe.String`, case 4).
- **The run fails on a missing feature: REWORK.** Extend goose or the
  semantics (`strings.Split` and `TrimPrefix` over string slicing, case 2).
- **Any of these where the model also departs from Go (R4): BLOCK.**
- **"The real code is harder to prove" never justifies a model.** Prove the
  real code. If it reads state whose ownership is not yet available (a
  package variable behind an unproved initializer), that is a gap in the
  proofs to fill, not a reason to trust.
- **Inherited entries count too.** When a change adds a spec for, or touches,
  an existing trusted entry, check that entry as if it were new, and report
  the result even if the change did not create it.

**R3. A model assumption must be unreachable, not merely unlikely.**
An `assume`, `AngelicExit` or deliberately stuck branch removes executions
from the model, so every verified program is only verified on the remaining
ones. That is sound only if *no Go program can reach the removed executions*
on the platform the semantics assumes (64-bit, finite memory). The accepted
ones (`README.md`, "Model assumptions") are of the form "a count of things
that each occupy memory exceeds 2^63": `len(m)` (every entry occupies memory).
A length Go *computes and checks* is not of that kind. Two such assumptions
were accepted by mistake: `strings.Join`'s total length (case 4) and
`append`'s new length, which is reachable with zero-size elements:
`x := make([]struct{}, 1<<62); x = append(x, x...)` panics in Go
("growslice: len out of range") with no memory to speak of. The `append` one
is still open.
Test: write the shortest Go program that makes Go take the removed path. If
it exists and runs (`wg.Add(1<<30); wg.Add(1<<30)` panics in Go), the
assumption is **BLOCK**: a program with that bug would verify. "A real
program would not do this", "the scheduler would have to be adversarial",
"the proof is otherwise impossible" are not arguments: the first two describe
reachable behaviour, the third is a program-logic problem (R3a). Check the
assumption against the function's *argument domain*, not against the
docstring's story: `Add(delta int)` takes any `int`, so an argument about
goroutines or memory does not bound its counter.

*R3a.* When an assumption was added because a proof needed a bound the
program cannot provide locally, the fix is in the logic, not the model: a
spec premise the caller discharges, backed where needed by a ghost resource
whose total is bounded by adequacy (thread tokens `threadToks`, time receipts
`⧗`; `README.md`, "Bounded layer, time receipts and thread tokens"). Point
the author there.

**R4. A trusted model must be faithful to Go where Go is defined, and may be
only *less* defined, never *more*.** Compare against the real source
(`go doc -src pkg.Func`, or the module cache), not against the docstring's
paraphrase. Check, in this order: panics Go performs that the model omits
(BLOCK: the verified program may crash); behaviours the model has that Go
does not, including results Go does not promise such as a slice's capacity,
aliasing, or iteration order (BLOCK if a spec exposes them, else REWORK);
atomicity: the model may not be more atomic than Go (a CAS loop standing in
for an atomic add is fine only if it is linearizable to the same operation and
loses no behaviour) and adds no divergence Go lacks (a spinning loop in place
of a wait-free primitive is acceptable under partial correctness only, and
the docstring must say so), and a model of a lock-free or racy routine must
keep the races goose would expose; Go behaviour the model makes stuck or panicking
(NOTE if documented in the docstring and excluded by every spec; REWORK if
undocumented; a *fake* panic inserted to make a case stuck, where Go does
not panic, is REWORK even when documented: be stuck by not handling the
case). Unicode: Go strings are
bytes in the model (`GoString = List w8`); anything the Go function does per
rune is a divergence to document.

**R5. A semantics change may only add Go behaviours or refine stuck ones.**
For a new or changed rule in `Golang/Defn`, `GooseLang/Lang.lean`,
`BoundedLang.lean` or an FFI: name the Go spec sentence it implements; check
the rule is *at least* as nondeterministic as Go (a deterministic choice
where Go leaves things unspecified, such as map iteration order or an
uninterpreted conversion, must be justified in the docstring); check it
cannot turn a Go panic or a stuck state into a successful step unless Go
succeeds there; check `BoundedLang` still refines `Lang` (fuel only
stutters). Something that was stuck becoming defined is the normal, good
case (that is how R1's rung 3 looks); something that was defined changing
value is BLOCK unless the old value was a bug against Go, in which case the
message must say so. Any new or changed `*Semantics` field must have its
lifting lemma, and the gold files/translator tests must still pass
(`cd goose && go test ./...`).

**R6. Adequacy statements are the contract: every change to them is trust.**
For `goose_adequacy*`, `goose_invariance*`, `goose_init`, the grove/disk
adequacy theorems and `GooseGpreS`: new hypotheses must be about *real
executions* and checkable from outside the logic (fewer than `N` steps,
fewer than `T` live threads), never about the program's ghost state; the
conclusion must still talk about `gooseRealEctxiLang`, not only the bounded
layer; `README.md` and `docs/PERENNIAL_PROOF_REFERENCE.md` must describe the
new hypothesis. Missing documentation is REWORK; a hypothesis the client
cannot establish without trusting the logic is BLOCK.

**R7. Generated code is trusted only through goose.** Any hand edit of
`Perennial/Code/**/*.lean` or `Perennial/GeneratedProof/**` is REWORK:
regenerate with `etc/update-goose-new.py` (or the `goose`/`proofgen`
commands in `goose/README.md`) and commit goose's output. When a `.toml`
changes, the regenerated `.lean` must be in the same change. A `"!Name"` in
`translate` paired with `Name` in `trusted` replaces goose's translation of a
function goose *can* translate by a hand-written one: that needs an R2
justification in the commit message, and the model must be goose's own output
of the real source except for the one documented change (rename the model's
parameters back to the generated names, then `diff` the two bodies; or run
goose on the source as in step 4).

**R8. Trust must be visible.** Every tier-0 addition needs: a docstring that
says what the model/rule does *and* where it departs from Go; the commit
message saying why trust was added and which lower rung was rejected; for a
model assumption, an entry in `README.md` "Model assumptions"; for an
adequacy or semantics change, the corresponding section of `README.md` /
`docs/PERENNIAL_PROOF_REFERENCE.md`. Also apply the project's size heuristic
to goose changes: a translator change must be small and obviously correct
(prefer fewer lines); a large translator diff is REWORK unless split.

**R9. No hidden trust in tiers 1-2.** `sorry` in `GooseLang`, `Golang`,
`Std`, `Algebra`, `Ghost` is an axiom: BLOCK. `opaque`, `partial def`,
`implemented_by`, `unsafe` in those tiers: BLOCK unless the docstring shows
nothing is proved about the value. `native_decide`/`bv_decide`: BLOCK
(`README.md`). `set_option` that disables a linter or raises a limit in a
tier-0 file: NOTE, ask why.

## Report format

Lead with the verdict, then the trust delta, then findings, then what was
checked. Keep it short enough to act on.

```
Verdict: BLOCK | REWORK | OK (n NOTEs)

Trust delta (everything the change adds to the trusted base, accepted or not):
- <item>: <one line: what it trusts, and why that rung of R1 is the right one;
  for a trusted entry, the goose run on the real source and its result (R2):
  "translates" (REWORK), "missing feature: <construct>" (REWORK, extend goose
  or the semantics), or "irreducible: <construct> in <innermost function>">
Inherited (pre-existing trust the change relies on, for context): <...>
Made visible (trust that already existed and that the change now documents): <...>

Findings (most severe first):
1. [BLOCK R3] <file:line> — <defect in one sentence>.
   Evidence: <the Go program / spec sentence / diff that shows it>.
   Fix: <the concrete change; name the lower rung for R1, the resource for R3a>.
2. ...

Checked: <commands run: build, #print axioms, go run, go test, go doc, goose>
Skipped: <steps not done and why (no build on disk, no toolchain, ...)>
```

Record accepted trust too: the user reads the trust delta to decide, not
only the findings. An empty findings list with a non-empty trust delta is a
normal outcome.

## `--fix`

Work in a worktree if not already in one (`EnterWorktree`). Apply the fixes
most-severe first, each as its own commit with a message that explains the
soundness reason (the message is itself reviewed by R8). Playbook:

- **Reachable assumption (R3):** remove the `assume`/stuck branch and restore
  Go's behaviour, preferably by letting goose translate the function again
  (drop the `!Name`/`trusted` entries, regenerate). Move the obligation into
  the spec as a premise; if a caller cannot discharge it locally, back it with
  the ghost resource that adequacy bounds (R3a). Re-prove the specs that used
  the assumption. The WaitGroup revert (`cases.md`, case 1) is the template.
- **Trusted code that is not irreducible (R2):** move the function to
  `translate` and regenerate.
  - For a missing feature, extend goose: a unit test in
    `goose/testdata/examples/unittest` or a semantics test in
    `testdata/examples/semantics`, then `go test -update-gold` and an audit of
    the gold diff.
  - Or add the missing rule to the right `*Semantics` class (`Golang/Defn`),
    with its lifting lemma in `Golang/Theory` and the Go-level spec (bounds →
    `Panic`). Adding a rule where the model is stuck today is the normal rung-3
    fix and is applied. Changing a behaviour that is already defined is the
    user's decision (R5).
  - Trust only the innermost irreducible callees, as one-line models where
    possible (`unsafe.String(unsafe.SliceData(b), n)` as `string(b)`), each with
    a docstring that names the irreducible construct.
  - Delete the old `.impl` and its `trusted` entry. Re-prove the old spec
    against the translated code; Go's own checks and panics come with it, so
    add the premises they need.
  - Rerun goose to show that only irreducible primitives remain trusted.
- **Infidelity (R4):** make the model do what Go does; if that is out of
  reach, make the model stuck/panicking there, say so in the docstring, and
  add the exclusion to every spec. Never leave a divergence silent.
- **Hand-edited generated code (R7):** regenerate and diff.
- **Changed semantics/adequacy (R5, R6):** changing a defined behaviour or an
  adequacy statement is the user's decision (a new rule for a stuck construct,
  under R2, is not); produce
  the fix as a proposal in the report (diff included) rather than applying
  it, unless the fix is a pure documentation update (R8).
- **Docs (R8):** update `README.md` "Model assumptions" / the relevant doc
  section and the docstring.

After fixing: `lake build` every touched module and its direct dependents,
`#print axioms` on the affected specs, `cd goose && go test ./...` when goose
changed, and rerun `etc/trusted-delta.py` on the result to show the trust
delta shrank. Report the before/after trust delta.
