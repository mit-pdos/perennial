# Differential testing of a semantics: how short must tests be?

Notes on testing a model of Go (GooseLang) against real Go with short,
feature-local programs. The theorems are in `Perennial/DiffTesting/`:
`Locality.lean` (footprints, separation, minimal witnesses are connected) and
`Bounds.lean` (no masking, length bounds, the lower bound). Statements below
name the Lean theorems; everything named is proved (`#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`).

## The setting

Two semantics `sem₁` (reference, real Go) and `sem₂` (the model) share a
state `L → V` and give each instruction a transition relation. A test runs a
program from `s₀` under both and compares the sets of final states. Each
instruction has a footprint, the locations it touches, and both semantics
*respect* the footprints (`Respects`): a step leaves the rest of the state
alone and does not depend on it.

## What is proved

1. **Locality.** Instructions split along disjoint footprints run as a
   product (`run_product`); a divergence is a divergence of one part
   (`diverges_split`); a minimal divergent program is footprint-connected
   (`minimal_connected`); agreement on connected programs is agreement on
   all programs (`connected_tests_complete`).
2. **No masking.** A divergent part stays divergent when instructions of
   other components are mixed in, unless they block
   (`diverges_of_part`, `diverges_of_part_total`). So testing whole real
   functions that use `defer`/`recover` among unrelated code exposes every
   bug that their `defer`/`recover` projection exposes. Instructions of the
   *same* component can mask, which is why the test generator, not the test
   context, has to be exhaustive within the component.
3. **Length is bounded by an abstraction of the component.** Before its last
   instruction, a minimal witness is run identically by both semantics, and
   the reference semantics' state sets after its proper prefixes are pairwise
   distinct (`minimal_reference_distinct`). More generally, if an abstraction
   `α` is *adequate* (state sets with equal `α` admit the same divergent
   continuations) and takes `N` values, every minimal witness has at most `N`
   instructions (`minimal_length_le`, `short_witness`).
4. **No constant bound in general.** For every `n` there are two semantics on
   a single location, both respecting footprints, whose minimal witness has
   `n + 1` instructions: a counter the model wraps at `n`
   (`no_uniform_bound`). The 64-bit overflow bug that needs 2^64 increments
   is this example.
5. **The frame hypothesis is needed on both sides** (`frame_hypothesis_needed`):
   a model step that writes outside its footprint gives a minimal witness that
   is not connected.

So "every bug shows within 7 instructions" is never a theorem about all
semantics. It is a theorem *per feature*, with 7 replaced by the size of an
adequate abstraction of that feature's state: concrete bounds have to be
computed from the two semantics, or assumed from evidence.

## Where a concrete `N` comes from

Three established shapes of argument give small adequate abstractions:

* **Finite control.** If a feature's relevant state is a finite machine, the
  classic distinguishing-experiment bounds apply. Moore (1956, Thm. 6, 7):
  distinguishable states of an `n`-state machine are told apart by an input
  of length `n − 1`, and two `n`-state machines by one of length `2n − 1`;
  both tight. Our `minimal_length_le` is the same pigeonhole, over the
  reference's prefix states.
* **Data independence and symmetry.** If the semantics treat values or
  goroutine identities uniformly, states that differ by a renaming are not
  distinguishable, and only as many distinct values or threads as the
  instructions can compare are needed. The parameterized-verification cutoffs
  are the model: Emerson and Kahlon (CADE 2000) reduce guarded systems of any
  size to `|U| + 1` copies, `|U|` the local states of one process.
* **Bounded inspection of unbounded state.** A rule that looks only at the top
  `k` entries of a stack (the defer stack, the call stack) makes "the top `k`
  entries, plus whether there are more" adequate *for that rule*.

The catch is the reference side. An abstraction is adequate only if it is
adequate for *real Go*, whose implementation has hidden states the
specification does not mention. Chow's W-method (TSE 1978) is the precise
form: tests complete for an `n`-state specification are complete against an
implementation only with a bound `m` on its states, and test length grows
with `m − n`. Go's implementation thresholds are exactly such hidden states,
each a code path a program reaches only past a size:

| feature | threshold | where |
|---|---|---|
| `defer` | open-coded only with ≤ 8 defers, none in loops, and returns × defers ≤ 15 | `cmd/compile/internal/walk/walk.go` `maxOpenDefers = 8`; `ssagen/ssa.go` |
| `append` | growth 2× below 256 elements, then ≈1.25×; zero-size elements special | `runtime/slice.go` `nextslicecap` |
| maps (Swiss tables, Go 1.24+) | 8 slots per group, ≤ 8 entries in one group, table split at 1024 | `internal/runtime/maps` |
| map literals | > 25 entries compiled as a loop | `walk/complit.go` |
| `switch` | binary search from 4 cases; jump tables from 8 (5 for type switches) | `walk/switch.go` |
| interfaces | integers < 256 boxed without allocation | `runtime/iface.go` `staticuint64s` |
| allocation | zero-size → `&zerobase`; tiny allocator < 16 B; small objects ≤ 32 KB | `runtime/malloc.go` |
| goroutines | initial stack 2048 B (deep recursion copies stacks) | `runtime/stack.go` |

So the adequate abstraction for `defer` must count up to at least 9 defers,
and a bound for it is at least 9, whatever the model looks like. The
practical recipe: per feature, `N` = the model's abstract states plus the
implementation's thresholds plus a margin, read from the Go source
(white-box), then test exhaustively up to `N`.

## Cost of exhaustive per-feature testing

Locality is what makes this affordable: enumeration is per component, over
that component's instructions only, never over the product of features.
With `k` instruction forms in a feature and bound `N`, there are about
`k^N` programs: `5^7 ≈ 7.8·10^4`, `5^9 ≈ 2·10^6`, `6^9 ≈ 10^7`. No masking
lets each enumerated program also be embedded in larger real code without
losing what it exposes.

## Empirical evidence on depth

The theorems say *where* bugs live and *what* bounds their size; how small
the sizes are in practice is empirical. The evidence is consistently small:

* **Concurrency.** Lu, Park, Seo, Zhou, ASPLOS 2008 (105 bugs): 92% "can be
  reliably triggered by enforcing certain orders among no more than 4 memory
  accesses"; 96% involve ≤ 2 threads; 66% of non-deadlock bugs one variable.
  Musuvathi and Qadeer, PLDI 2007: every new bug "exposed by an execution
  with at most 2 preempting context switches" (the technical report's
  abstract counts "7 previously unknown bugs", a likely source of a
  remembered "7"). Burckhardt et al., PCT, ASPLOS 2010: a bug of *depth* `d`
  (ordering constraints needed) is found in one run with probability at least
  `1/(n·k^(d−1))` for `n` threads and `k` steps, tight, and all the bugs they
  studied have depth 1 or 2. Thomson, Donaldson, Betts (PPoPP 2014, TOPC
  2016): 44 of 49 benchmark bugs within preemption bound 2. Yuan et al., OSDI
  2014 (198 production failures): 90% need ≤ 3 input events, 98% ≤ 3 nodes,
  77% reproducible by a unit test.
* **Feature interaction.** Kuhn, Wallace, Gallo, TSE 2004: every fault in
  their four systems was triggered by an interaction of at most 6
  parameters, most by 1-3. The analogue here is the number of components a
  connected witness spans.
* **Small scope.** Jackson (Alloy): "most bugs can be demonstrated with small
  counterexamples". Marinov et al., MIT-LCS-TR-921 (2003): exhaustive testing
  in scopes 4-7 kills almost all mutants, but SearchTree needed scope 6, one
  more than coverage required: the needed scope is set by the fault, which
  is the threshold point above.
* **Compilers and semantics.** Sun et al., ISSTA 2016: bug-report tests have
  median 21 (GCC) and 16 (LLVM) lines, 80% under 45. C-Reduce (PLDI 2012):
  median reduced wrong-code test 192 bytes. Hriţcu et al. (ICFP 2013):
  shrunk counterexamples of 4 instructions. Dasgupta et al. (PLDI 2019)
  validated an x86-64 semantics instruction by instruction and found
  manual and tool bugs with single instructions. Klein et al. (POPL 2012):
  random generation missed 20 of 30 reduction rules, an argument for
  targeted per-rule small programs over undirected random ones.

## Open directions

* **A depth-robust bound, analogous to PCT.** Points 2 and 3 above give a
  bound on exhaustive testing. A probabilistic guarantee for random
  generation needs an assumption PCT makes and this theory does not: that the
  bug shows in every program containing the witness pattern (as PCT's
  ordering constraints do in every schedule satisfying them). The theorems
  show this holds for cross-component insertions; within a component it is
  the open assumption.
* **Partial observation.** Tests see outputs, not whole states. The Moore
  bound `2n − 1` for observed outputs replaces the bound for full states and
  would follow from the same pigeonhole on pairs of observational classes.
* **Proving adequacy for the model.** For the GooseLang model, footprints
  (`Respects`) and an adequate abstraction per feature can be proved in Lean;
  only the reference side (what Go touches, and its thresholds) stays an
  assumption, read off the specification and the Go source.
