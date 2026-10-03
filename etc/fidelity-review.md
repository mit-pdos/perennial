# Fidelity review: Lean port vs Rocq (new goose)

Read-only review of branch `lean` (at a75654f30 plus working-tree changes) against
Rocq `master` (`new/`, `src/`). Scope and method: definitions and theorem
*statements* were compared with the Rocq source; proofs were not re-checked
beyond grepping for `sorry`/`axiom`/`opaque`.

## High

### H1. Hand-written `axiom`s silently drop the package `Assumptions` instance

Lean adds instance-implicit section `variable`s only to `theorem`s/`def`s that
use them; an `axiom` whose statement does not mention the variable does not get
it. As a result these axioms hold for *every* `go.Semantics`, regardless of
what `functions …`/`methods …` resolve to. Rocq's versions quantify over the
`Assumptions` class, which ties the resolved functions to the generated code.
The Lean axioms are strictly stronger than Rocq's and potentially inconsistent:
pick a semantics in which the function is stuck, and you get a WP for a stuck
program.

Confirmed with `#check @strings.wp_Fields`, whose binders are only
`[sem : go.Semantics]` with no `strings.Assumptions`.

| Lean | Rocq |
|---|---|
| `Perennial/Proof/strings.lean:97` `wp_Fields` | `new/proof/strings.v:60` (`∀ `{!strings.Assumptions}`) |
| `Perennial/Proof/go_etcd_io/etcd/api/v3/etcdserverpb.lean:41` `wp_InternalRaftRequest__Marshal`, `:48` `own_InternalRaftRequest_new_header` | `new/proof/go_etcd_io/etcd/api/v3/etcdserverpb.v:23,30` (Section has `package_sem`) |
| `Perennial/Proof/k8s_io/utils/third_party/forked/golang/btree.lean:55,65,80` `wp_BTree__Clone/Get/ReplaceOrInsert` (and the predicates at :46/:50, harmless) | `new/proof/k8s_io/.../btree.v` (Context has `btree.Assumptions`) |

**Fix:** put `include package_sem in` (for btree, `include … package_sem in`)
before each axiom, or bind `[strings.Assumptions]` explicitly. Then `#check`
each one. Also consider a lint that `#check`s every non-generated `axiom` for
the expected `Assumptions` binder. Generated `Perennial/Code/**` axioms are
goose placeholders whose counts match Rocq file by file; they were not affected.

## Medium

None found.

## Low

- **`proph_id`** (`Perennial/GooseLang/Lang.lean:29`, Rocq `lang.v:38`): `Nat`
  in Lean, `positive` in Rocq. Lean admits an extra id `0`; the zero value is
  `1` in both. This has no semantic effect but could be noted in the file header.
- **Disk FFI arguments** (`Perennial/GooseLang/Ffi/DiskFfi/Impl.lean`, Rocq
  `ffi/disk_ffi/impl.v`): Lean matches `#a`/`#l` (`into_val`) where Rocq
  matches `LitV (LitInt a)`/`LitV (LitLoc l)`. The two agree only if `into_val`
  on w64/loc is `LitV …`, which in Lean is abstract. This is documented. The
  Lean version is the more useful one.
- **`Bool` atomic specs** (`Perennial/Proof/sync/atomic.lean` ~1103, 1127:
  `wp_Bool__Load`, `wp_Bool__Store`, `wp_b32`) take an extra
  `is_pkg_init pkg_id.sync.atomic` precondition that Rocq (`atomic.v:863,872`)
  does not have. This is formally weaker but practically harmless. Fix: drop it.
- **`wp_Pointer__Load/Store`** add `▷` inside the AU precondition. This makes
  the specs stronger for clients, so it is fine; noted only as a divergence.
- **Ghost libraries** (`Perennial/Ghost/{GhostVar,GhostMap,DGhostVar,MonoList,SavedProp}.lean`)
  require `[Pos.Countable A]`, while Rocq takes any `A`. This is a restriction,
  not unsoundness. Document it in PORTING.md.
- **`wp_InternalMapForRange`** (`Perennial/Golang/Theory/Map.lean:321`, Rocq
  `map.v:24`) states its continuation via `is_go_step_pure` instead of
  `is_map_domain`. It is equivalent given the semantics field, and
  `wp_map_for_range` is faithful.
- **Rocq bugs ported faithfully** (report upstream):
  - `ArraySemantics.store_array` reads `#(W64 n)` instead of `#(W64 j)`
    (`Defn/Array.lean:49`, `array.v:45`).
  - `SliceSemantics.index_slice` builds `IndexRef` with arguments swapped.
  - `go.complex := "close"` typo (`predeclared.v:54`).
  - `index_array` uses `sint.nat`, so a negative index reads element 0.
- **Foundational `sorry`s that are also `Admitted` in Rocq:**
  `into_val_typed_array` (`Theory/Array.lean:200`), and the generated
  `TypedPointsto` for `notifyList` (`GeneratedProof/sync.lean`). It is a data
  instance, so `is_Cond` facts about that field rest on an arbitrary predicate,
  exactly as in Rocq. (`copyChecker` and `copyChecker.check` are no longer
  axiomatized: they are Lean-only trusted code in `TrustedCode/sync.lean`, with
  `copyChecker.t = loc`, so `wp_copyChecker__check` is proved.)
- **Unfinished work:** `Theory/Chan/AuSpec/ChanAuSend.lean:255` has `| _ => sorry`
  that is not admitted in Rocq; the directory is untracked and in progress. Not
  yet ported: `theory/chan.v`, `chan_au_recv.v`, `sync_proof/{waitgroup,waitgroup_join,rwmutex_guard}.v`.
  `PORTING.md` refers to `PORTING_STATUS.md`, which does not exist.
- **`uintptr` semantics (Lean addition, trusted).** Rocq declares only the type
  name `go.uintptr`. Lean adds `go.UintptrSemantics` (`Defn/Predeclared.lean`; it is a field
  `uintptr_semantics` of `PredeclaredSemantics`), plus `is_predeclared_uintptr` and
  `into_val_typed_uintptr`. Under the existing 64-bit-platform assumption, `uintptr` is
  `uint64`: the values are `w64`, the arithmetic and comparisons are unsigned, and the
  integer conversions are those of `uint64`. Pointer/`unsafe.Pointer` to/from `uintptr`
  conversions are not modelled, so they are stuck.
- **`sync_proof/once.lean`** fixes `HasLC.hasLC`, while the other files are
  generic over `hlc`. This is harmless.

## Checked and found faithful

- **Lang.lean vs `lang.v`:**
  - Syntax: `base_lit`, prim ops, `go_instruction` (same constructor set), the mutual `expr`/`val`/keyed-element/comm-clause types.
  - `ectx_item`/`fill_item` (right-to-left evaluation).
  - `subst` (including LiteralValue/SelectStmtClauses), `subst'`, `isFresh`, `state_init_heap`, `atomic_add_eval`.
  - `is_go_step`, `GoGlobalContext`/`GoLocalContext`, `ZeroVal` instances.
  - **`base_step` vs `base_trans`, case by case:**
    - Rec, Pair, Beta, If (true/false via `#b`), Fst, Snd, Fork, ArbitraryInt, Alloc.
    - StartRead/FinishRead (reader counts), Load (any `Reading n`), PrepareWrite (`Reading 0`), FinishStore (`is_Writing`), AtomicSwap and AtomicAdd (`Reading 0`).
    - CmpXchg: failure at any `Reading n`, success needs `Reading 0`; the return values match.
    - ExternalOp, GoInstruction (package state update), NewProph (fresh), ResolveProph, LiteralValue, SelectStmtClauses.
    - Everything else is stuck in both.
- **Locations.lean** vs `locations.v`.
- **NaHeap** vs `na_heap.v`: `lock_stateR = csum unit nat`, `to_na_heap`, pointsto and ctx. Block sizes and meta are dropped, as documented.
- **Lifting.lean** vs `lifting.v`:
  - `heap_pointsto` (= `⌜l ≠ null⌝ ∗ na_heap_pointsto`).
  - State interpretation: na_heap, ffi local/global, go_state auth, `go_lctx` equality, proph map.
  - Every wp lemma has an identical pre/postcondition: panic, ArbitraryInt, GoInstruction, fork, allocN_seq, alloc_untyped, load, prepare_write, finish_store, start_read, finish_read, atomic_swap, atomic_add, cmpxchg_fail/suc, new_proph, resolve_proph.
  - No `sorry`. `numLatersPerStep = 0` only reduces proof power and is documented.
- **Adequacy.lean:**
  - (Updated for time receipts.) The program logic is built for the step-bounded language `goose_ectxi_lang` (`BoundedLang.lean`: a fuel of Go-instruction steps, stutter at fuel 0); `goose_adequacy_blang N` concludes iris-lean `adequate NotStuck` for it, started with fuel `N - 1`. The time-receipt bound `N` is a parameter: `goose_adequacy N` (for every `N`) assumes a WP proved for receipt ghost state with `receipt_bound GF = N` (a hypothesis of `Hwp`, so the premises a proof makes about `N`, e.g. `N ≤ 2^48` for `idutil.wp_Generator__Next`, are discharged by the client's choice of `N`), and is about the real semantics `goose_real_ectxi_lang` (the former instance, unchanged `base_step`): for every real execution of `n < N` steps (`real_nsteps`), no thread is stuck (`real_not_stuck`) and a value of the main thread satisfies φ. The step bound is an explicit hypothesis; the transfer is the simulation `bounded_nsteps_of_real` plus `real_not_stuck_of_bounded`.
  - The hypothesis is a WP under *every* `heapGS` matching the initial `go_lctx`. This is meaningful and matches `goose_recv_adequacy_failstop` minus crashes.
  - `goose_invariance` is also faithful. There are no `sorry`s in iris-lean ProgramLogic.
- **Grove FFI** `is_grove_ffi_step`/`ffi_step`: identical, including stuttering.
- **Golang/Defn/\*\*:** every field of every semantics class, matched by script and then by hand:
  - CoreSemantics, CoreComparisonSemantics, GoSemanticsFunctions.
  - Integer, float, bool and string classes.
  - Array, slice, map, interface, chan, exception, loop, defer, pkg and lock.
  - Word ops are mapped correctly to BitVec: sdiv/srem, sshiftRight', and shift counts.
- **Golang/Theory:**
  - TypedPointsto and IntoValTyped(Underlying).
  - AtomicWps, PureWp/`tac_wp_pure_wp`.
  - `own_slice`/`own_slice_cap` and all slice specs.
  - `own_map` and the map specs.
  - `is_lock`/`own_lock` specs.
  - loop, exception, defer, predeclared, assume and array lemmas.
- **Ghost/\*\*** (own, ghost_var, ghost_map, dghost_var, mono_nat, mono_list, saved_prop/pred, token, auth_set, tok_set): the statements match.
- **sync_proof** (mutex, sema, cond, once, rwmutex as currently on disk) and the sync/atomic specs: the invariants and specs match.
- **Generated code:**
  - The `Perennial/Code` file set equals `new/code` (83 files) and all 1731 `*ⁱᵐᵖˡ` definitions exist.
  - Per-function operation counts match, and the remaining mismatches are artifacts of the comparison script.
  - Hand-compared bodies: std_core, sync `Once`, quorum `JointConfig.String`.
  - `GeneratedProof/sync` matches `new/generatedproof/sync.v`.
  - `Code/**` axiom counts equal Rocq's in every file.
