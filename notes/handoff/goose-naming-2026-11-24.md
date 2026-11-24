# Handoff: goose naming (2026-11-24)

Goal: replace perennial#640 ("goose: root references to named value types", marshtompsxd) with a
**uniform** naming scheme for the Lean names of Go identifiers: one fixed rule per kind of name, no
context-dependent or blanket qualification, readable output, collision-free (Upamanyu). This is a
trusted change (translator): it lands only after an independent `review-trusted` and Upamanyu's
approval. Don't comment on #640 before it lands; on landing, close #640 as superseded with the
landed commit and the test names below (Upamanyu OK'd closing it).

## The scheme (goose/README.md "Lean names of Go identifiers"; goose/glang/syntax.go header)

- struct field `F` -> projection `F'` (unchanged)
- type parameter `P` -> `P₀` (value type `P₀'`); function-local constant `c` -> `c₁`
- every other Go name `X` (type, function, global, method) -> `X`, or `X''` when reserved
  (`GoName`): Lean keywords (Upamanyu: keywords use the same rule, `Type''`, `def''`), framework /
  Iris / Lean names the output refers to unqualified, names declared under a namespace (`ty`,
  `impl`, `mk`, `eq_def`...), the generated code's binders
- generated names derived from a Go name `x` -> `tag'x` (`MemberName`): `get'F`, `set'F`,
  `unfold'M`, `ptr_unfold'M`, `instance'T`, `import'p`, `equals_unfold'T`, `typed_pointsto'T`,
  `into_val_typed'T`, `access_load'T'F`, `access_store'T'F`, `deferred'F` (recovering variant;
  its Go string stays `F'deferred`)
- package namespace: path components, a component that is a framework namespace (`go`, `chan`,
  `map`, `slice`, `pkg_id`, ...; `glang.FrameworkNamespaces`) -> `c''` (`NamespacePath`; module
  names keep the file path, `LeanModulePath`). `go/token` -> `go''.token`.
- references to other packages and proofgen's references to its own package: rooted
  (`_root_.Perennial.<ns>.X`)
- guillemets only as a lexing fallback (non-ASCII; Lean 4.34 rejects `名`, `λ`; goose quotes every
  non-ASCII name); goose's encoded names (`«struct#h»`, `«_#0'»`, `init.«0»`) and keyword
  package-path components (`pkg_id.«unsafe»`) keep their quoting.
- Collision argument: Go identifiers have no `'` and no subscript digits, so the forms are
  disjoint; every bare name the output uses is reserved; every relative dotted reference starts
  with a reserved name, a Go name of the package, or a framework namespace (which no package
  namespace contains). `goose/names_reserved_test.go` (`TestOutputNamesReserved`) checks this over
  goose's golds and freshly generated proofgen output of the test packages (mutation-checked).

## Reviews and fixes

First independent review (of 927e439a3): renaming OK, but the collision claim was false. Fixed:
(1) silent pre-existing capture of framework value types by package types (`type GoSlice ...`
used as a field type; trusted TypeAssumptions misstated the type) -> reserved + the test;
(2) unreserved framework names -> reserved, completeness by test, not by hand list;
(3) type-parameter binders capturing package types -> `P₀`; (4) member-name collisions
(field `unfold` vs method `get`, methods `ptr_f`/`f`) -> `tag'x`; (5) #640's test spec/proof/Link
ported; (6) `rec`, `fun_cases_unfolding`; keywords `X''`, `λ` -> `«λ''»`.

Second independent review (of fe7bd4685): BLOCK (filed as perennial#700): relative framework
references (`go.len` etc.) captured by a package at path `.../go` declaring `len`. Fixed by the
namespace rule above. Decision (overnight): the coordinator's preferred refusal would refuse two
real translated packages (etcd-grove `Net` `go/token`, `github.com/prometheus/client_model/go`;
checked exhaustively over Perennial + all 11 etcd-grove roots), and rooting every framework
reference (`_root_.Perennial.go.len`, ~110k places) is #640's readability cost; the `c''` rename is
the same conflict rule as Go names. Notes fixed: proofgen own-package refs rooted; `deferred'F`;
local constants `c₁`; test reads fresh proofgen output and checks dotted first components.

Next: a **third independent review-trusted** of the head below, then Upamanyu's approval, then
`etc/land.sh mark-reviewed` / push (coordinator), then close #640.

## #640 regression test

- `goose/testdata/examples/semantics/local_type_names.go` (#640's), its spec and `semantics_auto`
  proof `Perennial/Spec|Proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics/testLocalTypeNameShadow.lean`,
  the Link entry, and the Go test `TestLocalTypeNameShadow` (goose/cmd/test_gen). Passes (builds)
  on this branch.
- Fails before: branch `goose-names-640-before` (77ad1db22) = origin/lean 2cadd30c2 + the test file,
  translated with origin/lean's translator: `IntOrString.TypeAssumptions.set_Type` takes
  `(y : Type')` inside namespace `IntOrString` (the field). TODO: build
  `Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.semantics` there and record
  the error (the VM build was stopped at the wrap-up).
- Also `goose/testdata/examples/unittest/names` (one case per capture class).

## Branches

| repo | branch | head | state | for |
|---|---|---|---|---|
| Perennial | `goose-names-guillemet` | this commit (after de3860a0b) | full build of all 2453 modules OK at de3860a0b (merged origin/lean 52d62e83c); goose tests OK | the change to land |
| Perennial | `goose-names-guillemet-at-pin` | 7f436638a | full build 2311 modules OK | demo only: same change on etcd-grove's pin b3f2fc485 |
| Perennial | `goose-names-640-before` | 77ad1db22 | not built | evidence: #640 fails before |
| etcd-grove | `goose-names/2026-11-24` | ffffa08ea4 | pinned to 7f436638a; previous round (83ebfea13f) built fully (27779 jobs); this round's full VM build was stopped at the wrap-up (the round before it failed only on gen-init imports, fixed in ffffa08ea4) | demo: regenerated translations + references, renames only (1120 files, 0 unexplained at 83ebfea13f) |

Renames-only check: every changed generated line maps to one of the rules (setter binder `F'`->`y`,
`X'`->`X''`, `«X»`->`X''`, tags, binders, rooted refs, `go''`), apart from new test content.
Generated bytes shrink slightly (etcd-grove 40.08 MB -> 39.98 MB).

## Next steps

1. Build etcd-grove `goose-names/2026-11-24` (ffffa08ea4) fully on the VM; fix leftovers.
2. Build `goose-names-640-before` semantics module; record the #640 error.
3. Third independent review-trusted of `goose-names-guillemet`; fix findings; rebuild.
4. Upamanyu's approval; land via Perennial `etc/land.sh` (mark-reviewed, push by coordinator); close
   #640 as superseded (commit + test names); file nothing else.
5. etcd-grove pin bump onto the landed commit: rerun `etc/goose.py`, rewrite references (qualified
   tokens naming renamed generated declarations or class members; projections through
   `[x : ...Assumptions]` variables; `@! F'deferred`), rerun gen-init/gen-raft-tla/gen-specs-pkginit/
   kitgen/copy-part; hand-written spec names (`zap.Int'.spec`) stay.

## Pitfalls

- etcd-grove scripts that map namespaces to paths/modules must strip `''` from framework components
  (`gen-init.py` `dirof`/`modof`, `gen-specs-pkginit.py` `fpath`/`modpath`, regexes allow `'`).
- Hand-written macros building member names from strings (antithesis `odm`/`smu`), hard-coded names
  in `gen-init.py` (`sync.atomic.Bool''`), docstrings.
- Hand-written classes mirroring goose shapes keep their own names (etcd-grove `TrustedCode/os.lean`,
  KvNet ManualProof `net`, Perennial `Golang/Theory/Test.lean`).
- `Perennial/Code/strconv.lean` differs by Go-toolchain unicode drift when regenerating: restore it.
- /tmp is a small shared tmpfs: set `GOTMPDIR`/`TMPDIR` elsewhere for goose tests.
