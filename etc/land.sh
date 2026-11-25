#!/usr/bin/env bash
# Land the current branch on `lean`: the mechanical half of the `land` skill
# (.agents/skills/land/SKILL.md). This script is the only sanctioned way to
# move `lean`: the git hooks in etc/githooks (activated by etc/setup-hooks.sh)
# refuse commits on lean and pushes to it, except the one push this script
# makes with PERENNIAL_LAND=1 after the branch has been built and reviewed.
#
# Usage: etc/land.sh prepare [--no-build]
#            merge origin/lean into the branch, check the proofs' layout
#            (etc/gen-link.py --check) and the native tactic library's module
#            list (etc/meta-lib.py --check), build the touched Lean modules
#            (and, if framework files changed, Perennial and the regression
#            tests Perennial/ProgramLogic/*Test.lean), run goose's tests if
#            goose changed; print the Go model overlays' `MODEL:` marker count
#            (etc/model-deviations.py; visibility only, no gate)
#        etc/land.sh verdict-path
#            print the path of the review's verdict file (in the branch's git dir)
#        etc/land.sh mark-reviewed
#            record that /review-trusted passed on the branch's current changes:
#            checks the verdict file (Verdict: OK, a result for every criterion of
#            .agents/skills/review-trusted/CRITERIA.md, none FAIL, and a Witness line
#            when the witness gate fires); the review skill runs this itself
#        etc/land.sh witness-check [A..B]
#            dry run of push's witness gate on A..B (default origin/lean..HEAD):
#            report, build and push nothing
#        etc/land.sh push [--no-build]
#            prepare again, check the review record still matches the branch's
#            changes, run the witness gate, then fast-forward origin/lean to HEAD
#        etc/land.sh status
#
# The witness gate (criterion 1 of CRITERIA.md; `etc/trusted-delta.py --witness-gate`):
# when the branch adds to the model of Go (an added tier-0 line with a step rule, a
# semantics class or instance, a GoInstruction constructor, an assume, an angelic exit,
# an axiom, an extension's semantics, a trusted `.impl`, or a Go model overlay's table,
# replaced names or choice points), push refuses unless the branch's commits carry
#     Semantics-Witness: <goose/testdata/examples/**.go | Perennial/ProgramLogic/*Test.lean
#                         | Perennial/Proof/**.lean>     (exists at HEAD)
#     Real-use: <repo>:<package>.<function>
# or `Semantics-Witness: none (narrowing: <reason>)` for a change that only removes trust
# or makes the model stuck in more places (refused if it adds an assume, an angelic exit,
# an axiom, a GoInstruction constructor or a model overlay). prepare and push exercise
# each witness: a Lean one is built, a goose example is gold-checked by `go test
# ./goose/...` (examples/semantics also run in Go), and its Lean proofs' Link built.
#
# The review record is the patch-id of `git diff origin/lean...HEAD`, kept in
# the branch's git dir, so a merge of new origin/lean commits that does not
# disturb the branch's own hunks keeps it valid, while any edit to the branch's
# changes after the review invalidates it.
set -u
export PATH="$HOME/.elan/bin:$PATH"
# go (for goose's tests and modelcheck) is often installed outside the PATH
# a non-interactive shell gets; use the first usual install location that has it
for d in "$HOME/.local/go/bin" "/usr/local/go/bin" "$HOME/go/bin" "$HOME/sdk/go/bin"; do
  [ -x "$d/go" ] && { export PATH="$d:$PATH"; break; }
done

die() { echo "land: $*" >&2; exit 1; }
need_go() { command -v go >/dev/null 2>&1 || die "go not found (looked on PATH and in ~/.local/go/bin, /usr/local/go/bin); install go or put it on PATH"; }
cmd=${1:-status}; shift || true
NOBUILD=0; ARGS=()
for a in "$@"; do case "$a" in --no-build) NOBUILD=1;; -*) die "unknown option $a";; *) ARGS+=("$a");; esac; done

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || die "not in a git checkout"
cd "$ROOT" || exit 1
GITDIR=$(git rev-parse --git-dir)
MARK="$GITDIR/review-trusted.ok"
VERDICT="$GITDIR/review-trusted.verdict"
CRITERIA=.agents/skills/review-trusted/CRITERIA.md
BRANCH=$(git symbolic-ref --short -q HEAD) || die "detached HEAD; check out a branch"
# the git hooks are part of the workflow: activate them if this clone has not
[ "$(git config --get core.hooksPath)" = "etc/githooks" ] || bash etc/setup-hooks.sh

patch_id() { git diff origin/lean...HEAD | git patch-id --stable | cut -d' ' -f1; }

check_branch() {
  case "$BRANCH" in
    lean|master) die "on '$BRANCH'. Work on a branch (EnterWorktree, or git switch -c <topic>) and land it from there.";;
  esac
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    git status --short --untracked-files=no >&2
    die "uncommitted changes; commit them first"
  fi
}

fetch_and_merge() {
  git fetch -q origin lean || die "git fetch origin lean failed"
  if ! git merge-base --is-ancestor origin/lean HEAD; then
    echo "land: merging origin/lean ($(git rev-parse --short origin/lean)) into $BRANCH"
    if ! git merge --no-edit origin/lean; then
      die "merge conflicts with origin/lean; resolve them, commit, and rerun"
    fi
  fi
  if git diff --quiet origin/lean...HEAD; then
    die "nothing to land: $BRANCH has no changes against origin/lean"
  fi
}

# the witness gate (criterion 1): exit status of etc/trusted-delta.py --witness-gate
witness_gate() { python3 etc/trusted-delta.py --witness-gate "${1:-origin/lean..HEAD}"; }

# check the review's verdict file before recording it
check_verdict() {
  [ -f "$VERDICT" ] || die "no verdict file $VERDICT: the review writes it (.agents/skills/review-trusted/SKILL.md, step 7)"
  grep -m1 -v '^[[:space:]]*$' "$VERDICT" | grep -qE '^Verdict: OK\b' \
    || die "$VERDICT: its first line is not 'Verdict: OK'; an open BLOCK or REWORK is not recorded"
  local n bad=0
  for n in $(grep -oE '^[0-9]+\. \*\*' "$CRITERIA" | grep -oE '^[0-9]+'); do
    grep -qE "^C$n: (PASS|NOTE|N/A)\b" "$VERDICT" || {
      if grep -qE "^C$n: FAIL\b" "$VERDICT"; then echo "land: $VERDICT: criterion $n FAILs" >&2
      else echo "land: $VERDICT: no 'C$n: PASS|NOTE|FAIL|N/A <evidence>' line" >&2; fi
      bad=1; }
  done
  [ "$bad" = 0 ] || die "the verdict does not pass every criterion of $CRITERIA"
  if ! witness_gate | grep -q '^witness gate: no semantics addition'; then
    grep -qE '^Witness: (needed|narrowing)\b' "$VERDICT" \
      || die "$VERDICT: the witness gate fires, and there is no 'Witness: needed <evidence>' (or 'Witness: narrowing <evidence>') line (SKILL.md, step 5)"
  fi
}

# the witnesses named by the branch's commits, as `<kind> <path>` lines
witness_paths() { python3 etc/trusted-delta.py --witness-paths origin/lean..HEAD; }

build_changed() {
  # the layout of the program proofs, and their generated Link.lean files
  python3 etc/gen-link.py --check || die "etc/gen-link.py --check failed (run etc/gen-link.py, or fix the layout)"
  # the native-code library of the proof automation (lakefile.toml, PerennialMeta.lean)
  python3 etc/meta-lib.py --check || die "etc/meta-lib.py --check failed (run etc/meta-lib.py and commit)"
  [ "$NOBUILD" = 1 ] && { echo "land: build skipped (--no-build)"; return 0; }
  mapfile -t files < <(git diff --name-only origin/lean...HEAD)
  lean=(); goose=0; code=0; semtest=0
  for f in "${files[@]}"; do
    case "$f" in
      Perennial/Code/*) code=1;;&
      Perennial/*.lean|Perennial.lean) [ -f "$f" ] && lean+=("$f");;
      goose/*) goose=1;;
    esac
  done
  # the semantics witnesses (criterion 1) are exercised whether or not the branch changed them
  local kind w d
  while read -r kind w; do
    [ -n "$w" ] || continue
    echo "land: semantics witness $w ($kind)"
    case "$kind" in
      lean) case " ${lean[*]} " in *" $w "*) ;; *) lean+=("$w");; esac;;
      go-example)
        goose=1
        case "$w" in goose/testdata/examples/semantics/*) semtest=1;; esac
        d=$(dirname "${w#goose/testdata/examples/}")
        for f in "Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/$d/Link.lean" \
                 "Perennial/Code/github_com/mit_pdos/perennial/goose/testdata/examples/$d.lean"; do
          if [ -f "$f" ]; then case " ${lean[*]} " in *" $f "*) ;; *) lean+=("$f");; esac; break; fi
        done;;
    esac
  done < <(witness_paths)
  if [ ${#lean[@]} -gt 0 ]; then
    if [ ! -e .lake/packages ]; then
      die "no .lake/packages here, so nothing can be built. Share the main checkout's packages (ln -s /path/to/main/.lake/packages .lake/packages, copy .lake/build; see MEMORY: disk is tight), or run with --no-build and say so in the report."
    fi
    echo "land: lake build ${#lean[@]} changed module(s)"
    lake build "${lean[@]}" || die "lake build failed"
    # Perennial.lean's closure is what CI builds; check the root still elaborates when framework files changed
    case " ${lean[*]} " in *" Perennial/Golang/"*|*" Perennial/GooseLang/"*|*" Perennial/Std/"*|*" Perennial/Algebra/"*|*" Perennial/Ghost/"*)
      echo "land: framework files changed; lake build Perennial"
      lake build Perennial || die "lake build Perennial failed"
      # the framework's regression tests (Perennial/ProgramLogic/*Test.lean) are
      # outside Perennial.lean's closure, so nothing else rebuilds them when the
      # framework under them changes
      mapfile -t tests < <(ls Perennial/ProgramLogic/*Test.lean 2>/dev/null)
      if [ ${#tests[@]} -gt 0 ]; then
        echo "land: lake build ${#tests[@]} regression test(s) (Perennial/ProgramLogic/*Test.lean)"
        lake build "${tests[@]}" || die "a regression test failed (Perennial/ProgramLogic/*Test.lean)"
      fi;;
    esac
  fi
  if [ "$goose" = 1 ]; then
    need_go; echo "land: goose changed; go test ./goose/..."
    (cd "$ROOT" && go test ./goose/...) || die "goose tests failed"
  fi
  if [ "$semtest" = 1 ]; then
    need_go; echo "land: a witness is a semantics test; go test ./semantics/ (Go itself returns true)"
    (cd "$ROOT/goose/testdata/examples" && go test ./semantics/) || die "the semantics tests failed in Go"
  fi
  # the guard of docs/design/unsafe-memory.md (R4, section 5): no translated
  # package may contain code the semantics models incorrectly
  if [ "$goose" = 1 ] || [ "$code" = 1 ]; then
    need_go; echo "land: goose or its translations changed; etc/update-goose-new.py --modelcheck"
    python3 etc/update-goose-new.py --modelcheck --std-lib --models --goose-examples \
      || die "modelcheck found code the semantics models incorrectly (docs/design/unsafe-memory.md, R4)"
  fi
}

show_status() {
  echo "branch: $BRANCH"
  git rev-parse -q --verify origin/lean >/dev/null || { echo "origin/lean: (not fetched)"; return; }
  echo "ahead of origin/lean: $(git rev-list --count origin/lean..HEAD) commit(s); behind: $(git rev-list --count HEAD..origin/lean)"
  echo "uncommitted (tracked): $(git status --porcelain --untracked-files=no | wc -l) file(s)"
  if [ -f "$MARK" ]; then
    if [ "$(cat "$MARK")" = "$(patch_id)" ]; then echo "review-trusted: OK for the current changes"
    else echo "review-trusted: recorded, but the branch's changes moved since; rerun /review-trusted"; fi
  else echo "review-trusted: not recorded; run /review-trusted"; fi
  if [ -f "$VERDICT" ]; then echo "verdict file: $VERDICT ($(grep -m1 -v '^[[:space:]]*$' "$VERDICT"))"; fi
}

case "$cmd" in
  status) show_status;;
  prepare)
    check_branch; fetch_and_merge; build_changed
    witness_gate || echo "land: WARNING: push will refuse until the witness gate passes (above)"
    # the Go models' departures from the real Go source, a trust-base measure (no gate);
    # etcd-grove's models/ too when ETCD_GROVE_DIR is set
    python3 etc/model-deviations.py || echo "land: WARNING: etc/model-deviations.py failed"
    echo "land: prepared. Next: /review-trusted --fix (it checks every criterion of $CRITERIA" \
         "and writes its verdict to $VERDICT), then etc/land.sh push";;
  verdict-path) echo "$VERDICT";;
  witness-check)
    git rev-parse -q --verify origin/lean >/dev/null || git fetch -q origin lean
    witness_gate "${ARGS[0]:-origin/lean..HEAD}"; st=$?
    [ -n "${ARGS[0]:-}" ] || witness_paths | sed 's/^/land: would exercise witness: /'
    exit $st;;
  mark-reviewed)
    check_branch
    git rev-parse -q --verify origin/lean >/dev/null || git fetch -q origin lean
    pid=$(patch_id); [ -n "$pid" ] || die "no changes to record"
    check_verdict
    printf '%s\n' "$pid" > "$MARK"
    { grep -v '^Patch-id: ' "$VERDICT"; echo "Patch-id: $pid"; } > "$VERDICT.tmp" && mv "$VERDICT.tmp" "$VERDICT"
    echo "land: review recorded for $BRANCH ($pid)";;
  push)
    check_branch; fetch_and_merge
    [ -f "$MARK" ] || die "no review record: run /review-trusted --fix (it records an OK verdict with etc/land.sh mark-reviewed)"
    [ "$(cat "$MARK")" = "$(patch_id)" ] || die "the branch's changes differ from what /review-trusted passed; rerun /review-trusted --fix"
    grep -qx "Patch-id: $(patch_id)" "$VERDICT" 2>/dev/null || die "the verdict file $VERDICT is missing or of other changes; rerun /review-trusted --fix"
    echo "land: review verdict: $(grep -m1 -v '^[[:space:]]*$' "$VERDICT")"
    witness_gate || die "the witness gate refuses (criterion 1 of $CRITERIA; see above)"
    build_changed
    echo "land: fast-forwarding origin/lean to $(git rev-parse --short HEAD)"
    if ! PERENNIAL_LAND=1 git push origin HEAD:refs/heads/lean; then
      die "push rejected (origin/lean moved?); rerun etc/land.sh push"
    fi
    rm -f "$MARK" "$VERDICT"
    # update a local `lean` checkout if there is a clean one
    while read -r path _ br; do
      case "$br" in "[lean]")
        if [ -z "$(git -C "$path" status --porcelain --untracked-files=no)" ] && git -C "$path" merge -q --ff-only origin/lean 2>/dev/null; then
          echo "land: local lean at $path fast-forwarded"
        else
          echo "land: local lean at $path not updated (dirty or diverged): git -C $path merge --ff-only origin/lean"
        fi;;
      esac
    done < <(git worktree list)
    echo "land: $BRANCH landed on lean as $(git rev-parse --short HEAD)";;
  *) die "usage: etc/land.sh prepare|verdict-path|mark-reviewed|witness-check [A..B]|push|status [--no-build]";;
esac
