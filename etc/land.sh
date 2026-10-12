#!/usr/bin/env bash
# Land the current branch on `lean`: the mechanical half of the `land` skill
# (.agents/skills/land/SKILL.md). This script is the only sanctioned way to
# move `lean`: the git hooks in etc/githooks (activated by etc/setup-hooks.sh)
# refuse commits on lean and pushes to it, except the one push this script
# makes with PERENNIAL_LAND=1 after the branch has been built and reviewed.
#
# Usage: etc/land.sh prepare [--no-build]
#            merge origin/lean into the branch, check the proofs' layout
#            (etc/gen-link.py --check), build the touched Lean modules,
#            run goose's tests if goose changed
#        etc/land.sh mark-reviewed
#            record that /review-trusted passed on the branch's current changes
#            (the review skill runs this itself when its verdict is OK)
#        etc/land.sh push [--no-build]
#            prepare again, check the review record still matches the branch's
#            changes, then fast-forward origin/lean to HEAD
#        etc/land.sh status
#
# The review record is the patch-id of `git diff origin/lean...HEAD`, kept in
# the branch's git dir, so a merge of new origin/lean commits that does not
# disturb the branch's own hunks keeps it valid, while any edit to the branch's
# changes after the review invalidates it.
set -u
export PATH="$HOME/.elan/bin:$PATH"

die() { echo "land: $*" >&2; exit 1; }
cmd=${1:-status}; shift || true
NOBUILD=0
for a in "$@"; do case "$a" in --no-build) NOBUILD=1;; *) die "unknown option $a";; esac; done

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || die "not in a git checkout"
cd "$ROOT" || exit 1
GITDIR=$(git rev-parse --git-dir)
MARK="$GITDIR/review-trusted.ok"
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

build_changed() {
  # the layout of the program proofs, and their generated Link.lean files
  python3 etc/gen-link.py --check || die "etc/gen-link.py --check failed (run etc/gen-link.py, or fix the layout)"
  [ "$NOBUILD" = 1 ] && { echo "land: build skipped (--no-build)"; return 0; }
  mapfile -t files < <(git diff --name-only origin/lean...HEAD)
  lean=(); goose=0
  for f in "${files[@]}"; do
    case "$f" in
      Perennial/*.lean|Perennial.lean) [ -f "$f" ] && lean+=("$f");;
      goose/*) goose=1;;
    esac
  done
  if [ ${#lean[@]} -gt 0 ]; then
    if [ ! -e .lake/packages ]; then
      die "no .lake/packages here, so nothing can be built. Share the main checkout's packages (ln -s /path/to/main/.lake/packages .lake/packages, copy .lake/build; see MEMORY: disk is tight), or run with --no-build and say so in the report."
    fi
    echo "land: lake build ${#lean[@]} changed module(s)"
    lake build "${lean[@]}" || die "lake build failed"
    # Perennial.lean's closure is what CI builds; check the root still elaborates when framework files changed
    case " ${lean[*]} " in *" Perennial/Golang/"*|*" Perennial/GooseLang/"*|*" Perennial/Std/"*|*" Perennial/Algebra/"*|*" Perennial/Ghost/"*)
      echo "land: framework files changed; lake build Perennial"
      lake build Perennial || die "lake build Perennial failed";;
    esac
  fi
  if [ "$goose" = 1 ]; then
    echo "land: goose changed; go test ./goose/..."
    (cd "$ROOT" && go test ./goose/...) || die "goose tests failed"
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
}

case "$cmd" in
  status) show_status;;
  prepare)
    check_branch; fetch_and_merge; build_changed
    echo "land: prepared. Next: /review-trusted --fix, then etc/land.sh push";;
  mark-reviewed)
    check_branch
    git rev-parse -q --verify origin/lean >/dev/null || git fetch -q origin lean
    pid=$(patch_id); [ -n "$pid" ] || die "no changes to record"
    printf '%s\n' "$pid" > "$MARK"
    echo "land: review recorded for $BRANCH ($pid)";;
  push)
    check_branch; fetch_and_merge
    [ -f "$MARK" ] || die "no review record: run /review-trusted --fix (it records an OK verdict with etc/land.sh mark-reviewed)"
    [ "$(cat "$MARK")" = "$(patch_id)" ] || die "the branch's changes differ from what /review-trusted passed; rerun /review-trusted --fix"
    build_changed
    echo "land: fast-forwarding origin/lean to $(git rev-parse --short HEAD)"
    if ! PERENNIAL_LAND=1 git push origin HEAD:refs/heads/lean; then
      die "push rejected (origin/lean moved?); rerun etc/land.sh push"
    fi
    rm -f "$MARK"
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
  *) die "usage: etc/land.sh prepare|mark-reviewed|push|status [--no-build]";;
esac
