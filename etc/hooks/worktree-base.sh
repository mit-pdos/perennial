#!/usr/bin/env bash
# PostToolUse(EnterWorktree) hook: a new worktree must start from the primary
# branch's history (etc/primary-branch; `lean` if there is none).
#
# EnterWorktree with worktree.baseRef = fresh branches from origin/<GitHub
# default branch>, which for this repository is master, not the primary branch. The project
# settings use baseRef = head (the local HEAD, normally the primary branch); this hook
# checks the result and, when the worktree sits exactly at origin/master,
# resets it to origin/$primary. It reports the base either way.
set -u
in=$(cat)
d=$(printf '%s' "$in" | grep -oE '/[^"[:space:]]*/\.claude/worktrees/[^"[:space:]/]+' | head -1)
[ -n "$d" ] && [ -d "$d" ] || exit 0
git -C "$d" rev-parse --git-dir >/dev/null 2>&1 || exit 0
# the primary branch as the session's checkout names it: the new worktree may lack
# etc/primary-branch (when it was created at origin/master, the case handled here)
. "$(dirname "${BASH_SOURCE[0]}")/../primary-branch.sh"
src=${CLAUDE_PROJECT_DIR:-}
[ -n "$src" ] && [ -d "$src" ] || src=$(printf '%s' "$in" | jq -r '.cwd // ""' 2>/dev/null)
[ -n "$src" ] && [ -d "$src" ] || src=$PWD
primary=$(primary_branch "$(git -C "$src" rev-parse --show-toplevel 2>/dev/null || echo "$src")")
timeout 30 git -C "$d" fetch -q origin "$primary" master >/dev/null 2>&1 || true
head=$(git -C "$d" rev-parse HEAD)
om=$(git -C "$d" rev-parse -q --verify origin/master 2>/dev/null || true)
ol=$(git -C "$d" rev-parse -q --verify "origin/$primary" 2>/dev/null || true)
[ -n "$ol" ] || exit 0
short=$(git -C "$d" rev-parse --short "origin/$primary")
if [ "$head" = "$om" ] && [ -z "$(git -C "$d" status --porcelain --untracked-files=no)" ]; then
  git -C "$d" reset -q --hard "origin/$primary"
  msg="Worktree $d was created from origin/master (the GitHub default branch); it has been reset to origin/$primary ($short). $primary is the primary branch. Finish the work with /land."
elif git -C "$d" merge-base --is-ancestor "origin/$primary" "$head" 2>/dev/null; then
  msg="Worktree $d is at or ahead of origin/$primary ($short). Finish the work with /land."
elif git -C "$d" merge-base --is-ancestor "$head" "origin/$primary" 2>/dev/null; then
  behind=$(git -C "$d" rev-list --count "$head..origin/$primary")
  msg="Worktree $d is on $primary's history, $behind commit(s) behind origin/$primary ($short); /land merges origin/$primary in before landing. Finish the work with /land."
else
  msg="WARNING: worktree $d is not on $primary's history (HEAD $(git -C "$d" rev-parse --short HEAD)). Before working, run: git reset --hard origin/$primary"
fi
jq -n --arg m "$msg" '{hookSpecificOutput:{hookEventName:"PostToolUse",additionalContext:$m}}'
