#!/usr/bin/env bash
# PostToolUse(EnterWorktree) hook: a new worktree must start from lean's history.
#
# EnterWorktree with worktree.baseRef = fresh branches from origin/<GitHub
# default branch>, which for this repository is master, not lean. The project
# settings use baseRef = head (the local HEAD, normally lean); this hook
# checks the result and, when the worktree sits exactly at origin/master,
# resets it to origin/lean. It reports the base either way.
set -u
in=$(cat)
d=$(printf '%s' "$in" | grep -oE '/[^"[:space:]]*/\.claude/worktrees/[^"[:space:]/]+' | head -1)
[ -n "$d" ] && [ -d "$d" ] || exit 0
git -C "$d" rev-parse --git-dir >/dev/null 2>&1 || exit 0
timeout 30 git -C "$d" fetch -q origin lean master >/dev/null 2>&1 || true
head=$(git -C "$d" rev-parse HEAD)
om=$(git -C "$d" rev-parse -q --verify origin/master 2>/dev/null || true)
ol=$(git -C "$d" rev-parse -q --verify origin/lean 2>/dev/null || true)
[ -n "$ol" ] || exit 0
short=$(git -C "$d" rev-parse --short origin/lean)
if [ "$head" = "$om" ] && [ -z "$(git -C "$d" status --porcelain --untracked-files=no)" ]; then
  git -C "$d" reset -q --hard origin/lean
  msg="Worktree $d was created from origin/master (the GitHub default branch); it has been reset to origin/lean ($short). lean is the primary branch. Finish the work with /land."
elif git -C "$d" merge-base --is-ancestor origin/lean "$head" 2>/dev/null; then
  msg="Worktree $d is at or ahead of origin/lean ($short). Finish the work with /land."
elif git -C "$d" merge-base --is-ancestor "$head" origin/lean 2>/dev/null; then
  behind=$(git -C "$d" rev-list --count "$head..origin/lean")
  msg="Worktree $d is on lean's history, $behind commit(s) behind origin/lean ($short); /land merges origin/lean in before landing. Finish the work with /land."
else
  msg="WARNING: worktree $d is not on lean's history (HEAD $(git -C "$d" rev-parse --short HEAD)). Before working, run: git reset --hard origin/lean"
fi
jq -n --arg m "$msg" '{hookSpecificOutput:{hookEventName:"PostToolUse",additionalContext:$m}}'
