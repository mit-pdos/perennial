#!/usr/bin/env bash
# One-time per clone: run the versioned git hooks in etc/githooks (no commits on
# lean/master, no direct pushes to them). The setting lives in the clone's
# config, so every worktree of the clone inherits it. Idempotent; etc/land.sh
# and the Claude Code session hook run it too.
set -e
root=$(git rev-parse --show-toplevel)
chmod +x "$root"/etc/githooks/* 2>/dev/null || true
cur=$(git config --get core.hooksPath || true)
if [ "$cur" = "etc/githooks" ]; then
  echo "perennial: git hooks already active (core.hooksPath = etc/githooks)"
else
  git config core.hooksPath etc/githooks
  echo "perennial: git hooks activated (core.hooksPath = etc/githooks)${cur:+; was: $cur}"
fi
