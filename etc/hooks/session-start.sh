#!/usr/bin/env bash
# SessionStart hook: say where this session stands in the branch workflow.
# stdout is added to the model's context.
set -u
in=$(cat)
cwd=$(printf '%s' "$in" | jq -r '.cwd // ""' 2>/dev/null)
[ -d "$cwd" ] || cwd=$PWD
git -C "$cwd" rev-parse --git-dir >/dev/null 2>&1 || exit 0
br=$(git -C "$cwd" symbolic-ref --short -q HEAD 2>/dev/null) || exit 0
case "$br" in
  lean|master)
    echo "Perennial workflow: this checkout is on '$br'. Do not commit here (a hook denies it). Work on a branch: EnterWorktree, or 'git switch -c <topic>' in a worktree of your own. When the work is done, run /land: it merges origin/lean in, builds what changed, runs /review-trusted --fix, and fast-forwards lean. See CLAUDE.md, Workflow.";;
  *)
    n=""
    if git -C "$cwd" rev-parse -q --verify origin/lean >/dev/null 2>&1; then
      n=" ($(git -C "$cwd" rev-list --count origin/lean..HEAD) commit(s) ahead of origin/lean)"
    fi
    echo "Perennial workflow: on branch '$br'$n. When the work is done, run /land (it reviews with /review-trusted and fast-forwards lean). See CLAUDE.md, Workflow.";;
esac
