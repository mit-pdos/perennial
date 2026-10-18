#!/usr/bin/env bash
# PreToolUse(Bash) hook: keep the primary branch (etc/primary-branch; `lean` if
# there is none), `lean` and `master` clean.
#
# Denies, with a reason the model sees:
#   * git commit / merge / rebase / cherry-pick / revert / am / pull while the
#     checkout the command runs in is on one of them;
#   * git push whose refspec targets one of them, or any force push.
# etc/land.sh is the one sanctioned way to move the primary branch: commands that invoke it
# pass. Everything else passes untouched (no output).
set -u
in=$(cat)
cmd=$(printf '%s' "$in" | jq -r '.tool_input.command // ""' 2>/dev/null) || exit 0
[ -n "$cmd" ] || exit 0
case "$cmd" in *git*) ;; *) exit 0;; esac
case "$cmd" in *etc/land.sh*) exit 0;; esac

deny() {
  jq -n --arg r "$1" '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}'
  exit 0
}
c=$(printf '%s' "$cmd" | tr '\n' ' ')
. "$(dirname "${BASH_SOURCE[0]}")/../primary-branch.sh"
primary=$(primary_branch "${CLAUDE_PROJECT_DIR:-.}")
# the branch name as an extended regular expression matching it literally
primary_re=$(printf '%s' "$primary" | sed 's/[][\\.*^$+?(){}|]/\\&/g')
case "$primary" in lean|master) protected="lean or master";; *) protected="$primary, lean or master";; esac

# --- pushes that would move a protected branch directly ---------------------
# `git [global options] <subcommand>`: global options may take arguments (-C dir),
# so match the subcommand anywhere in the same shell segment after `git`.
if printf '%s' "$c" | grep -Eq '(^|[;&|[:space:]])git[[:space:]]+([^;&|]*[[:space:]])?push([[:space:]]|$)'; then
  if printf '%s' "$c" | grep -Eq -- '(--force|--force-with-lease|(^|[[:space:]])-f([[:space:]]|$)|[[:space:]]\+[[:alnum:]])'; then
    deny "Force pushes are not allowed in this repository."
  fi
  if printf '%s' "$c" | grep -Eq "(^|[[:space:]:+])(refs/heads/)?(lean|master|$primary_re)([[:space:]]|\$)"; then
    deny "Do not push to $protected directly. Land the branch with /land (it merges origin/$primary in, builds, runs /review-trusted --fix, then fast-forwards $primary through etc/land.sh)."
  fi
fi

# --- history-changing commands while on a protected branch -------------------
if printf '%s' "$c" | grep -Eq '(^|[;&|[:space:]])git[[:space:]]+([^;&|]*[[:space:]])?(commit|merge|rebase|cherry-pick|revert|am|pull|push)([[:space:]]|$)'; then
  dir=$(printf '%s' "$in" | jq -r '.cwd // ""')
  d2=$(printf '%s' "$c" | grep -oE '(^|[;&|[:space:]])cd[[:space:]]+[^[:space:];&|]+' | head -1 | sed -E 's/^[;&|[:space:]]*cd[[:space:]]+//')
  [ -n "$d2" ] && dir=$d2
  d3=$(printf '%s' "$c" | grep -oE 'git[[:space:]]+-C[[:space:]]+[^[:space:]]+' | head -1 | sed -E 's/git[[:space:]]+-C[[:space:]]+//')
  [ -n "$d3" ] && dir=$d3
  [ -d "$dir" ] || dir=$PWD
  br=$(git -C "$dir" symbolic-ref --short -q HEAD 2>/dev/null) || exit 0
  case "$br" in
    lean|master|"$primary")
      deny "This checkout ($dir) is on '$br'. Do not commit or merge on it: work on a branch (EnterWorktree, or 'git switch -c <topic>' in a worktree of your own) and finish with /land, which reviews the change and fast-forwards $primary. See CLAUDE.md, Workflow.";;
  esac
fi
exit 0
