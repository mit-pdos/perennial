#!/usr/bin/env bash
# Stop hook: once per new commit, remind an agent on an unlanded branch to /land.
#
# Fires (decision: block, which asks the model to continue once) when the
# checkout is on a branch other than the primary branch (etc/primary-branch),
# lean and master that has commits not on origin/<primary> or uncommitted
# tracked changes, and that state differs from the last time this hook fired.
# stop_hook_active guards against loops.
set -u
in=$(cat)
[ "$(printf '%s' "$in" | jq -r '.stop_hook_active // false')" = "true" ] && exit 0
cwd=$(printf '%s' "$in" | jq -r '.cwd // ""')
[ -d "$cwd" ] || cwd=$PWD
git -C "$cwd" rev-parse --git-dir >/dev/null 2>&1 || exit 0
br=$(git -C "$cwd" symbolic-ref --short -q HEAD) || exit 0
. "$(dirname "${BASH_SOURCE[0]}")/../primary-branch.sh"
primary=$(primary_branch "$(git -C "$cwd" rev-parse --show-toplevel)")
case "$br" in lean|master|"$primary") exit 0;; esac
git -C "$cwd" rev-parse -q --verify "origin/$primary" >/dev/null 2>&1 || exit 0
n=$(git -C "$cwd" rev-list --count "origin/$primary..HEAD")
dirty=$(git -C "$cwd" status --porcelain --untracked-files=no | wc -l | tr -d ' ')
[ "$n" = 0 ] && [ "$dirty" = 0 ] && exit 0
state="$(git -C "$cwd" rev-parse HEAD) $dirty"
f="$(git -C "$cwd" rev-parse --git-dir)/land-nudge"
[ -f "$f" ] && [ "$(cat "$f")" = "$state" ] && exit 0
printf '%s\n' "$state" > "$f"
extra=""; [ "$dirty" != 0 ] && extra=" and $dirty uncommitted tracked file(s)"
reason="Perennial workflow: branch '$br' has $n commit(s) not on origin/$primary$extra. If this work is finished, land it now with /land (commit, merge origin/$primary in, build, /review-trusted --fix, fast-forward $primary). If the work is unfinished or you are waiting on the user, say so briefly and end your turn again; this reminder fires once per new commit."
jq -n --arg r "$reason" '{decision:"block",reason:$r}'
