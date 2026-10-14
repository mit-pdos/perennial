# Notes for agents

For every agent working in this repository, whatever the tool (Claude Code
reads this file through `CLAUDE.md`; Codex and others read it directly).

* `lean` is the primary branch. Read `README.md` (design decisions,
  conventions) and `docs/` before working on proofs.
* Do not consult the Rocq sources (`master`, `new/`, `src/`, or any checkout
  of them such as `../etcd-grove-rr`). They are frozen and out of date, and
  the Lean statements are authoritative. Comments and docs should describe
  the Lean development on its own terms, without comparisons to Rocq.
* Build a module with `lake build Perennial.Path.To.Module` (elan is in
  `~/.elan/bin`). To check whether a theorem is fully proved, run
  `#print axioms` on it and look for `sorryAx`.

## Workflow: branch, review, land

`lean` only moves by fast-forward to a branch that has been built and
reviewed. Git hooks enforce the branch discipline for every tool; the landing
script enforces the review.

1. **Once per clone, activate the hooks:** `etc/setup-hooks.sh`. It sets
   `core.hooksPath` to `etc/githooks` (worktrees inherit it); the hooks refuse
   commits on `lean`/`master` and pushes to them. At the start of a session,
   run it if `git config core.hooksPath` does not print `etc/githooks`.
2. **Never commit on `lean`.** Work on a branch: a worktree
   (`git worktree add ../perennial-<topic> -b <topic> origin/lean`, or your
   tool's worktree feature) or `git switch -c <topic>`. Check the base:
   GitHub's default branch is `master`, so a worktree created from "the
   default branch" is on the wrong history; `git reset --hard origin/lean`
   if `git merge-base --is-ancestor HEAD origin/lean` fails.
3. **When the work is done, land it** by following
   `.agents/skills/land/SKILL.md` (Claude Code: `/land`; Codex: the `land`
   skill): commit everything; `etc/land.sh prepare` (merges `origin/lean`
   into the branch, builds the changed modules, runs goose's tests if goose
   changed); the trusted-base review of `.agents/skills/review-trusted/SKILL.md`
   in fix mode, committing its fixes, which records an OK verdict with
   `etc/land.sh mark-reviewed`; then `etc/land.sh push`, which refuses
   without that record and fast-forwards `origin/lean`. Nothing else pushes
   to `lean`: no `git push origin lean`, no `HEAD:lean`, no force pushes, no
   `--no-verify`. Once landed, delete the branch: its worktree, the local
   branch (`git branch -d`) and its remote copy if it was pushed
   (`git push origin --delete <branch>`); only branches you created.
4. **Changes to the trusted base** (the Go semantics in `Perennial/GooseLang`
   and `Perennial/Golang/Defn`, `goose/`, `Perennial/TrustedCode`, the `.toml`
   trust lists, adequacy statements, any `assume`/`axiom`/`sorry` outside
   `Perennial/Proof`) deserve the review early, not only at landing:
   `etc/trusted-delta.py [commit | A..B]` prints what a change adds to the
   trusted base, and `.agents/skills/review-trusted/SKILL.md` says how to
   judge it (the trust ladder: prove > translate real Go > extend the
   semantics or goose > a Go model under `goose/model` > hand-written
   GooseLang > assume > axiom; model assumptions must be unreachable, not
   unlikely; a model may be less defined than Go, never more; goose emits
   each operation annotated with its operands' Go types, and any choice that
   depends on what a type is, such as signedness, width or a type parameter's
   instantiation, is made by the Lean semantics, not by goose).
5. **Fixing a bug in the semantics or goose** follows
   `.agents/skills/fix-semantics/SKILL.md` (Claude Code: `/fix-semantics`):
   one bug at a time, the smallest change that completes an existing scheme
   rather than adding a carve-out, and a plan the user signs off before any
   trusted file changes. Its `cases.md` holds the user's past decisions.

`.claude/settings.json` adds Claude Code conveniences on top (a reminder to
land at the end of a turn, a check of a new worktree's base); nothing in the
workflow depends on them.
