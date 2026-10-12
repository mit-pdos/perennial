---
name: land
description: Finish a piece of work on Perennial and put it on `lean`. Commits the branch, merges origin/lean into it, builds what changed, runs /review-trusted --fix, and fast-forwards lean through etc/land.sh. Use when work on a branch or worktree is complete and should reach lean, or when asked to land, merge, ship or push a branch to lean. The only sanctioned way to move lean.
argument-hint: "[--no-build]"
---

# Land the current branch on `lean`

`lean` only ever moves by fast-forward to a branch that has been built and
reviewed. Hooks deny `git commit` on lean and `git push` to lean; the path is
this skill, whose mechanical half is `etc/land.sh`.

## Procedure

1. **Be on a branch with everything committed.** If the checkout is on
   `lean`, stop: the work should have been done on a branch (`EnterWorktree`,
   or `git switch -c <topic>`); move the uncommitted changes to one before
   continuing. Commit all intended work with proper messages (`git status`;
   do not sweep unrelated files in). If the user asked for a pull request or
   to hold the work, open a draft PR or stop here instead of landing.

2. **Prepare.** From the repo root:

   ```
   etc/land.sh prepare [--no-build]
   ```

   It fetches and merges `origin/lean` into the branch (resolve conflicts,
   commit, rerun), `lake build`s the changed modules (and `Perennial` when
   framework files changed), and runs `go test ./goose/...` if goose changed.
   A build failure is yours to fix: fix, commit, rerun. `--no-build` is for a
   checkout with no `.lake` (say so in the report; the memory note on sharing
   `.lake/packages` says how to get one).

3. **Review.** Run `/review-trusted --fix` (no target: it reviews the branch
   against the merge base with `origin/lean`). Fix what it finds and commit
   the fixes. When its verdict is OK, or there is no trusted change, it
   records that with `etc/land.sh mark-reviewed`. A BLOCK you cannot fix
   means the work does not land: report it and stop.

4. **Push.**

   ```
   etc/land.sh push [--no-build]
   ```

   It prepares again (origin/lean may have moved), checks that the recorded
   review still matches the branch's changes (if not, back to step 3),
   rebuilds, and fast-forwards `origin/lean` to HEAD. A rejected push means
   origin/lean moved during the build: rerun the command.

5. **Delete the branch.** Once it has landed, the branch is merged into
   `lean`: delete it. Remove its worktree if it had one (`git worktree remove
   <path>`, from another checkout), the local branch (`git branch -d
   <branch>`, which refuses a branch that is not merged), and its remote copy
   if it was ever pushed (`git push origin --delete <branch>`). Delete only
   branches you created.

6. **Report**: the landed commit, what the review found and fixed, anything
   skipped (`--no-build`), and the branch name (deleted).

## Rules

- Never `git push origin lean`, `git push HEAD:lean`, force-push, or merge
  into a local `lean` by hand. The script is the path, and the hook denies
  the rest.
- Do not land with `--no-build` silently, and never with an open BLOCK.
- One piece of work per landing: if the branch has drifted into two unrelated
  changes, land them as they are but say so; do not split history by hand.
