# Notes for agents

* `lean` is the primary branch. Read `README.md` (design decisions,
  conventions) and `docs/` before working on proofs.
* Do not consult the Rocq sources (`master`, `new/`, `src/`, or any checkout
  of them such as `../etcd-grove-rr`). They are frozen and out of date, and
  the Lean statements are authoritative. Comments and docs should describe
  the Lean development on its own terms, without comparisons to Rocq.
* Build a module with `lake build Perennial.Path.To.Module` (elan is in
  `~/.elan/bin`). To check whether a theorem is fully proved, run
  `#print axioms` on it and look for `sorryAx`.
* Changes to the trusted base (Go semantics in `Perennial/GooseLang` and
  `Perennial/Golang/Defn`, `goose/`, `Perennial/TrustedCode`, the `.toml`
  trust lists, adequacy statements, any `assume`/`axiom`/`sorry` outside
  `Perennial/Proof`) are reviewed with the `review-trusted` skill
  (`/review-trusted [commit | A..B] [--fix]`, `.claude/skills/review-trusted/`)
  before they are committed or merged. `etc/trusted-delta.py` prints the trust
  delta of a change.
