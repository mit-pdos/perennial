---
name: fix-semantics
description: Fix an unsoundness or incompleteness in Perennial's Go semantics (Perennial/GooseLang, Perennial/Golang/Defn) or the goose translator, the simple way - by completing a uniform scheme rather than adding a carve-out - with a plan the user signs off before any trusted change. Use when a proof is stuck on a construct the semantics or goose does not handle, when the model is more defined than Go, when goose's translation differs from Go's behaviour, or when asked to fix a semantics/translator bug.
argument-hint: "<symptom or failing module>"
---

# Fix a semantics or translator bug, simply

The trusted base must stay small and uniform: every special case in goose or
the semantics is something a fuzzer has to know about, a reviewer has to check,
and a proof has to step through. Bug-fixing loops tend to accrete carve-outs. This skill is for fixing one bug at a time with the
smallest change that makes the scheme more uniform, not less.

The calibration lives in two files next to this one:

* `examples.md`: decisions the user made. Authoritative.
* `candidate-examples.md`: past commits labelled by an agent, not yet reviewed.
  Useful as examples of shapes, never as precedent over `examples.md`.

Read both before proposing anything.

## Procedure

1. **Classify the symptom.** One of:
   * *incomplete*: the model is stuck where Go runs (a missing rule, an
     untranslated construct);
   * *unsound*: the model is more defined than Go, or has a behaviour Go does
     not (a wrong rule, a translation that evaluates something twice, in the
     wrong order, or with the wrong value);
   * *not a semantics bug*: the proof is wrong, or the spec is.
   Write a minimal Go witness. For unsoundness, run it in Go and say what Go
   does.

2. **Find the scheme the fix belongs to.** Locate the existing rule, goose
   function or translation pattern that handles the closest construct (e.g.
   slices for strings, `$s` binding for operands). The fix should make the
   construct an instance of that scheme. If no scheme fits, say so: that is a
   design question for the user, not something to patch.

3. **Propose a plan and stop.** Never change trusted files before the user
   signs off. The plan states:
   * the change, as a diff or the exact rule;
   * its cost: changed/new goose branches, new semantics rules, new negative
     tests, new trusted models, lines in the trusted base;
   * the closest case in `examples.md` and how this one matches its shape;
   * the sibling rules or translations with the same defect, which the plan
     includes (look for them: the same lookup, test or binding elsewhere);
   * what it leaves out (unrelated fixes are split into separate items).
   A cost of more than one new branch/rule/negative test, or any branch that
   depends on context, is a red flag: say why it is unavoidable or propose
   leaving the construct stuck instead.

4. **Implement exactly the plan.** No narrative comments in the trusted base:
   a rule that is self-evidently Go's behaviour needs none. Match the
   surrounding code's form (naming, `⤳[under]`, `Panic` messages).

5. **Regenerate and check.**
   * goose changed: add a semantics test (`goose/testdata/examples/semantics`,
     `func test*() bool`, then `go generate ./goose/cmd/test_gen`), update
     gold files (`go test ./goose -update-gold`), run `go test ./goose/...`
     and `go vet`. Rebuild goose/proofgen into a private GOPATH (not
     `go install`, the machine is shared) and regenerate Perennial/Code with
     `etc/update-goose-new.py`; for std/primitive/marshal whose sources are not
     checked out, apply only the hunks the change implies and check them
     against a regeneration from the nearest available source.
   * Build: `etc/lean-ci.sh -q`; no new failures. Proofs that break should
     break because the model changed in the intended way.
   * `etc/trusted-delta.py HEAD`: the signals should be exactly the planned
     ones.

6. **Record the case.** Append the decision to `examples.md` (format at its top),
   including what the user rejected or changed in the plan and their words.
   If it came from `candidate-examples.md`, move it.

## Principles (provisional, distilled from examples.md; the user may edit)

* **Complete a uniform scheme; don't add a case.** A new rule should look
  like a sibling of an existing one (Case 1). A new goose branch keyed on a
  syntactic context ("inside a deferred literal", "when parenthesized", "when
  the operands have no call") is almost always wrong.
* **Compositional translation.** The translation of an expression depends only
  on the translations of its subexpressions and its own Go types. Each operand
  is translated once and referred to by name (Case 2).
* **Stuck is an acceptable answer.** A construct the semantics cannot give
  Go's meaning simply should stay stuck or be refused by goose by a general
  rule (an unsupported construct), not given a special meaning. Run-time panics
  are stuck; proofs show they are unreachable.
* **Type-dependent choices are the semantics' job.** Goose emits operations
  annotated with their operands' Go types; signedness, width, and type
  parameter instantiation are decided by Lean rules, not by goose branches.
* **One logical bug per change.** Split unrelated fixes; each gets its own
  plan and case. Sibling rules with the same defect are one bug and are fixed
  together (Case 9).
* **No narrative in the trusted base.** No comments justifying a rule or
  recounting a bug; the commit message and `examples.md` carry the history.

## Relation to other skills

`review-trusted` grades a finished change for soundness and added trust; this
skill produces the change. Run `review-trusted` on the result before landing.
Landing on `lean` is the `land` skill, only when the user asks.
