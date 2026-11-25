# Criteria for a trusted change

The user's criteria for any change to the trusted base: semantics (step rules,
`GoInstruction`s, semantics classes, extensions), laws and axioms, `TrustedCode`
models, Go model overlays, and goose translation changes. The review
(`SKILL.md`) reports every criterion for every change as `PASS`, `NOTE`, `FAIL`
or `N/A`, with evidence; `etc/land.sh mark-reviewed` refuses a verdict without
a line for each, or with a `FAIL`. Where a rule of `SKILL.md` already says how
to judge it, the item names the rule and does not repeat it.

1. **A witness for every semantics addition.** The change names a minimal Go
   program that needs the addition (trailer `Semantics-Witness:`, a goose
   example or Lean test land.sh exercises) and a real translated function with
   the same complication (trailer `Real-use: <repo>:<package>.<function>`), and
   shows that existing lemmas do not suffice: the proof attempt with what
   Perennial already has, and the search for a lemma that covers it.
   *Why:* an addition a proof did not need is trust nobody should have to
   review (perennial#703: `structFieldRef_not_null`, already given by
   `typedPointsto_not_null`). `etc/land.sh push` checks the trailers; the review
   checks the need (SKILL.md, step 5).
2. **Translate the real Go when the semantics supports it.** A trusted model
   only where goose and the semantics cannot express the code.
   *Why:* a model is trust; the translation is checked. (R1, R2.)
3. **No package-specific instructions in core GooseLang.** A new
   `GoInstruction` or step rule must be a general Go primitive (as the
   reflection primitives are); package behaviour goes in a trusted model or a
   Go model overlay.
   *Why:* every special case in the core is a carve-out every proof and
   reviewer must know about (`AsAssign` for `errors.As` is the precedent not to
   repeat).
4. **Follow the Go spec, not gc.** Where gc differs from the spec, the model
   follows the spec and the divergence is a known limitation
   (`docs/KNOWN_LIMITATIONS.md`); where the spec leaves a choice, the model
   keeps every choice (R5) or takes a documented platform assumption
   (`README.md`, "Platform").
   *Why:* the proof is about Go programs, not one compiler's accidents.
5. **State interpretations are determined by the state; adequacy stays
   minimal.** No modes, flags or ghost updates inside a state interpretation;
   no program-specific or proof-engineering resources in a trusted adequacy
   statement: the program's proof allocates its own ghost state.
   *Why:* everything in adequacy is in every client's trusted base. (R6.)
6. **Prove code rather than add laws.** Where the code can be proved, no new
   axiom or axiomatized law; to retire an axiom, strengthen the boundary spec
   that creates the state rather than add a law about it.
   *Why:* an axiom is checked by nothing. (R1 rung 7, R10.)
7. **Goose changes are as trusted as Lean rules.** A translator change gets the
   scrutiny of a semantics rule (R5, R8); when one construct needs a
   conversion, add the whole family (every source and target type of the same
   kind) rather than the one case.
   *Why:* the translator is the semantics of Go source; a uniform family is
   simpler to trust than a list of cases.
8. **Avoid modes and flags in specs and proofs unless necessary.** Prefer
   facts about the state alone.
   *Why:* a mode is extra state every client must track and every reviewer
   must check is set honestly.
9. **A soundness gap no proof reaches gets a documented open issue, not a
   fix.** Record it (a GitHub issue, `docs/KNOWN_LIMITATIONS.md`) and change
   nothing until a proof needs it; a gap a proof reaches is fixed
   (`fix-semantics`).
   *Why:* speculative fixes add trust and review load for no verified program.
10. **Trusted files' docs are concise technical text.** A docstring says what
    the rule or model does and where it departs from Go, and nothing about
    history or how it came about; longer reasoning goes in `docs/` (design
    notes) or the commit message.
    *Why:* the trusted base is read by every reviewer; narrative hides the
    claim. (R8; `fix-semantics`, "No narrative in the trusted base".)
11. **No concrete bounds in specs.** Specs use `maxAddr` or abstract facts,
    never `2^47` or another literal limit; bounds belong in the step rules.
    *Why:* a literal in a spec ties every client to one platform constant and
    duplicates the semantics.
12. **Uniform translation naming.** One rule per kind of name (functions,
    methods, types, anonymous structs, quoted identifiers `«»`); no name that
    depends on context and no blanket qualification.
    *Why:* a reader and a proof must predict a name from the Go source alone.
    (`goose/README.md`; `README.md`, "Conventions".)
13. **Every decision of an extension's trusted semantics has an evidence
    example.** A Go test in a package beside the extension's Go side says the
    decision, the Lean names, the behaviour allowed or excluded, and the
    evidence (measured, documented with a citation, or assumed); a change to
    the semantics adds or updates its example in the same commit.
    *Why:* an extension models an outside system the Go spec does not
    describe; the example is the only check that the model matches it.
