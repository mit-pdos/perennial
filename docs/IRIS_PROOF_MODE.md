# The Iris Proof Mode in Lean (iris-lean)

The Lean port uses [iris-lean](https://github.com/leanprover-community/iris-lean)'s
proof mode (`.lake/packages/iris/Iris/Iris/ProofMode/Tactics/*.lean`; upstream
docs in `.lake/packages/iris/Iris/docs/tactics.md`). This page describes its
syntax as used in Perennial, with Rocq IPM equivalents for readers who know them. Lean blocks are
copied from [`TutorialExamples.lean`](TutorialExamples.lean) (checked with
`lake env lean docs/TutorialExamples.lean`).

Main differences from Rocq at a glance:

* tactic names are lowercase: `iIntros` → `iintro`, `iDestruct` → `icases`;
* hypothesis names and patterns are **not strings**: `iintro ⟨HP, HQ⟩` rather
  than `iIntros "[HP HQ]"`;
* conjunction/existential patterns use `⟨…⟩`, disjunction `(… | …)`;
* `_` is an anonymous hypothesis and `-` drops one (Rocq: `?` and `_`);
* specialization uses `$$`: `iapply H $$ HP [$HQ]` (Rocq `iApply ("H" with "HP [$HQ]")`);
* Lean binders in patterns are written `%x` (Rocq `(x)`);
* `iAssert` and `iPoseProof` are both `ihave`.

## 1. The goal display

```
Hlen : vs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len     -- Lean (pure) context
⊢
  □Hpkg : isPkgInit pkg                               -- intuitionistic (□)
  ∗HΦ : s ↦* vs -∗ Φ #(sum_w64 vs)                      -- spatial (∗)
  ∗Hs : s ↦* vs
  ⊢ Φ #(sum_w64 vs)                                      -- the Iris goal
```

Intuitionistic hypotheses are marked `□`, spatial ones `∗`. Pure facts live in
the ordinary Lean context. Most tactics start the proof mode themselves on a goal
`P ⊢ Q` or `⊢ Q` (`istart`/`istop` do it explicitly). `IProp GF` is affine, so
spatial hypotheses can be dropped (in a generic `BI` you need `[BIAffine PROP]`).

## 2. Patterns

### Cases patterns (`icases`, `iintro`, `imod`, `iinv`, `wp_start as`, `ihave`)

| Pattern | Meaning | Rocq |
|:--|:--|:--|
| `H` | name the hypothesis | `"H"` |
| `_` | anonymous hypothesis | `"?"` |
| `-` | drop it | `"_"` |
| `$` | frame it against the goal | `"$"` |
| `⟨p₁, p₂, …, pₙ⟩` | destruct `∗`/`∧`/`∃` (nested to the right) | `"[p1 p2]"`, `"(p1 & p2 & p3)"` |
| `(p₁ \| p₂)` | destruct `∨` (one goal each); parentheses optional inside `⟨⟩` | `"[p1 \| p2]"` |
| `%x` / `%h` | move to the Lean context: an existential witness or a pure fact; any `rcases` pattern, e.g. `%⟨h1, h2⟩`, `%rfl` | `"%h"`, `(x)`, `"%->"` |
| `#p` | move to the intuitionistic context | `"#p"` |
| `∗p` | move to the spatial context | `"-#p"` |
| `>p` | eliminate a modality (`▷` of a timeless prop, `\|==>`, `\|={E}=>`) | `">p"` |

### Intro patterns (`iintro`)

All cases patterns, plus:

| Pattern | Meaning | Rocq |
|:--|:--|:--|
| `%x` | introduce a `∀` or a pure premise | `(x)`, `"%x"` |
| `!>` | introduce a modality (`imodintro`) | `"!>"` |
| `//` | try `itrivial` | `"//"` |
| `/=` | simplify | `"/="` |
| `*`, `**` | introduce all `∀`s / all `∀`s, pure arrows and wands | `"*"`, `"**"` |
| `!%` | introduce a pure goal and leave the proof mode | |
| `{H₁ $H₂}` | clear (or, with `$`, frame) the selected hypotheses | `"{H1} {$H2}"` |

Example: `iintro %Φ ⟨Hs, %Hbound⟩ HΦ`.

### Selection patterns (`iclear`, `iframe`, `irevert`, `icombine`, `iloeb generalizing`)

`H` (a hypothesis), `%h` (a Lean hypothesis), `%` (all pure), `#` (all
intuitionistic), `∗` (all spatial — the Unicode `∗`, not `*`). Rocq
`iFrame "∗#"` is `iframe ∗ #`.

### Specialization patterns (after `$$`)

| Pattern | Meaning | Rocq |
|:--|:--|:--|
| `H` | use hypothesis `H` for the premise | `"H"` |
| `%t` | instantiate a `∀` with the Lean term `t` | `$! t` |
| `[H₁ H₂]` | new goal for the premise with exactly these spatial hypotheses | `"[H1 H2]"` |
| `[$H₁ H₂]` | ... framing `H₁` into it | `"[$H1 H2]"` |
| `[-H₁]` | ... with all spatial hypotheses except `H₁` | `"[-H1]"` |
| `[]` | new goal with no spatial hypotheses | `"[]"` |
| `[$]` | solve the premise by framing | `"[$]"` |
| `[> H]`, `[> $]` | the premise may use the goal's modality | `"[> H]"` |
| `[# $H]`, `[# $]` | persistent premise: framed hypotheses are not consumed | `"[#]"` |
| `[H //]` | also try `itrivial` on the new goal | `"[H //]"` |
| `[H] as G` | name the generated goal (not inside `wp_apply`) | |
| `(H $$ spats)` | specialize `H` first, then use it | `("H" with "...")` |

### Proof mode terms

A *pmTerm* is `t $$ spat₁ … spatₙ`, where `t` is an Iris hypothesis or a Lean
term (a lemma with explicit arguments, a `(lem (x := v))`, ...). It is accepted
by `iapply`, `ispecialize`, `icases`, `ihave`, `imod`, `iinv`, `wp_apply`.
Examples: `iapply HΦ $$ Hs`, `ihave %Hlen := ownSlice_len _ _ _ $$ Hs`,
`imod ghostVar_update_halves (n + 1) γ n n $$ Hv Hv' with ⟨Hv, Hv'⟩`.

## 3. Tactics

### Context management

| Lean | Rocq | Notes |
|:--|:--|:--|
| `iintro pats` | `iIntros "..." (x)` | `%x` for Lean binders |
| `icases t with pat` | `iDestruct t as "pat"` | consumes `t` if it is a spatial hypothesis |
| `icases +keep t with pat` | | keep the original |
| `ihave pat := t` | `iPoseProof t as "pat"`, `iDestruct (lem with ..) as ..` | does not consume an intuitionistic `t` |
| `ihave pat : P $$ spat` | `iAssert P with "spat" as "pat"` | goal for `P` first |
| `iclear sel` | `iClear "sel"` | |
| `irename H => H'` | `iRename "H" into "H'"` | |
| `irename : P => H` | `iRename select P into "H"` | find the hypothesis by its statement |
| `irevert sel` | `iRevert "sel"` | |
| `ipure H`, `ipure H with pat` | `iPure "H" as pat` | |
| `iintuitionistic H`, `ispatial H` | | `icases H with #H` / `∗H` |
| `ispecialize t` | `iSpecialize t` | e.g. `ispecialize H $$ %x HP [HQ]` |

```lean
example (P Q : PROP) (Φ : Nat → PROP) :
    ⊢ P ∗ Q -∗ (∀ n, Φ n) -∗ Q ∗ Φ 3 ∗ P := by
  iintro ⟨HP, HQ⟩ HΦ
  isplitl [HQ]
  · iexact HQ
  isplitl [HΦ]
  · iapply HΦ
  · iexact HP
```

```lean
example (P Q R : PROP) (φ : Prop) (Ψ : Nat → PROP) :
    ⊢ (∃ n, Ψ n ∗ ⌜φ⌝) -∗ □ R -∗ (P ∨ Q) -∗ (∃ n, Ψ n) ∗ R ∗ (Q ∨ P) := by
  iintro ⟨%n, HΨ, %Hφ⟩ #HR (HP | HQ)
  · iframe HΨ HR     -- `iframe` also instantiates the `∃ n`
    iright
    iexact HP
  · iframe HΨ HR
    ileft
    iexact HQ
```

```lean
example (P Q R : PROP) :
    ⊢ (P -∗ Q -∗ R) -∗ P -∗ Q -∗ R := by
  iintro H HP HQ
  -- give `HP` to the first premise, frame `HQ` into the second
  iapply H $$ HP [$HQ]

example (P Q R : PROP) :
    ⊢ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R := by
  iintro HPQ HQR HP
  ihave HQ := HPQ $$ HP
  ispecialize HQR $$ HQ
  iexact HQR

example (P : PROP) (Φ : Nat → PROP) :
    ⊢ (∀ n, P -∗ Φ n) -∗ P -∗ Φ 7 := by
  iintro H HP
  -- `%t` instantiates a universal quantifier
  iapply H $$ %7 HP
```

```lean
example (P Q : PROP) [Persistent Q] (h : P ⊢ Q) :
    ⊢ P -∗ Q ∗ P := by
  iintro HP
  -- `ihave pat : prop $$ spat` (Rocq `iAssert`): the new goal `Q` gets `HP`;
  -- since `Q` is persistent (`#HQ`), `HP` also stays available afterwards
  ihave #HQ : Q $$ [HP]
  · iapply h; iexact HP
  iframe # ∗
```

```lean
example (P Q : PROP) :
    ⊢ P -∗ Q -∗ P := by
  iintro HP HQ
  iclear HQ
  irename HP => H
  iexact H
```

### Goals

| Lean | Rocq |
|:--|:--|
| `iexact H` | `iExact "H"` |
| `iassumption` | `iAssumption` |
| `iapply t` | `iApply t` |
| `iexists x, y` (holes `_` allowed) | `iExists x, y` |
| `ileft`, `iright` | `iLeft`, `iRight` |
| `isplit` | `iSplit` |
| `isplitl [H₁ H₂]`, `isplitr [H₁ H₂]` | `iSplitL "H1 H2"`, `iSplitR "H1 H2"` |
| `isplitl`, `isplitr` | `iSplitL`, `iSplitR` (all hypotheses to one side) |
| `iframe sel`, `iframe` (= `iframe ∗`) | `iFrame "sel"`, `iFrame` |
| `icombine H₁ H₂ as pat`, `icombine H₁ H₂ gives pat` | `iCombine "H1 H2" as "pat"` / `gives "pat"` |
| `ipureintro` | `iPureIntro` |
| `iempintro` | `iEmpIntro` |
| `iexfalso` | `iExFalso` |
| `itrivial` | `done` (on Iris goals) |
| `iaccu` | `iAccu` |

`iframe` also instantiates existentials it frames through (disable with
`set_option iris.frame.instantiateExists false`) and leaves what it cannot frame.
iris-lean's framing only matches syntactically (up to reducible unfolding). With
Perennial's tactics imported (`Perennial/Golang/Theory/IrisTactics.lean`),
`iframe`/`iframe ∗` first (1) replaces conjuncts of the goal that are equal *by
computation* to a spatial hypothesis (`P ([] ++ [v])` vs `P [v]`, an unreduced
`match`, a `let`), (2) makes a spatial hypothesis with a persistent type
intuitionistic when several conjuncts need it, and (3) for `∃ x, ..` picks the
witness from the hypothesis matching the conjunct that mentions `x` (ignoring
hypotheses that exactly match a conjunct without `x`), when it is unique. Other
differences still need a rewrite first (`rw [show f x = y from ...]`).

```lean
example (P : PROP) (x y : Nat) (h : x = y) :
    ⊢ P -∗ P ∗ ⌜y = x⌝ := by
  iintro HP
  iframe
  ipureintro
  exact h.symm

example (P : PROP) (φ : Prop) :
    ⊢ ⌜φ⌝ ∗ P -∗ P := by
  iintro ⟨Hφ, HP⟩
  ipure Hφ          -- move the pure hypothesis to the Lean context
  iexact HP
```

```lean
example (Φ : Nat → PROP) :
    ⊢ Φ 1 -∗ ∃ n, Φ n := by
  iintro H
  iexists 1
  iexact H

example (Φ : Nat → Nat → PROP) :
    ⊢ Φ 1 2 -∗ ∃ n m, Φ n m := by
  iintro H
  iexists _, _
  iexact H
```

```lean
example (P Q R : PROP) :
    ⊢ □ R -∗ P -∗ Q -∗ R ∗ Q ∗ P := by
  iintro #HR HP HQ
  iframe HP
  iframe # ∗
```

### Modalities

| Lean | Rocq |
|:--|:--|
| `imodintro`, `imodintro (□ _)` | `iModIntro`, `iModIntro (□ _)` |
| `inext` | `iNext` |
| `inext n credit: H` | `iNext` with later credits (goal must be a fancy update) |
| `imod t`, `imod t with pat` | `iMod t`, `iMod t as "pat"` |
| `iinv H with pat Hclose` | `iInv "H" as "pat" "Hclose"` |
| `iinv N with pat Hclose` | `iInv N as ...` (the last invariant with namespace `N`) |

```lean
example (P Q : IProp GF) (E : CoPset) :
    ⊢ (|==> P) -∗ ▷ Q -∗ |={E}=> P ∗ ▷ Q := by
  iintro HP HQ
  imod HP            -- eliminate the update, keeping the name `HP`
  imodintro          -- introduce `|={E}=>`
  iframe

example (P : IProp GF) [Timeless P] (E : CoPset) :
    ⊢ ▷ P -∗ |={E}=> P := by
  iintro >HP         -- strip the later of a timeless proposition
  imodintro
  iexact HP

example (P Q : IProp GF) :
    ⊢ ▷ P -∗ ▷ Q -∗ ▷ (P ∗ Q) := by
  iintro HP HQ
  inext              -- strips `▷` from the goal and the hypotheses
  iframe
```

`iinv H with pat Hclose` on a goal `|={E}=> Q` (or a WP of an atomic
expression; on a non-atomic one it is an error, `wp_bind` first) opens `H : inv N P`, destructs `▷ P` with `pat` (use `>` to strip
the later of timeless parts) and destructs the closing view shift (which takes
`▷ P` back and restores the mask) with `Hclose`; close with
`imod Hclose $$ [..] with _`. Without the second pattern, giving `▷ P` back
becomes part of the goal instead (in `wp_runtime_Semacquire`,
`Perennial/Proof/sync_proof/sema.lean`, it is proved with `isplitl [..]` after
the atomic step). See the ghost-state example in
`PERENNIAL_PROOF_TUTORIAL.md` §10. The mask side condition (`↑N ⊆ E`, e.g.
`↑(N.@"inv") ⊆ ⊤ ∖ ↑(N.@"sema")`) is proved by `solve_ndisj` (Perennial's
`iinv`, `Perennial/Golang/Theory/IrisTactics.lean`); a condition it cannot
prove is left as a goal before the main one. For other mask goals (e.g. the
premise of `fupd_mask_intro`) use `solve_ndisj` explicitly.

### Induction and rewriting

| Lean | Rocq |
|:--|:--|
| `iloeb as IH`, `iloeb as IH generalizing %x H` | `iLöb as "IH" forall (x) "H"` |
| `iinduction e with ...` | `iInduction e as ...` |
| `irewrite [h]`, `irewrite [← h] at H` | `iRewrite h` (internal equality `≡`) |
| `ieval (tac)`, `ieval (tac) at H` | `iEval (tac)`, `iEval (tac) in "H"` |
| `isimp [lemmas] at H`, `iunfold f at H` | `iSimpl`, `iUnfold` |

```lean
example (P : PROP) : ⊢ ▷ P -∗ ▷ P := by
  iintro HP
  iloeb as IH
  iexact HP
```

Ordinary Lean `rw`, `simp only`, `unfold` also work on a proof mode goal: the
hypotheses are part of the goal term, so they rewrite the whole context (this is
how `simp only [isMutex_unseal, isMutexDef]` is used in the sync proofs). To
change only some hypotheses use `ieval ... at H`.

## 4. Notation and precedence

`∗` (35), `-∗` (25, right associative), `∧`, `∨`, `→`, `⌜φ⌝`, `□ P`, `▷ P`,
`<pers> P`, `|==> P`, `|={E1,E2}=> P`, `P ==∗ Q`, `P ={E}=∗ Q`, `£ n` (later
credits), `[∗ list] k ↦ x ∈ l, P`, `[∗ map] k ↦ x ∈ m, P`. In a term
position that is not already an Iris proposition, wrap with `iprop(...)`.

**Precedence trap.** `|==>`, `▷`, `□` and `<pers>` take their argument at
precedence 40, above `∗` (35): `|==> A ∗ B` is `(|==> A) ∗ B`, unlike Rocq. The
fancy update `|={E}=> A ∗ B` and the wand forms `A ==∗ B ∗ C`, `A ={E}=∗ B ∗ C`
extend to the right, as in Rocq.

```lean
-- `|==>` (and `▷`, `□`) bind tighter than `∗`; `|={E}=>` extends to the right.
example (P Q : IProp GF) : iprop(|==> P ∗ Q) = iprop((|==> P) ∗ Q) := rfl
example (P Q : IProp GF) (E : CoPset) : iprop(|={E}=> P ∗ Q) = iprop(|={E}=> (P ∗ Q)) := rfl
example (P Q : IProp GF) : iprop(▷ P ∗ Q) = iprop((▷ P) ∗ Q) := rfl
```

## 5. Pitfalls for Rocq IPM users

* `iDestruct "H" as "[H1 H2]"` → `icases H with ⟨H1, H2⟩`;
  `iDestruct "H" as (x y) "[H1 %H2]"` → `icases H with ⟨%x, %y, H1, %H2⟩`.
* `iDestruct (lem with "H") as %Hp` → `ihave %Hp := lem $$ H` or
  `icases lem $$ H with %Hp`. For a pure (or persistent) result the hypotheses
  used for the premises stay available, as in Rocq.
* `iApply ("H" with "[$H1] [H2]")` → `iapply H $$ [$H1] [H2]`; `"H" $! x` →
  `H $$ %x`.
* `iFrame "∗#"` → `iframe ∗ #` (or `iframe # ∗`); `iFrame "H"` → `iframe H`.
* `iModIntro` → `imodintro`; `iIntros "!> H"` → `iintro !> H`.
* `"%->"` → `%rfl` (it is an `rcases` pattern), or `%h` then `subst h`.
* Write `% ⟨a, b⟩` with a space after `%` when `%⟨` is a token in your imports
  (otherwise: "unexpected token '%⟨'").
* `iMod (lem with "H") as "H'"` → `imod lem $$ H with H'`.
* The strings in named propositions (`"Hx" ∷ P`) are iris-lean cases patterns
  parsed from the string (`"%H"`, `"#H"`, `"⟨H1, H2⟩"`), not Rocq patterns.
  Hypothesis names that are not plain identifiers (goose's `«$r0»`) cannot be
  written there; `irename «$r0» => Hsum` first.
* `iExists _, _` → `iexists _, _`.
* `iSplitL "H1 H2"` → `isplitl [H1 H2]` (brackets, no quotes).
* `iClear "∗"` → `iclear ∗`.
* `done` on an Iris goal → `itrivial`; Rocq `lia`/`word` → `omega`/`word`.
