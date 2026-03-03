Copied from <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md>

Tactic overview
===============

This reference manual defines a few different syntaxes that are used
pervasively. These are defined in dedicated sections in this manual.

- An "[introduction pattern][ipat]" `ipat` like `"H"` or `"[H1 H2]"` is used to
  _destruct_ a hypothesis (sometimes called _eliminating_ a hypothesis). This is
  directly used by `iDestruct` and `iIntros`, but many tactics also integrate
  support for `ipat`s to combine some other work with destructing, such as
  `iMod`. The name "introduction pattern" comes from a similar term in Coq which
  is used in tactics like `destruct` and `intros`.
- A "[selection pattern][selpat]" `selpat` like `"H1 H2"` or `"#"` names a collection of
  hypotheses. Most commonly used in `iFrame`.
- A "[specialization pattern][spat]" `spat` like `H` or `[$H1 H2]` is used to specialize
  a wand to some hypotheses along with specifying framing. Commonly used as part
  of proof mode terms (described just below).
- A "[proof mode term][pm-trm]" `pm_trm` like `lemma with spat` or `"H" $! x with spat`
  allows to specialize a wand (which can be either a Gallina lemma or a
  hypothesis) on the fly, as an argument to `iDestruct` for example.

Many of the tactics below apply to more goals than described in this document
since the behavior of these tactics can be tuned via instances of the type
classes in the file [proofmode/classes](../iris/proofmode/classes.v). Most notably, many
of the tactics can be applied when the connective to be introduced or to be eliminated
appears under a later, an update modality, or in the conclusion of a
weakest precondition.

[ipat]: #introduction-patterns-ipat
[selpat]: #selection-patterns-selpat
[spat]: #specialization-patterns-spat
[pm-trm]: #proof-mode-terms-pm_trm

Starting and stopping the proof mode
------------------------------------

- `iStartProof` : start the proof mode by turning a Coq goal into a proof
  mode entailment. This tactic is performed implicitly by all proof mode tactics
  described in this file, and thus should generally not be used by hand.
  + `iStartProof PROP` : explicitly specify which BI logic `PROP : bi` should be
    used. This is useful to drop down in a layered logic, e.g. to drop down from
    `monPred PROP` to `PROP`.
- `iStopProof` : turn the proof-mode entailment into an ordinary Coq goal
  `big star of context ⊢ proof mode goal`.

Applying hypotheses and lemmas
------------------------------

- `iExact "H"`  : finish the goal if the conclusion matches the hypothesis `H`
- `iAssumption` : finish the goal if the conclusion matches any hypothesis in
  either the proofmode or the Coq context. Only hypotheses in the Coq context
  that are _syntactically_ of the shape `⊢ P` are recognized by this tactic
  (this means that assumptions of the shape `P ⊢ Q` are not recognized).
- `iApply pm_trm` : match the conclusion of the current goal against the
  conclusion of `pm_trm` and generates goals for the premises of `pm_trm`. See
  [proof mode terms][pm-trm] below.
  If the applied term has more premises than given specialization patterns, the
  pattern is extended with `[] ... []`. As a consequence, all unused spatial
  hypotheses move to the last premise.

Context management
------------------

- `iIntros (x1 ... xn) "ipat1 ... ipatn"` : introduce universal quantifiers
  using Coq introduction patterns `x1 ... xn` and implications/wands using proof
  mode [introduction patterns][ipat] `ipat1 ... ipatn`.
- `iClear (x1 ... xn) "selpat"` : clear the hypotheses given by the [selection
  pattern][selpat] `selpat` and the Coq level hypotheses/variables `x1 ... xn`.
- `iClear select (pat)%I` : clear the last hypothesis of the intuitionistic
  or spatial context that matches pattern `pat`.
- `iRevert (x1 ... xn) "selpat"` : revert the hypotheses given by the [selection
  pattern][selpat] `selpat` into wands, and the Coq level hypotheses/variables
  `x1 ... xn` into universal quantifiers. Intuitionistic hypotheses are wrapped
  into the intuitionistic modality.
- `iRevert select (pat)%I` : revert the last hypothesis of the intuitionistic
  or spatial context that matches pattern `pat`.
- `iRename "H1" into "H2"` : rename the hypothesis `H1` into `H2`.
- `iRename select (pat)%I into "H"` : rename the last hypothesis of the
  intuitionistic or spatial context that matches pattern `pat` into `H`. This
  is particularly useful to give a name to an anonymous hypothesis.
- `iSpecialize pm_trm` : instantiate universal quantifiers and eliminate
  implications/wands of a hypothesis `pm_trm`. See [proof mode terms][pm-trm] below.
- `iSpecialize pm_trm as #` : instantiate universal quantifiers and eliminate
  implications/wands of a hypothesis `pm_trm` whose conclusion is persistent.
  All hypotheses can be used for proving the premises of `pm_trm`, as well as
  for the resulting main goal.
- `iPoseProof pm_trm as (x1 ... xn) "ipat"` : put `pm_trm` into the context and
  destruct it using the [introduction pattern][ipat] `ipat`. This tactic is
  essentially the same as `iDestruct` with the difference that `pm_trm` is not
  thrown away if possible.
- `iAssert (P)%I with "spat" as "H"` : generate a new subgoal `P` and add the
  hypothesis `P` to the current goal as `H`. The [specialization pattern][spat] `spat`
  specifies which hypotheses will be consumed by proving `P`.
  + `iAssert (P)%I with "spat" as "ipat"` : like the above, but immediately destruct
    the generated hypothesis using the [introduction pattern][ipat] `ipat`. If `ipat`
    is "intuitionistic" (most commonly, it starts with `#` or `%`), then all spatial
    hypotheses are available in both the subgoal for `P` as well as the current
    goal. An `ipat` is considered intuitionistic if all branches start with a
    `#` (which causes `P` to be moved to the intuitionistic context) or with a
    `%` (which causes `P` to be moved to the pure Coq context).
  + `iAssert (P)%I as %cpat` : assert `P` and destruct it using the Coq introduction
    pattern `cpat`. All hypotheses can be used for proving `P` as well as for
    proving the current goal.
- `iSelect (pat)%I tac` : run the tactic `tac H`, where `H` is the name of the
  last hypothesis in the intuitionistic or spatial hypothesis context that
  matches pattern `pat`. There is no backtracking to select the next hypothesis
  in case `tac H` fails.

Introduction of logical connectives
-----------------------------------

- `iPureIntro` : turn a pure goal, typically of the form `⌜φ⌝`, into a Coq
  goal. This tactic also works for goals of the shape `a ≡ b` on discrete
  OFEs, and `✓ a` on discrete cameras.
- `iLeft` : prove a disjunction `P ∨ Q` by proving the left side `P`.
- `iRight` : prove a disjunction `P ∨ Q` by proving the right side `Q`.
- `iSplitL "H1 ... Hn"` : split a conjunction `P ∗ Q` into two proofs. The
  hypotheses `H1 ... Hn` are used for the left conjunct, and the remaining ones
  for the right conjunct. Intuitionistic hypotheses are always available in both
  proofs. Also works on `P ∧ Q`, although in that case you can use `iSplit` and
  retain all the hypotheses in both goals.
- `iSplitR "H0 ... Hn"` : symmetric version of the above, using the hypotheses
  `H1 ... Hn` for the right conjunct. Note that the goals are still ordered
  left-to-right; you can use `iSplitR "..."; last
  first` to reverse the generated goals.
- `iSplit` : split a conjunction `P ∧ Q` into two goals. Also works for
  separating conjunction `P ∗ Q` provided one of the operands is persistent (and both
  proofs may use the entire spatial context).
- `iExists t1, .., tn` : provide a witness for an existential quantifier `∃ x, ...`. `t1
  ... tn` can also be underscores, which are turned into evars. (In fact they
  can be arbitrary terms with holes, or `open_constr`s, and all of the
  holes will be turned into evars.)

Elimination of logical connectives
----------------------------------

- `iExFalso` : change the goal to proving `False`.
- `iDestruct` is an important enough tactic to describe several special cases:
  + `iDestruct "H1" as (x1 ... xn) "H2"` : eliminate a series of existential
    quantifiers in hypothesis `H1` using Coq introduction patterns `x1 ... xn`
    and name the resulting hypothesis `H2`. The Coq introduction patterns can
    also be used for pure conjunctions; for example we can destruct
    `∃ x, ⌜v = x⌝ ∗ l ↦ x` using `iDestruct "H" as (x Heq) "H"` to immediately
    put `Heq: v = x` in the Coq context. This variant of the tactic will always
    throw away the original hypothesis `H1`.
  + `iDestruct pm_trm as "ipat"` : specialize the [proof-mode term][pm-trm] (see
    below) and destruct it using the [introduction pattern][ipat] `ipat`. If
    `pm_trm` starts with a hypothesis, and that hypothesis resides in the
    intuitionistic context, it will not be thrown away.
  + `iDestruct pm_trm as (x1 ... xn) "ipat"` : combine the above, first
    specializing `pm_trm`, then eliminating existential quantifiers (and pure
    conjuncts) with `x1 ... xn`, and finally destructing the resulting term
    using the [introduction pattern][ipat] `ipat`.
  + `iDestruct pm_trm as %cpat` : destruct the pure conclusion of a term
    `pr_trm` using the Coq introduction pattern `cpat`. When using this tactic,
    all hypotheses can be used for proving the premises of `pm_trm`, as well as
    for proving the resulting goal.
  + `iDestruct num as (x1 ... xn) "ipat"` / `iDestruct num as %cpat` :
    introduce `num : nat` hypotheses and destruct the last introduced hypothesis.
  + `iDestruct select (pat)%I as ...` is the same as `iDestruct "H" as ...`,
    where `H` is the name of the last hypothesis of the intuitionistic or
    spatial context matching pattern `pat`.

  In case all branches of `ipat` start with a `#` (which causes the hypothesis
  to be moved to the intuitionistic context), with an `%` (which causes the
  hypothesis to be moved to the pure Coq context), or with an `->`/`<-` (which
  performs a rewrite), then one can use all hypotheses for proving the premises
  of `pm_trm`, as well as for proving the resulting goal. Note that in this case
  the hypotheses still need to be subdivided among the spatial premises.

Separation logic-specific tactics
---------------------------------

- `iFrame (t1 .. tn) "selpat"` : cancel the Coq terms (or Coq hypotheses)
  `t1 ... tn` and Iris hypotheses given by [`selpat`][selpat] in the goal. The constructs
  of the selection pattern have the following meaning:
  + `%` : repeatedly frame hypotheses from the Coq context.
  + `#` : repeatedly frame hypotheses from the intuitionistic context.
  + `∗` : frame as much of the spatial context as possible. (N.B: this
          is the unicode symbol `∗`, not the regular asterisk `*`.)
  Notice that framing spatial hypotheses makes them disappear, but framing Coq
  or intuitionistic hypotheses does not make them disappear.
  This tactic solves the goal if everything in the conclusion has been framed,
  i.e., the conclusion turned into `True`/`emp`. If multiple selection patterns
  are given, and the goal turns into `True`/`emp` while not all have been
  processed, the `iFrame` tactic fails.
- `iFrame select (pat)%I` : cancel the last hypothesis of the intuitionistic
  of spatial context that matches pattern `pat`.
- `iCombine "H1 H2" as "ipat"` : combine `H1 : P1` and `H2 : P2` into `H: P1 ∗
  P2` or something simplified but equivalent, then `destruct` the combined
  hypothesis using `ipat`. Some examples of simplifications `iCombine` knows
  about are to combine `own γ x` and `own γ y` into `own γ (x ⋅ y)`, and to
  combine `l ↦{1/2} v` and `l ↦{1/2} v` into `l ↦ v`.
- `iCombine "H1 H2" gives "ipat"` : from `H1 : P1` and `H2 : P2`, find
  persistent consequences of `P1 ∗ P2`, then `destruct` this consequence with
  `ipat`. Some examples of persistent consequences `iCombine` knows about are
  that `own γ x` and `own γ y` gives `✓ (x ⋅ y)`, and that
  `l ↦{#q1} v1` and `l ↦{#q2} v2` gives `⌜(q1 + q2 ≤ 1) ∧ v1 = v2⌝`.
- `iCombine "H1 H2" as "ipat1" gives "ipat2"` combines the two functionalities
  of `iCombine` described above.
- `iAccu` : solve a goal that is an evar by instantiating it with all
  hypotheses from the spatial context joined together with a separating
  conjunction (or `emp` in case the spatial context is empty). Not commonly
  used, but can be extremely useful when combined with automation.

Modalities
----------

- `iModIntro` : introduce a modality in the goal. The type class `FromModal` is
  used to specify which modalities this tactic should introduce, and how
  introducing that modality affects the hypotheses. Instances of
  that type class include: later, except 0, basic update and fancy update,
  intuitionistically, persistently, affinely, plainly, absorbingly, objectively,
  and subjectively.
  + `iModIntro mod` (rarely used): introduce a specific modality named by
  `mod`,  which is a term pattern (i.e., a term with holes as underscores).
  `iModIntro mod` will find a subterm matching `mod`, and try introducing its
  topmost modality. For instance, if the goal is `⎡|==> P⎤`, using `iModIntro
  ⎡|==> P⎤%I` or `iModIntro ⎡_⎤%I` would introduce `⎡_⎤` and produce goal `|==>
  P`, while `iModIntro (|==> _)%I` would introduce `|==>` and produce goal
  `⎡P⎤`.
  + `iNext` : an alias of `iModIntro (▷^_ _)` (that is, introduce the later
    modality). This eliminates a later in the goal, and in exchange also strips
    one later from all the hypotheses.
  + `iNext n` : an alias of `iModIntro (▷^n _)` (that is, introduce the `▷^n`
    modality).
  + `iAlways` : a deprecated alias of `iModIntro` (intended to introduce the `□`
    modality).
- `iNext n credit:"H"` : decrease the later credit `H` by `n` and strip `n`
  laters from all the hypotheses. This tactic requires the goal to be a fancy
  update modality.
  + `iNext credit:"H"` : equivalent to `iNext 1 credit:"H"`.
- `iMod pm_trm as (x1 ... xn) "ipat"` : eliminate a modality `pm_trm` that is
  an instance of the `ElimModal` type class, and destruct the resulting
  hypothesis using `ipat`. Instances include: later, except 0,
  basic update `|==>` and fancy update `|={E}=>`.
  + `iMod "H"` : equivalent to `iMod "H" as "H"` (eliminates the modality and
    keeps the name of the hypothesis).
  + `iMod pm_trm` : equivalent to `iMod pm_term as "?"` (the resulting
    hypothesis will be introduced anonymously).

Induction
---------

- `iLöb as "IH"` : perform Löb induction by
  generating a hypothesis `IH : ▷ goal`.
  + `iLöb as "IH" forall (x1 ... xn) "selpat"` : perform Löb induction,
  generalizing over the Coq level variables `x1 ... xn`, the hypotheses given by
  the selection pattern `selpat`, and the spatial context as usual.
- `iInduction x as cpat` : perform induction on the Coq term `x`. The
  Coq introduction pattern `cpat` is used to name the introduced variables,
  including the induction hypotheses which are introduced into the proof mode
  context. Note that induction hypotheses should not be put into string
  quotation marks `".."`, e.g., use `iInduction n as [|n IH]` to perform
  induction on a natural number `n`. An implementation caveat is that the names
  of the induction hypotheses should be fresh in both the Coq context and the
  proof mode context.
  + `iInduction x as cpat forall (x1 ... xn) "selpat"` : perform induction,
    generalizing over the Coq level variables `x1 ... xn`, the hypotheses given by
    the selection pattern `selpat`, and the spatial context.
  + `iInduction x as cpat using t` : perform induction using the induction
    scheme `t`. Common examples of induction schemes are `map_ind`, `set_ind_L`,
    and `gmultiset_ind` for `gmap`, `gset`, and `gmultiset`.
  + `iInduction x as cpat using t forall (x1 ... xn) "selpat"` : the above
    variants combined.
  + `iInduction x as cpat "IH" "selpat"` : ignore the names of the induction
    hypotheses from `cpat` and call them `IH`, `IH1`, `IH2`, etc. Here "IH" is
    a string (in string quotation marks). This is *legacy* syntax that might be
    deprecated in the future. Similar legacy syntax exists for all variants above.

Rewriting / simplification
--------------------------

- `iRewrite pm_trm` / `iRewrite pm_trm in "H"` : rewrite using an internal
  equality in the proof mode goal / hypothesis `H`.
- `iRewrite -pm_trm` / `iRewrite -pm_trm in "H"` : rewrite in reverse direction
  using an internal equality in the proof mode goal / hypothesis `H`.
- `iEval (tac)` / `iEval (tac) in "selpat"` : perform a tactic `tac`
  on the proof mode goal / hypotheses given by the selection pattern
  `selpat`. Using `%` as part of the selection pattern is unsupported.
  The tactic `tac` should be a reduction or rewriting tactic like
  `simpl`, `cbv`, `lazy`, `rewrite` or `setoid_rewrite`. The `iEval`
  tactic is implemented by running `tac` on `?evar ⊢ P` / `P ⊢ ?evar`
  where `P` is the proof goal / a hypothesis given by `selpat`. After
  running `tac`, `?evar` is unified with the resulting `P`, which in
  turn becomes the new proof mode goal / a hypothesis given by
  `selpat`. Note that parentheses around `tac` are needed.
- `iSimpl` / `iSimpl in "selpat"` : perform `simpl` on the proof mode
  goal / hypotheses given by the selection pattern `selpat`. This is a
  shorthand for `iEval (simpl)`.
- `iUnfold xs` / `iUnfold xs in "selpat"` : perform `unfold xs` on the proof
  mode goal / hypotheses given by the selection pattern `selpat`. This is a
  shorthand for `iEval (unfold xs)`. Similar to Coq's `unfold`, the argument
  `xs` should be a comma-separated non-empty list.

Iris
----

- `iInv H as (x1 ... xn) "ipat"` : open an invariant in hypothesis H. The result
  is destructed using the Coq intro patterns `x1 ... xn` (for existential
  quantifiers) and then the proof mode [introduction pattern][ipat] `ipat`.
  + `iInv H with "selpat" as (x1 ... xn) "ipat" "Hclose"` : generate an update
  for closing the invariant and put it in a hypothesis named `Hclose`.
  + `iInv H with "selpat" as (x1 ... xn) "ipat"` : supply a selection pattern
  `selpat`, which is used for any auxiliary assertions needed to open the
  invariant (e.g. for cancelable or non-atomic invariants).
  + `iInv N as (x1 ... xn) "ipat"` : identify the invariant to be opened with a
    namespace `N` rather than giving a specific hypothesis.
  + `iInv S with "selpat" as (x1 ... xn) "ipat" "Hclose"` : combine all the
    above, where `S` is either a proof-mode identifier or a namespace.

Miscellaneous
-------------

- The tactic `done` of [std++](https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/tactics.v)
  (which solves "trivial" goals using `intros`, `reflexivity`, `symmetry`,
  `eassumption`, `trivial`, `split`, `discriminate`, `contradiction`, etc.) is
  extended so that it also, among other things:
  + performs `iAssumption`,
  + introduces `∀`, `→`, and `-∗` in the proof mode,
  + introduces pure goals `⌜ φ ⌝` using `iPureIntro` and calls `done` on `φ`, and,
  + solves other trivial proof mode goals, such as `emp`, `x ≡ x`, big operators
    over the empty list/map/set/multiset.

  (Note that ssreflect also has a `done` tactic. Although Iris uses ssreflect,
  it overrides ssreflect's `done` tactic with std++'s.)
- The proof mode adds hints to the core `eauto` database so that `eauto`
  automatically introduces: conjunctions and disjunctions, universal and
  existential quantifiers, implications and wand, plainness, persistence, later
  and update modalities, and pure connectives.

Selection patterns (`selpat`)
=============================

Selection patterns are used to select hypotheses in the tactics `iRevert`,
`iClear`, `iFrame`, `iLöb` and `iInduction`. The proof mode supports the
following _selection patterns_:

- `H` : select the hypothesis named `H`.
- `%` : select the entire pure/Coq context.
- `#` : select the entire intuitionistic context.
- `∗` : select the entire spatial context. (N.B: this
        is the unicode symbol `∗`, not the regular asterisk `*`.)

Introduction patterns (`ipat`)
==============================

Introduction patterns are used to perform introductions and eliminations of
multiple connectives on the fly. The proof mode supports the following
_introduction patterns_:

- `H` : create a hypothesis named `H`.
- `?` : create an anonymous hypothesis.
- `_` : clear the hypothesis.
- `$` : frame the hypothesis in the goal.
- `[ipat1 ipat2]` : (separating) conjunction elimination. In order to destruct
  conjunctions `P ∧ Q` in the spatial context, one of the following conditions
  should hold:
  + Either the proposition `P` or `Q` should be persistent.
  + Either `ipat1` or `ipat2` should be `_`, which results in one of the
    conjuncts to be thrown away.
- `[%x ipat]`/`[% ipat]` : existential elimination, naming the witness `x` or
  keeping it anonymous. Falls back to (separating) conjunction elimination in
  case the hypothesis is not an existential, so this pattern also works for
  (separating) conjunctions with a pure left-hand side.
- `(pat1 & pat2 & ... & patn)` : syntactic sugar for `[pat1 [pat2 .. patn ..]]`
  to destruct nested (separating) conjunctions.
- `[ipat1|ipat2]` : disjunction elimination.
- `[]` : false elimination.
- `%H` : move the hypothesis to the pure Coq context, and name it `H`.
- `%` : move the hypothesis to the pure Coq context (anonymously). Note that if
  `%` is followed by an identifier, and not another token, a space is needed
  to disambiguate from `%H` above.
- `->` and `<-` : rewrite using a pure Coq equality
- `# ipat` : move the hypothesis into the intuitionistic context. The tactic
  will fail if the hypothesis is not intuitionistic. On success, the tactic will
  strip any number of intuitionistic and persistence modalities. If the
  hypothesis is already in the intuitionistic context, the tactic will still
  strip intuitionistic and persistence modalities (it is a no-op if the
  hypothesis does not contain such modalities).
- `-# ipat` (uncommon) : move the hypothesis into the spatial context. This can
  move a hypothesis from the intuitionistic context to the spatial context, or
  can explicitly specify the spatial context when the intuitionistic context
  could be used (e.g., because a hypothesis was proven without using spatial
  hypotheses). If the hypothesis is already in the spatial context, the tactic
  is a no-op. If the hypothesis is not affine, an `<affine>` modality is added
  to the hypothesis.
- `> ipat` : eliminate a modality (if the goal permits); commonly used to strip
  a later from the hypothesis when it is timeless and the goal is either a `WP`
  or an update modality `|={E}=>`.

Apart from this, there are the following introduction patterns that can only
appear at the top level:

- `{selpat}` : clear the hypotheses given by the selection pattern `selpat`.
  Items of the selection pattern can be prefixed with `$`, which cause them to
  be framed instead of cleared.
- `!%` : introduce a pure goal (and leave the proof mode).
- `!>` : introduce a modality by calling `iModIntro`.
- `!#` : introduce a modality by calling `iModIntro` (deprecated).
- `/=` : perform `simpl`.
- `//` : perform `try done` on all goals.
- `//=` : syntactic sugar for `/= //`
- `*` : introduce all universal quantifiers. (N.B.: this is the asterisk `*` and
  not the separating conjunction `∗`)
- `**` : introduce all universal quantifiers, as well as all arrows and wands.

For example, given:

        ∀ x, <affine> ⌜ x = 0 ⌝ ⊢
          □ (P → False ∨ □ (Q ∧ ▷ R) -∗
          P ∗ ▷ (R ∗ Q ∧ ⌜ x = pred 2 ⌝)).

You can write

        iIntros (x Hx) "!> $ [[] | #[HQ HR]] /= !>".

which results in:

        x : nat
        Hx : x = 0
        ______________________________________(1/1)
        "HQ" : Q
        "HR" : R
        --------------------------------------□
        R ∗ Q ∧ x = 1


Specialization patterns (`spat`)
================================

Since we are reasoning in a spatial logic, when eliminating a lemma or
hypothesis of type ``P_0 -∗ ... -∗ P_n -∗ R``, one has to specify how the
hypotheses are split between the premises. The proof mode supports the following
_specialization patterns_ to express splitting of hypotheses:

- `H` : use the hypothesis `H`, which should match the premise exactly. If `H` is
  spatial, it will be consumed.
- `(H spat1 .. spatn)` : first recursively specialize the hypothesis `H` using
  the specialization patterns `spat1 .. spatn`, and finally use the result of
  the specialization of `H`, which should match the premise exactly. If `H` is
  spatial, it will be consumed.
- `[H1 .. Hn]` and `[H1 .. Hn //]` : generate a goal for the premise with the
  (spatial) hypotheses `H1 ... Hn` and all intuitionistic hypotheses. The
  spatial hypotheses among `H1 ... Hn` will be consumed, and will not be
  available for subsequent goals. Hypotheses prefixed with a `$` will be framed
  in the goal for the premise. The pattern can be terminated with a `//`, which
  causes `done` to be called to close the goal (after framing).
- `[-H1 ... Hn]` and `[-H1 ... Hn //]` : the negated forms of the above
  patterns, where the goal for the premise will have all spatial premises except
  `H1 .. Hn`.
- `[> H1 ... Hn]` and `[> H1 ... Hn //]` : like the above patterns, but these
  patterns can only be used if the goal is a modality `M`, in which case
  the goal for the premise will be wrapped in the modality `M`.
- `[> -H1 ... Hn]` and `[> -H1 ... Hn //]` : the negated forms of the above
  patterns.
- `[# $H1 .. $Hn]` and `[# $H1 .. $Hn //]` : generate a goal for a persistent
  premise in which all hypotheses are available. This pattern does not consume
  any hypotheses; all hypotheses are available in the goal for the premise as
  well in the subsequent goal. The hypotheses `$H1 ... $Hn` will be framed in
  the goal for the premise. These patterns can be terminated with a `//`, which
  causes `done` to be called to close the goal (after framing).
- `[%]` and `[% //]` : generate a Coq goal for a pure premise. This pattern
  does not consume any hypotheses. The pattern can be terminated with a `//`
  which causes `done` to be called to close the goal.
- `[$]` : solve the premise by framing. It will first repeatedly frame and
  consume the spatial hypotheses, and then repeatedly frame the intuitionistic
  hypotheses. Spatial hypotheses that are not framed are carried over to the
  subsequent goal.
- `[> $]` : like the above pattern, but this pattern can only be used if the
  goal is a modality `M`, in which case the goal for the premise will be wrapped
  in the modality `M` before framing.
- `[# $]` : solve the persistent premise by framing. It will first repeatedly
  frame the spatial hypotheses, and then repeatedly frame the intuitionistic
  hypotheses. This pattern does not consume any hypotheses.

For example, given:

        H : □ P -∗ P 2 -∗ R -∗ x = 0 -∗ Q1 ∗ Q2

One can write:

        iDestruct ("H" with "[#] [H1 $H2] [$] [% //]") as "[H4 H5]".


Proof mode terms (`pm_trm`)
===========================

Many of the proof mode tactics (such as `iDestruct`, `iApply`, `iRewrite`) can
take both hypotheses and lemmas, and allow one to instantiate universal
quantifiers and implications/wands of these hypotheses/lemmas on the fly.

The syntax for the arguments of these tactics, called _proof mode terms_, is:

        (H $! t1 ... tn with "spat1 .. spatn")

Here, `H` can be either a hypothesis or a Coq lemma whose conclusion is
of the shape `P ⊢ Q`. In the above, `t1 ... tn` are arbitrary Coq terms used
for instantiation of universal quantifiers, and `spat1 .. spatn` are
[specialization patterns][spat] to eliminate implications and wands.

Proof mode terms can be written down using the following shorthand syntaxes, too:

        (H with "spat1 .. spatn")
        (H $! t1 ... tn)
        H

HeapLang tactics
================

If you came here looking for the `wp_` tactics, those are described in the
[HeapLang documentation](./heap_lang.md).
