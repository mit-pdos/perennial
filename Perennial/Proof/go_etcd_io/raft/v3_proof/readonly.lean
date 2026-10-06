/-
Port of `new/proof/go_etcd_io/raft/v3_proof/readonly.v`: the ReadIndex
(linearizable read) protocol of raft, its ghost state, and specs for the
`readOnly` methods.

See the Rocq file for the discussion of the protocol (and of the bug in the raft
library: https://github.com/etcd-io/etcd/issues/20418#issuecomment-3974901065,
https://github.com/etcd-io/raft/issues/392).

Lean notes:
* Everything lives in `namespace go_etcd_io.raft.v3_proof.readonly`: Rocq's
  `readonly.v` defines its own `RaftNames` record, shadowing the axiomatized
  `RaftNames` of `protocol.v`.
* Rocq's `Context (cfg : gset w64)` is an explicit section variable `cfg`.
* `ownTerm`/`isTermLb`: Rocq owns `{[node_id := ●MN n]}` in a
  `gmap w64 mono_natR` camera. `allG` has no `gmap` CMRA code (only `gmapUR`
  as a unital camera, and `gmap_viewR`), so here the per-node ghost name is
  found through a persistent ghost map: `node_id ↪[termGn]□ γn ∗
  mono_nat_auth_own γn 1 n` (resp. `mono_nat_lb_own γn n`). Neither is used
  in any lemma of this file except as an opaque persistent witness.
* Deviations from Rocq (statements/definitions):
  - `ownReadOnly` takes the number `n` of read requests added so far, with
    `"%Hcount"`; `wp_readOnly_recvAck` and `wp_readOnly_maybeAdvance` keep `n`,
    `wp_readOnly_addRequest` requires `n < 2^64 - 1` and returns `n + 1`. This
    makes the overflow side condition admitted in Rocq provable.
  - `ProgressTracker.wp_IsSingleton`: Rocq's (trusted) statement
    `{{{ True }}} .. {{{ RET #false; True }}}` is false; replaced by the true
    spec (see the lemma), now proved. This needed `len` to unfold at the named
    map type `quorum.MajorityConfig`: `go.len_map` takes `[t ↓u go.MapType ..]`
    (Rocq: literal `go.MapType` only), and `wp_map_len` (new, not in Rocq) is
    in `Perennial/Golang/Theory/Map.lean`.
  - New helper: `array_acc_same`.
-/
import Perennial.Proof.go_etcd_io.raft.v3_proof.protocol
import Perennial.Ghost.MonoList
import Perennial.Ghost.MonoNat
import Perennial.Ghost.SavedProp
import Perennial.Ghost.DGhostVar
import Perennial.Ghost.GhostMap

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open scoped GMap

namespace go_etcd_io.raft.v3_proof.readonly

-- (once, before the proofs: a notation declared after asynchronously elaborated
-- proofs waits for them)
local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- Rocq `RaftNames`. -/
structure RaftNames where
  mk ::
  commitedGn : GName
  termGn : GName
  configGn : GName
  readsGn : GName
  readReqGn : GName
  heartbeatGn : GName

section proof
variable (cfg : GSet w64)

section global_proof
variable {GF : BundledGFunctors} [InvGS GF] [AllG GF]

/-- Rocq `N`. -/
def N : Namespace := nroot

/-! ### Ghost state for the raft protocol -/

abbrev ownCommitAuth (γ : RaftNames) (log : List (List w8)) : IProp GF :=
  monoListAuthOwn γ.commitedGn (1 : Qp).half log
abbrev ownCommit (γ : RaftNames) (log : List (List w8)) : IProp GF :=
  monoListAuthOwn γ.commitedGn (1 : Qp).half log
abbrev isCommit (γ : RaftNames) (log : List (List w8)) : IProp GF :=
  monoListLbOwn γ.commitedGn log

instance isCommit_pers (γ : RaftNames) (log : List (List w8)) :
    Persistent (isCommit (GF := GF) γ log) := by
  unfold isCommit; infer_instance

/-- Rocq `ownTerm` (see the file header for the encoding). -/
def ownTerm (γ : RaftNames) (node_id term : w64) : IProp GF :=
  iprop(∃ γn : GName, node_id ↪[γ.termGn]□ γn ∗ monoNatAuthOwn γn 1 (sint.nat term))
/-- Rocq `isTermLb` (see the file header for the encoding). -/
def isTermLb (γ : RaftNames) (node_id term : w64) : IProp GF :=
  iprop(∃ γn : GName, node_id ↪[γ.termGn]□ γn ∗ monoNatLbOwn γn (sint.nat term))

instance isTermLb_pers (γ : RaftNames) (node_id term : w64) :
    Persistent (isTermLb (GF := GF) γ node_id term) := by
  unfold isTermLb; infer_instance

def ownUnusedHeartbeatCtx (γ : RaftNames) (term : w64) (ctx : GoString) : IProp GF :=
  iprop(∃ (per_term_gn ctx_gn : GName),
    term ↪[γ.heartbeatGn]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghostVar ctx_gn (DFrac.own 1) (∅ : GSet w64))

def isHeartbeatCtx (γ : RaftNames) (term : w64) (ctx : GoString) (srvs : GSet w64) :
    IProp GF :=
  iprop(∃ (per_term_gn ctx_gn : GName),
    term ↪[γ.heartbeatGn]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghostVar ctx_gn DFrac.discard srvs)

instance isHeartbeatCtx_pers (γ : RaftNames) (term : w64) (ctx : GoString)
    (srvs : GSet w64) : Persistent (isHeartbeatCtx (GF := GF) γ term ctx srvs) := by
  unfold isHeartbeatCtx; infer_instance

theorem isHeartbeatCtx_agree (γ : RaftNames) (term : w64) (ctx : GoString)
    (srvs1 srvs2 : GSet w64) :
    ⊢ isHeartbeatCtx (GF := GF) γ term ctx srvs1 -∗
      isHeartbeatCtx γ term ctx srvs2 -∗
      ⌜srvs1 = srvs2⌝ := by
  unfold isHeartbeatCtx
  iintro ⟨%gn1, %cgn1, #Ht1, #Hc1, #Hv1⟩ ⟨%gn2, %cgn2, #Ht2, #Hc2, #Hv2⟩
  icases ghostMapElem_agree term γ.heartbeatGn _ _ gn1 gn2 $$ Ht1 Ht2 with %Heq1
  subst Heq1
  icases ghostMapElem_agree ctx gn1 _ _ cgn1 cgn2 $$ Hc1 Hc2 with %Heq2
  subst Heq2
  icases dghostVar_agree cgn1 srvs1 _ srvs2 _ $$ Hv1 Hv2 with %Heq3
  ipureintro
  exact Heq3

/-! ### Propositions defined in terms of the primitive ghost state.

This proof assumes there's only one configuration (for now). -/

/-- Rocq `Axiom ownCommittedInTerm`. -/
axiom ownCommittedInTerm {GF : BundledGFunctors} (γ : RaftNames) (term : w64)
  (log : List (List w8)) : IProp GF
/-- Rocq `Axiom isCommittedInTerm`. -/
axiom isCommittedInTerm {GF : BundledGFunctors} (γ : RaftNames) (term : w64)
  (log : List (List w8)) : IProp GF
/-- Rocq `Axiom isCommittedInTerm_pers`. -/
axiom isCommittedInTerm_pers {GF : BundledGFunctors} (γ : RaftNames) (term : w64)
  (log : List (List w8)) : Persistent (isCommittedInTerm (GF := GF) γ term log)
attribute [instance] isCommittedInTerm_pers

/-- Rocq `IsQuorum`. -/
def IsQuorum (quorum : GSet w64) : Prop :=
  GMap.size cfg < 2 * GMap.size (quorum ∩ cfg)

theorem quorums_intersect (q1 q2 : GSet w64) :
    IsQuorum cfg q1 → IsQuorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 := by
  intro Hsize1 Hsize2
  by_cases Hempty : q1 ∩ q2 = ∅
  · exfalso
    have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg := by
      rw [GMap.elem_of_subseteq]; set_solver
    have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) := by
      rw [GMap.elem_of_disjoint]
      intro x h1 h2
      rw [GMap.elem_of_intersection] at h1 h2
      have : x ∈ q1 ∩ q2 := (GMap.elem_of_intersection _ _ _).mpr ⟨h1.1, h2.1⟩
      rw [Hempty] at this
      exact GMap.not_elem_of_empty _ this
    have Hle := GMap.subseteq_size Hunion
    rw [GMap.size_union Hdisj] at Hle
    unfold IsQuorum at *
    omega
  · obtain ⟨x, Hx⟩ := GMap.set_choose_L _ Hempty
    exact ⟨x, by set_solver, by set_solver⟩

theorem quorums_subseteq (q1 q2 : GSet w64) :
    q1 ⊆ q2 → IsQuorum cfg q1 → IsQuorum cfg q2 := by
  intro Hsub Hsize
  unfold IsQuorum at *
  have Hs : q1 ∩ cfg ⊆ q2 ∩ cfg := by
    rw [GMap.elem_of_subseteq] at *; set_solver
  have := GMap.subseteq_size Hs
  omega

/-- Rocq `isStaleTerm`. -/
def isStaleTerm (γ : RaftNames) (term : w64) : IProp GF :=
  iprop(∃ quorum : GSet w64,
    "%Hquorum" ∷ ⌜IsQuorum cfg quorum⌝ ∗
    "#Hterm_lbs" ∷
      □ (∀ id, ⌜id ∈ quorum⌝ → ∃ term', isTermLb γ id term' ∗ ⌜sint.nat term < sint.nat term'⌝))

instance isStaleTerm_pers (γ : RaftNames) (term : w64) :
    Persistent (isStaleTerm (GF := GF) cfg γ term) := by
  unfold isStaleTerm; infer_instance

/-- Rocq `Axiom committed_in_term_agree`. -/
axiom committed_in_term_agree {GF : BundledGFunctors} (γ : RaftNames) (term : w64)
    (log1 log2 : List (List w8)) :
  ⊢ ownCommittedInTerm (GF := GF) γ term log1 -∗
    isCommittedInTerm γ term log2 -∗
    ⌜log2 <+: log1⌝

/-- Rocq `Axiom committed_in_term_stale`: when own and is have different terms,
the own term is stale. -/
axiom committed_in_term_stale (cfg : GSet w64) {GF : BundledGFunctors} [AllG GF]
    (γ : RaftNames) (term1 term2 : w64) (log1 log2 : List (List w8)) :
  term1 ≠ term2 →
  ⊢ ownCommittedInTerm (GF := GF) γ term1 log1 -∗
    isCommittedInTerm γ term2 log2 -∗
    isStaleTerm cfg γ term1

/-! TODO (Rocq): set this up to confirm backwards compatibility (i.e. if some raft
servers run the new code and some run the old code, system is still safe; only
the leader needs to run the new code in order for the system to tolerate
duplicate ReadIndex requests). -/

/-- Rocq `ownReads`: ownership of the reads queue, an authoritative monotone
list of `(start_index, saved_pred_gname)` pairs. The gnames are hidden
internally; the caller sees only `readsΦ`. -/
def ownReads (γ : RaftNames) (readsΦ : List (w64 × (List (List w8) → IProp GF))) : IProp GF :=
  iprop(∃ l : List (w64 × GName),
    ⌜l.map Prod.fst = readsΦ.map Prod.fst⌝ ∗
    monoListAuthOwn γ.readsGn 1 l ∗
    ∀ (i : Nat) (si : w64) (Φ : List (List w8) → IProp GF) (gn : GName),
      ⌜readsΦ[i]? = some (si, Φ)⌝ →
      ⌜l[i]? = some (si, gn)⌝ →
      savedPredOwn gn DFrac.discard Φ)

/-- Rocq `isInReads`: persistent witness that `(start_index, Φ)` is tracked in
the reads queue. -/
def isInReads (γ : RaftNames) (si : w64) (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(∃ (i : Nat) (gn : GName),
    monoListIdxOwn γ.readsGn i (si, gn) ∗
    savedPredOwn gn DFrac.discard Φ)

instance isInReads_persistent (γ : RaftNames) (si : w64) (Φ : List (List w8) → IProp GF) :
    Persistent (isInReads γ si Φ) := by
  unfold isInReads; infer_instance

/-- Insert a new read entry at the end of the list, obtaining a persistent witness. -/
theorem reads_insert (γ : RaftNames) (readsΦ : List (w64 × (List (List w8) → IProp GF)))
    (si : w64) (Φ : List (List w8) → IProp GF) :
    ⊢ ownReads γ readsΦ ==∗
      ownReads γ (readsΦ ++ [(si, Φ)]) ∗ isInReads γ si Φ := by
  unfold ownReads isInReads
  iintro ⟨%l, %Hfst, Hauth, #Hfor⟩
  imod saved_pred_alloc Φ DFrac.discard DFrac.valid_discard with ⟨%gn, #Hgn⟩
  imod monoListAuthOwn_update_app [(si, gn)] $$ Hauth with ⟨Hauth, #Hlb⟩
  have Hlen : l.length = readsΦ.length := by
    simpa using congrArg List.length Hfst
  imodintro
  isplitl [Hauth]
  · iexists l ++ [(si, gn)]
    isplitr
    · ipureintro
      simp only [List.map_append, Hfst, List.map_cons, List.map_nil]
    iframe Hauth
    iintro %i %si' %Φ' %gn' %Hreads %Hl'
    by_cases Hi : i < readsΦ.length
    · rw [List.getElem?_append_left Hi] at Hreads
      rw [List.getElem?_append_left (by omega)] at Hl'
      iapply Hfor $$ %i %si' %Φ' %gn' %Hreads %Hl'
    · have Hi' : readsΦ.length ≤ i := by omega
      rw [List.getElem?_append_right Hi'] at Hreads
      rw [List.getElem?_append_right (by omega)] at Hl'
      rcases Hdiff : i - readsΦ.length with _ | n
      · have Hdiff' : i - l.length = 0 := by omega
        rw [Hdiff'] at Hl'
        rw [Hdiff] at Hreads
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at Hreads Hl'
        obtain ⟨rfl, rfl⟩ := Hreads
        obtain ⟨-, rfl⟩ := Hl'
        iexact Hgn
      · rw [Hdiff] at Hreads
        simp at Hreads
  · iexists l.length, gn
    isplitl
    · iapply monoListIdxOwn_get l.length (si, gn) ?_ $$ Hlb
      simp
    · iexact Hgn

/-- Agreement: the witness corresponds to an entry in `readsΦ` with a
propositionally equal predicate (up to `▷`). -/
theorem reads_agree (γ : RaftNames) (readsΦ : List (w64 × (List (List w8) → IProp GF)))
    (si : w64) (Φ : List (List w8) → IProp GF) (x : List (List w8)) :
    ⊢ ownReads γ readsΦ -∗
      isInReads γ si Φ -∗
      ∃ (i : Nat) (Ψ : List (List w8) → IProp GF),
        ⌜readsΦ[i]? = some (si, Ψ)⌝ ∗
        ▷ (Φ x ≡ Ψ x) := by
  unfold ownReads isInReads
  iintro ⟨%l, %Hfst, Hauth, #Hfor⟩ ⟨%i, %gn, #Hidx, #Hgn⟩
  icases mono_list_auth_idx_lookup γ.readsGn 1 l i (si, gn) $$ Hauth Hidx with %Hl
  have Hsi : (readsΦ.map Prod.fst)[i]? = some si := by
    rw [← Hfst, List.getElem?_map, Hl]; rfl
  rw [List.getElem?_map] at Hsi
  obtain ⟨⟨si', Φ'⟩, HreadsΦ, Heq⟩ := Option.map_eq_some_iff.mp Hsi
  simp only at Heq
  subst Heq
  ihave #HΨ := Hfor $$ %i %si' %Φ' %gn %HreadsΦ %Hl
  iexists i, Φ'
  isplitr
  · ipureintro; exact HreadsΦ
  iapply saved_pred_agree gn _ _ Φ Φ' x $$ Hgn HΨ

/-- Rocq `Ncommit`. -/
def Ncommit : Namespace := N.@"commit"

/-- Rocq `isRaftCommitInv`. `Hread_aus`: permission to linearize reads on all
future logs (for any `Φ` stored in the reads queue, firing its AU against the
current committed log produces `Φ` applied to that log). `Hread_wits`:
witnesses that reads were linearized on every index starting at their
respective starting index. -/
def isRaftCommitInv (γ : RaftNames) : IProp GF :=
  inv Ncommit iprop(∃ (term : w64) (log : List (List w8))
      (readsΦ : List (w64 × (List (List w8) → IProp GF))),
    "commit" ∷ ownCommitAuth γ log ∗
    "#Hcommit" ∷ isCommittedInTerm γ term log ∗
    "reads" ∷ ownReads γ readsΦ ∗
    "#Hread_aus" ∷ □ (∀ (Φ : List (List w8) → IProp GF), ⌜Φ ∈ readsΦ.map Prod.snd⌝ →
        ∀ log : List (List w8),
          ownCommitAuth γ log ={⊤ \ ↑N}=∗ ownCommitAuth γ log ∗ Φ log) ∗
    "#Hread_wits" ∷ □ (∀ (start_index : w64) (Φ : List (List w8) → IProp GF),
        ⌜(start_index, Φ) ∈ readsΦ⌝ → ∀ index : w64,
          ⌜uint.nat start_index ≤ uint.nat index ∧ uint.nat index ≤ log.length⌝ →
          Φ (log.take (uint.nat index))))

instance isRaftCommitInv_pers (γ : RaftNames) :
    Persistent (isRaftCommitInv (GF := GF) γ) := by
  unfold isRaftCommitInv; infer_instance

/-- Rocq `isReadIndex`: a read index witness. Given any committed log at least
as long as `index`, opening the invariant at mask `⊤` lets us fire the stored
AU to get `Φ log`. Needs `£ 2`: one credit to open the invariant (strip `▷`),
one to strip the `▷` from `saved_pred_agree`. -/
def isReadIndex (γ : RaftNames) (index : w64) (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(□ (∀ log : List (List w8), ⌜uint.nat index ≤ log.length⌝ → ⌜log.length < 2 ^ 64⌝ →
       £ 2 -∗ isCommit γ log ={⊤}=∗ Φ log))

instance isReadIndex_pers (γ : RaftNames) (index : w64) (Φ : List (List w8) → IProp GF) :
    Persistent (isReadIndex γ index Φ) := by
  unfold isReadIndex; infer_instance

theorem isInReads_to_valid (γ : RaftNames) (i j : w64) (Φ : List (List w8) → IProp GF) :
    "#Hinv" ∷ isRaftCommitInv γ ∗
    "#Hr" ∷ isInReads γ j Φ ∗
    "%Hj" ∷ ⌜uint.nat j ≤ uint.nat i⌝ ⊢
    isReadIndex γ i Φ := by
  iintro ⟨#Hinv, #Hr, %Hj⟩
  unfold isReadIndex
  imodintro
  iintro %log_wit %Hlog_wit %Hoverflow ⟨Hlc, Hlc2⟩ #Hlog_wit
  unfold isRaftCommitInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icases mono_list_auth_lb_valid γ.commitedGn _ log log_wit $$ commit Hlog_wit with % ⟨-, Hle⟩
  icases reads_agree γ readsΦ j Φ log_wit $$ reads Hr with ⟨%i', %Ψ, %Hr_lookup, #HΦ⟩
  ihave Hwit := Hread_wits $$ %j %Ψ %(List.mem_of_getElem? Hr_lookup) %(W64 log_wit.length)
  ispecialize Hwit $$ %(by
    have := Hle.length_le
    constructor <;> word)
  rw [show uint.nat (W64 log_wit.length) = log_wit.length by word,
    ← List.prefix_iff_eq_take.mp Hle]
  imod lc_fupd_elim_later $$ Hlc2 HΦ with #HΦ'
  imod Hclose $$ [commit reads] with -
  · inext
    iexists term, log, readsΦ
    iframe # ∗
  imodintro
  -- (`irewrite [HΦ']` fails: no `NonExpansive (fun x => x)` instance for the motive)
  ihave Hiff := internalEq_iff _ _ $$ HΦ'
  icases Hiff with ⟨-, Hiff⟩
  iapply Hiff $$ Hwit

theorem mask_diff_Ncommit : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑Ncommit := mask_diff_ndot N "commit"

/-- Try to add a read with continuation `Φ` to be executed forever starting at
the committed index from term `term`. -/
theorem try_read (γ : RaftNames) (term : w64) (log : List (List w8))
    (Φ : List (List w8) → IProp GF) :
    "Hlc" ∷ £ 1 ∗
    "%Hno_overflow" ∷ ⌜log.length < 2 ^ 64⌝ ∗
    "#Hinv" ∷ isRaftCommitInv γ ∗
    "Hcom" ∷ ownCommittedInTerm γ term log ∗
    "#Hau" ∷ □ (|={⊤ \ ↑N, ∅}=> ∃ log, ownCommit γ log ∗
      (ownCommit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)) ⊢
    |={⊤}=> ∃ stale_ids : GSet w64,
      □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', isTermLb γ id term' ∗
          ⌜sint.nat term < sint.nat term'⌝) ∗
      ownCommittedInTerm γ term log ∗
      (isReadIndex γ (W64 log.length) Φ ∨ ⌜IsQuorum cfg stale_ids⌝) := by
  iintro ⟨Hlc, %Hno_overflow, #Hinv, Hcom, #Hau⟩
  ihave #Hinv2 := Hinv
  iunfold isRaftCommitInv at Hinv2
  iinv Hinv2 with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%inv_term, %inv_log, %inv_readsΦ, Hcommit_auth, #Hcommit_term, Hreads,
    #Hread_aus, #Hread_wits⟩
  by_cases Hterm : term = inv_term
  · -- Same term: the committed log in the invariant matches our term.
    subst Hterm
    icases committed_in_term_agree γ term log inv_log $$ Hcom Hcommit_term with %Hle
    -- Insert `(W64 inv_log.length, Φ)` into the reads queue.
    imod reads_insert γ inv_readsΦ (W64 inv_log.length) Φ $$ Hreads with ⟨Hreads, #Hin_reads⟩
    -- Re-establish `Hread_aus` for the extended list.
    ihave #Hread_aus_new : (□ (∀ (Φ0 : List (List w8) → IProp GF),
        ⌜Φ0 ∈ (inv_readsΦ ++ [(W64 inv_log.length, Φ)]).map Prod.snd⌝ →
        ∀ log0 : List (List w8),
          ownCommitAuth γ log0 ={⊤ \ ↑N}=∗ ownCommitAuth γ log0 ∗ Φ0 log0) : IProp GF) $$ []
    · imodintro
      iintro %Φ0 %Hin %log0 Hca
      rw [List.map_append, List.mem_append] at Hin
      rcases Hin with Hin | Hin
      · iapply Hread_aus $$ %Φ0 %Hin %log0 Hca
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at Hin
        subst Hin
        imod Hau with ⟨%log_au, Hcommit, Hclose'⟩
        icases monoListAuthOwn_agree γ.commitedGn _ _ log0 log_au $$ Hca Hcommit with
          % ⟨-, Heq⟩
        subst Heq
        imod Hclose' $$ Hcommit with #HΦ
        imodintro
        iframe # ∗
    -- Close the invariant with the extended reads list.
    imod (fupd_mask_subseteq (PROP := IProp GF) mask_diff_Ncommit) with Hmask
    imod Hau with ⟨%log', Hcom', Hclose'⟩
    icases monoListAuthOwn_agree γ.commitedGn _ _ log' inv_log $$ Hcom' Hcommit_auth with
      % ⟨-, Heq⟩
    subst Heq
    imod Hclose' $$ Hcom' with #HΦ
    imod Hmask with -
    imod Hclose $$ [Hcommit_auth Hreads] with -
    · inext
      iexists term, log', inv_readsΦ ++ [(W64 log'.length, Φ)]
      iframe # ∗
      imodintro
      iintro %start_index %Φ0 %Hindex %index %Hindex2
      rw [List.mem_append] at Hindex
      rcases Hindex with Hindex | Hindex
      · iapply Hread_wits $$ %start_index %Φ0 %Hindex %index %Hindex2
      · simp only [List.mem_singleton, Prod.mk.injEq] at Hindex
        obtain ⟨rfl, rfl⟩ := Hindex
        have Hlen := Hle.length_le
        rw [List.take_of_length_le (by word)]
        iexact HΦ
    imodintro
    iexists ∅
    isplitr
    · imodintro
      iintro %id %Hid
      exact absurd Hid (GMap.not_elem_of_empty _)
    iframe Hcom
    ileft
    iapply isInReads_to_valid γ (W64 log.length) (W64 log'.length) Φ
    iframe # ∗
    ipureintro
    have Hlen := Hle.length_le
    word
  · -- Different term: term is stale.
    ihave #Hstale := committed_in_term_stale cfg γ term inv_term log inv_log Hterm $$
      Hcom Hcommit_term
    imod Hclose $$ [Hcommit_auth Hreads] with -
    · inext
      iexists inv_term, inv_log, inv_readsΦ
      iframe # ∗
    imodintro
    iunfold isStaleTerm at Hstale
    icases Hstale with ⟨%quorum, %Hquorum, #Hterm_lbs⟩
    iexists quorum
    iframe # ∗
    iright
    ipureintro
    exact Hquorum

/-- Rocq `isHeartbeatCtxStale`. -/
def isHeartbeatCtxStale (γ : RaftNames) (term : w64) (ctx : GoString)
    (stale_ids : GSet w64) : IProp GF :=
  iprop(isHeartbeatCtx γ term ctx stale_ids ∗
    □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', isTermLb γ id term' ∗
        ⌜sint.nat term < sint.nat term'⌝))

instance isHeartbeatCtxStale_pers (γ : RaftNames) (term : w64) (ctx : GoString)
    (stale_ids : GSet w64) : Persistent (isHeartbeatCtxStale (GF := GF) γ term ctx stale_ids) := by
  unfold isHeartbeatCtxStale; infer_instance

/-- Rocq `isHeartbeatRequest`. -/
def isHeartbeatRequest (γ : RaftNames) (term : w64) (ctx : List w8) : IProp GF :=
  iprop(∃ stale_ids, isHeartbeatCtxStale γ term ctx stale_ids)

/-- Rocq `isHeartbeatResp`: confirms that `from` was not stale back when `ctx`
was first used in `term`. -/
def isHeartbeatResp (γ : RaftNames) («from» : w64) (term : w64) (ctx : List w8) : IProp GF :=
  iprop(∃ srvs, isHeartbeatCtx γ term ctx srvs ∗ ⌜«from» ∉ srvs⌝)

/-- Rocq `isHeartbeatAck`: witnesses that `from` acknowledged heartbeat
context `ctx` in `term`, confirming `from` was not stale at that point. Similar
to `isHeartbeatResp` but used as a precondition for `recvAck`. -/
def isHeartbeatAck (γ : RaftNames) («from» : w64) (term : w64) (ctx : GoString) : IProp GF :=
  iprop(∃ srvs, isHeartbeatCtx γ term ctx srvs ∗ ⌜«from» ∉ srvs⌝)

instance isHeartbeatAck_pers (γ : RaftNames) («from» : w64) (term : w64) (ctx : GoString) :
    Persistent (isHeartbeatAck (GF := GF) γ «from» term ctx) := by
  unfold isHeartbeatAck; infer_instance

theorem heartbeat_ack_not_stale (γ : RaftNames) («from» : w64) (term : w64) (ctx : GoString)
    (stale_ids : GSet w64) :
    ⊢ isHeartbeatCtx (GF := GF) γ term ctx stale_ids -∗
      isHeartbeatAck γ «from» term ctx -∗
      ⌜«from» ∉ stale_ids⌝ := by
  iintro #Hctx #Hack
  unfold isHeartbeatAck
  icases Hack with ⟨%srvs, #Hctx', %Hnot_in⟩
  icases isHeartbeatCtx_agree γ term ctx stale_ids srvs $$ Hctx Hctx' with %Heq
  subst Heq
  ipureintro
  exact Hnot_in

theorem start_heartbeat (stale_ids : GSet w64) (γ : RaftNames) (term : w64) (ctx : GoString) :
    ⊢ □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', isTermLb (GF := GF) γ id term' ∗
          ⌜sint.nat term < sint.nat term'⌝) -∗
      ownUnusedHeartbeatCtx γ term ctx ==∗
      isHeartbeatCtxStale γ term ctx stale_ids := by
  iintro #Hstale Hunused
  unfold ownUnusedHeartbeatCtx
  icases Hunused with ⟨%per_term_gn, %ctx_gn, #Hterm, #Hctx, Hvar⟩
  imod dghostVar_update stale_ids ctx_gn _ $$ Hvar with Hvar
  imod dghostVar_persist ctx_gn 1 stale_ids $$ Hvar with #Hvar
  imodintro
  unfold isHeartbeatCtxStale isHeartbeatCtx
  isplitl
  · iexists per_term_gn, ctx_gn
    iframe # ∗
  · iexact Hstale

/-- Rocq `ownReadReqCtx`. -/
def ownReadReqCtx (γ : RaftNames) (read_req_ctx : GoString) : IProp GF :=
  iprop(∃ γreq : GName,
    "#Hγreq" ∷ read_req_ctx ↪[γ.readReqGn]□ γreq ∗
    "Hreq" ∷ savedPredOwn γreq (DFrac.own 1) (fun (_ : List (List w8)) => iprop(True)))

/-- Rocq `isReadReqCtx`. -/
def isReadReqCtx (γ : RaftNames) (read_req_ctx : GoString)
    (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(∃ γreq : GName,
    "#Hγreq" ∷ read_req_ctx ↪[γ.readReqGn]□ γreq ∗
    "#Hreq" ∷ savedPredOwn γreq DFrac.discard Φ ∗
    "#Hau" ∷ □ (|={⊤ \ ↑N, ∅}=> ∃ log, ownCommit γ log ∗
      (ownCommit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)))

instance isReadReqCtx_pers (γ : RaftNames) (read_req_ctx : GoString)
    (Φ : List (List w8) → IProp GF) : Persistent (isReadReqCtx γ read_req_ctx Φ) := by
  unfold isReadReqCtx; infer_instance

theorem start_req_ctx (Φ : List (List w8) → IProp GF) (req_ctx : GoString) (index : w64)
    (γ : RaftNames) :
    ownReadReqCtx γ req_ctx ∗
    □ (|={⊤ \ ↑N, ∅}=> ∃ log, ownCommit γ log ∗ (ownCommit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)) ⊢
    |={⊤}=> isReadReqCtx γ req_ctx Φ := by
  iintro ⟨Hown, #Hau⟩
  iNamed Hown
  imod saved_pred_update Φ γreq _ $$ Hreq with Hreq
  imod saved_pred_persist γreq _ Φ $$ Hreq with #Hreq
  imodintro
  unfold isReadReqCtx
  iexists γreq
  iframe # ∗

/-- Rocq `isMsgReadIndex`. -/
def isMsgReadIndex (γ : RaftNames) (read_req_ctx : GoString) : IProp GF :=
  iprop(∃ Φ, isReadReqCtx γ read_req_ctx Φ)

/-- Rocq `isMsgReadIndexResp`. -/
def isMsgReadIndexResp (γ : RaftNames) (read_req_ctx : GoString) (index : w64) : IProp GF :=
  iprop(∃ Φ, isReadReqCtx γ read_req_ctx Φ ∗ isReadIndex γ index Φ)

/-- If a quorum of servers acked a heartbeat context, and the stale set for that
context were also a quorum, they would intersect — but each acking server is
provably NOT in the stale set. Contradiction. -/
theorem heartbeat_ack_quorum_not_stale (γ : RaftNames) (term : w64) (ctx : GoString)
    (stale_ids ack_srvs : GSet w64) :
    IsQuorum cfg ack_srvs →
    IsQuorum cfg stale_ids →
    ⊢ isHeartbeatCtx (GF := GF) γ term ctx stale_ids -∗
      □ (∀ id, ⌜id ∈ ack_srvs⌝ → isHeartbeatAck γ id term ctx) -∗
      False := by
  intro Hack_quorum Hstale_quorum
  iintro #Hctx #Hacks
  obtain ⟨x, Hx_ack, Hx_stale⟩ := quorums_intersect cfg _ _ Hack_quorum Hstale_quorum
  ihave #Hack_x := Hacks $$ %x %Hx_ack
  icases heartbeat_ack_not_stale γ x term ctx stale_ids $$ Hctx Hack_x with %Hnot
  exact absurd Hx_stale Hnot

end global_proof

/-- Rocq `Axiom ownRaft`. -/
axiom ownRaft [FfiSyntax] {GF : BundledGFunctors} (γ : RaftNames) (rf : v3.raft.t) : IProp GF

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]


/-- Lean addition: `array_acc`, putting back the same element. -/
theorem array_acc_same {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (i : Int)
    (dq : DFrac) (n : Int) (a : array.t V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

/-- Lean deviation (Rocq: `{{{ True }}} p.IsSingleton() {{{ RET #false; True }}}`,
admitted as trusted, which is false: `IsSingleton` returns `true` for a
single-voter configuration). The true spec: given the `ProgressTracker` and
its two voter maps (`Voters[0]`, `Voters[1]`, both non-nil), the result is
`len(Voters[0]) == 1 && len(Voters[1]) == 0`, where `len` is the (wrapping)
`int` size of the map. -/
theorem ProgressTracker.wp_IsSingleton (p : Loc) (dq : DFrac) (pt : v3.tracker.ProgressTracker.t)
    (v0 v1 : Loc) (m0 m1 : GMap w64 Unit) (dq0 dq1 : DFrac) :
    {{ "Hp" ∷ p ↦{dq} pt ∗
        "%Hvoters" ∷ ⌜pt.Config'.Voters'.arr = [v0, v1]⌝ ∗
        "Hm0" ∷ (v0 ↦${dq0} m0 : IProp GF) ∗
        "Hm1" ∷ (v1 ↦${dq1} m1 : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType v3.tracker.ProgressTracker @!! go!"IsSingleton"))
        (Val #()))
    {{ RET #(decide (W64 (GMap.size m0) = W64 1 ∧ W64 (GMap.size m1) = W64 0));
        p ↦{dq} pt ∗ v0 ↦${dq0} m0 ∗ v1 ↦${dq1} m1 }} := by
  wp_start as ⟨Hp, %Hvoters, Hm0, Hm1⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases typedPointsto_not_null_dup _ _ _ $$ Config with ⟨Config, %HnnC⟩
  iStructNamed Config
  icases array_acc_same (GF := GF) _ (sint.Z (W64 0)) _ _ _ v0 (by decide) (by simp [Hvoters])
    $$ Voters with ⟨Hv0, Voters⟩
  wp_auto
  wp_apply wp_map_len $$ Hm0 with Hm0
  ihave Voters := Voters $$ Hv0
  wp_if_destruct
  · icases array_acc_same (GF := GF) _ (sint.Z (W64 1)) _ _ _ v1 (by decide) (by simp [Hvoters])
      $$ Voters with ⟨Hv1, Voters⟩
    wp_auto
    wp_apply wp_map_len $$ Hm1 with Hm1
    ihave Voters := Voters $$ Hv1
    rw [show decide (W64 ↑m0.size = W64 1 ∧ W64 ↑m1.size = W64 0) = decide (W64 ↑m1.size = W64 0)
      by simp [Hif]]
    iapply HΦ
    iframe Hm0 Hm1
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe Progress Votes MaxInflight MaxInflightBytes
    iapply typedPointsto_combine _ _ _ HnnC
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  · rw [show decide (W64 ↑m0.size = W64 1 ∧ W64 ↑m1.size = W64 0) = false from
      decide_eq_false (fun h => Hif h.1)]
    iapply HΦ
    iframe Hm0 Hm1
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe Progress Votes MaxInflight MaxInflightBytes
    iapply typedPointsto_combine _ _ _ HnnC
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe

theorem raft.wp_committedEntryInCurrentTerm (r : Loc) (rf : v3.raft.t) (γ : RaftNames) :
    {{ r ↦ rf ∗ ownRaft (GF := GF) γ rf }}
      (App (Val (r @!! go.GoType.PointerType v3.raft @!! go!"committedEntryInCurrentTerm"))
        (Val #()))
    {{ (c : Bool), RET #c; r ↦ rf ∗ ownRaft γ rf ∗
        if c then ∃ l, isCommittedInTerm γ rf.Term' l else True }} := by
  -- Unprovable: `ownRaft` is an opaque axiom (as in Rocq). It gives neither ownership of
  -- `rf.raftLog` (needed to run `raftLog.term`, which calls the `Storage` interface methods
  -- `Term`/`FirstIndex`/`LastIndex` and `Logger.Panicf`) nor any link between the terms in the
  -- log and `isCommittedInTerm` (also an axiom). Replacing `ownRaft` by a definition would
  -- need representation predicates for `raftLog`/`unstable`, specs for user-supplied `Storage`
  -- and `Logger` implementations, and a ghost protocol relating storage terms to
  -- `isCommittedInTerm`; none of these exist (in Rocq or here).
  sorry -- Rocq: Admitted (trusted)

/-- Rocq `isReadIndexRequest`. -/
def isReadIndexRequest (γ : RaftNames) (r : Loc) (read_req_ctx : GoString) (index : w64) :
    IProp GF :=
  iprop(∃ read_req : v3.readIndexRequest.t,
    "#r" ∷ r ↦□ read_req ∗
    "#ctx" ∷ read_req.req'.Context' ↦*□ read_req_ctx ∗
    "%Hindex" ∷ ⌜read_req.index' = index⌝ ∗
    "#His_read" ∷ (∃ Φ, isReadReqCtx γ read_req_ctx Φ))

instance isReadIndexRequest_pers (γ : RaftNames) (r : Loc) (read_req_ctx : GoString)
    (index : w64) : Persistent (isReadIndexRequest (GF := GF) γ r read_req_ctx index) := by
  unfold isReadIndexRequest; infer_instance

/-- Rocq `ownHeartbeatAuth`. -/
def ownHeartbeatAuth (γ : RaftNames) (term : w64) (highest_index : w64) : IProp GF :=
  iprop(∃ (per_term_gn : GName) (used : GMap GoString GName),
    term ↪[γ.heartbeatGn]□ per_term_gn ∗
    ghostMapAuth per_term_gn 1 used ∗
    ⌜∀ k, k ∈ used → k = [] ∨ k.length = 8 ∧ uint.Z (leToU64 k) ≤ uint.Z highest_index⌝)

/-- Rocq `ownReadOnly`. The entries of `read_reqs` are
`((read_req_ctx, index), stale_ids)`.

Lean deviation: an extra parameter `n`, the number of read requests added
so far (`confirmedReads + len(unconfirmedReads)` without wrap-around), with
`"%Hcount" : uint.nat confirmedReads + len unconfirmedReads = n ∧ n < 2^64`.
The heartbeat context of a new request is `u64Le (n + 1)`, which must not
wrap around to an already used context, so `wp_readOnly_addRequest` requires
`n < 2^64 - 1` (Rocq: no `n`, and the overflow side condition is admitted). -/
def ownReadOnly (γ : RaftNames) (r : Loc) (term : w64) (n : Nat) : IProp GF :=
  iprop(∃ (ro : v3.readOnly.t) (acks : GMap w64 w64) (unconfirmedReads : List Loc)
      (read_reqs : List ((GoString × w64) × GSet w64)),
    "r" ∷ r ↦ ro ∗
    "Hacks" ∷ ro.acks' ↦$ acks ∗
    "#Hacks_wits" ∷ □ (∀ (voterId ackedIdx : w64),
        ⌜acks !! voterId = some ackedIdx⌝ →
        isHeartbeatAck γ voterId term (u64Le ackedIdx)) ∗
    "%Hoption" ∷ ⌜ro.option' = W64 0⌝ ∗ -- equals ReadOnlySafe
    "%Hcount" ∷ ⌜uint.nat ro.confirmedReads' + unconfirmedReads.length = n ∧ n < 2 ^ 64⌝ ∗
    "unconfirmedReads" ∷ ro.unconfirmedReads' ↦* unconfirmedReads ∗
    "unconfirmedReads_cap" ∷ ownSliceCap Loc ro.unconfirmedReads' (DFrac.own 1) ∗
    "#HunconfirmedReads" ∷ □ ([∗list] i ↦ r; x ∈ unconfirmedReads; read_reqs,
        "#readIndexRequest" ∷ isReadIndexRequest γ r x.1.1 x.1.2 ∗
        "#Hhb" ∷ isHeartbeatCtxStale γ term
          (u64Le (ro.confirmedReads' + W64 (i + 1 : Nat))) x.2 ∗
        "%Hstale_contains" ∷ ⌜unionList ((read_reqs.take i).map Prod.snd) ⊆ x.2⌝ ∗
        "#Hstale_or_safe" ∷ (⌜IsQuorum cfg x.2⌝ ∨
          (∃ Φ, isReadReqCtx γ x.1.1 Φ ∗ isReadIndex γ x.1.2 Φ))) ∗
    "Hhb_auth" ∷ ownHeartbeatAuth γ term (ro.confirmedReads' + W64 unconfirmedReads.length))

theorem ownHeartbeatAuth_new (stale_ids : GSet w64) (γ : RaftNames) (term : w64)
    (highest_index : w64) :
    uint.Z highest_index < 2 ^ 64 - 1 →
    ⊢ ownHeartbeatAuth (GF := GF) γ term highest_index ==∗
      ownHeartbeatAuth γ term (highest_index + W64 1) ∗
      isHeartbeatCtx γ term (u64Le (highest_index + W64 1)) stale_ids := by
  intro Hno
  unfold ownHeartbeatAuth isHeartbeatCtx
  iintro ⟨%per_term_gn, %used, #Hp, Hauth, %Hused⟩
  imod dghostVar_alloc stale_ids with ⟨%gn, H⟩
  imod dghostVar_persist gn 1 stale_ids $$ H with #H
  have Hfresh : used.lookup (u64Le (highest_index + W64 1)) = none := by
    cases h : used.lookup (u64Le (highest_index + W64 1)) with
    | none => rfl
    | some v =>
      exfalso
      have hmem : u64Le (highest_index + W64 1) ∈ used := by
        rw [GMap.mem_iff]; exact Option.isSome_iff_exists.mpr ⟨v, h⟩
      rcases Hused _ hmem with h1 | ⟨-, h2⟩
      · have := u64Le_length (highest_index + W64 1)
        rw [h1] at this; simp at this
      · rw [u64Le_to_word] at h2
        word
  imod ghost_map_insert_persist (u64Le (highest_index + W64 1)) gn Hfresh $$ Hauth
    with ⟨Hauth, #Hk⟩
  imodintro
  isplitl [Hauth]
  · iexists per_term_gn, _
    iframe # ∗
    ipureintro
    intro k hk
    have hk' := (GMap.lookup_insert_is_Some used _ k gn).mp hk
    rcases hk' with rfl | ⟨-, hk'⟩
    · right
      rw [u64Le_to_word, u64Le_length]
      exact ⟨rfl, by word⟩
    · rcases Hused k hk' with h | ⟨h1, h2⟩
      · left; exact h
      · right; exact ⟨h1, by word⟩
  · iexists per_term_gn, gn
    iframe #

theorem ownHeartbeatAuth_agree (stale_ids : GSet w64) (γ : RaftNames) (term : w64)
    (ctx : GoString) (highest_index : w64) :
    ctx ≠ [] →
    ⊢ isHeartbeatCtx (GF := GF) γ term ctx stale_ids -∗
      ownHeartbeatAuth γ term highest_index -∗
      ⌜ctx.length = 8 ∧ uint.Z (leToU64 ctx) ≤ uint.Z highest_index⌝ := by
  intro Hctx
  unfold ownHeartbeatAuth isHeartbeatCtx
  iintro ⟨%gn1, %cgn1, #Hp, #Hfrag, -⟩ ⟨%gn2, %used, #Hp2, Hauth, %Hin⟩
  icases ghostMapElem_agree term γ.heartbeatGn _ _ gn1 gn2 $$ Hp Hp2 with %Heq
  subst Heq
  icases ghost_map_lookup $$ Hauth Hfrag with %Hl
  ipureintro
  have hmem : ctx ∈ used := by
    rw [GMap.mem_iff]; exact Option.isSome_iff_exists.mpr ⟨cgn1, Hl⟩
  rcases Hin ctx hmem with h | h
  · exact absurd h Hctx
  · exact h

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
theorem wp_readOnly_recvAck (γ : RaftNames) (r : Loc) (term : w64) («from» : w64)
    (ctx_sl : slice.t) (ctx : List w8) (v : w64) (n : Nat) :
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "Hown" ∷ ownReadOnly cfg γ r term n ∗
        "Hctx" ∷ ctx_sl ↦* ctx ∗
        "#Hack" ∷ isHeartbeatAck γ «from» term ctx }}
      (App (App (Val (r @!! go.GoType.PointerType v3.readOnly @!! go!"recvAck")) (Val #«from»))
        (Val #ctx_sl))
    {{ RET #(); ownReadOnly cfg γ r term n }} := by
  wp_start as ⟨Hown, Hctx, #Hack⟩
  iunfold ownReadOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  wp_if_destruct
  · iapply HΦ
    unfold ownReadOnly
    iexists ro, acks, unconfirmedReads, read_reqs
    iframe # ∗
    ipureintro; exact ⟨Hoption, Hcount⟩
  · wp_apply wp_map_lookup1 $$ Hacks as Hacks
    ihave %Hctx_len := ownSlice_len _ _ _ $$ Hctx
    iunfold isHeartbeatAck at Hack
    icases Hack with ⟨%srvs, #Hhb_ctx, %Hnot⟩
    have Hne : ctx ≠ [] := by
      intro h; rw [h] at Hctx_len; simp at Hctx_len; apply Hif; word
    icases ownHeartbeatAuth_agree srvs γ term ctx _ Hne $$ Hhb_ctx Hhb_auth with
      % ⟨Hlen, Hbounds⟩
    rw [show ctx = ctx ++ [] by simp]
    wp_apply encoding.binary.wp_LittleEndian_Uint64 ctx_sl ctx _ [] Hlen $$ [$Hctx] as Hctx
    wp_func_call
    wp_call
    rw [List.append_nil]
    -- the new acked index `nv` has a heartbeat-ack witness
    have Hfin : ∀ nv : w64, (nv = leToU64 ctx ∨ acks !! «from» = some nv) →
        ⊢ (□ (∀ (voterId ackedIdx : w64), ⌜acks !! voterId = some ackedIdx⌝ →
              isHeartbeatAck (GF := GF) γ voterId term (u64Le ackedIdx))) -∗
          isHeartbeatCtx γ term ctx srvs -∗
          □ (∀ (voterId ackedIdx : w64), ⌜(<[«from» := nv]> acks) !! voterId = some ackedIdx⌝ →
              isHeartbeatAck γ voterId term (u64Le ackedIdx)) := by
      intro nv Hnv
      iintro #Hacks_wits #Hhb_ctx
      imodintro
      iintro %voterId %ackedIdx %Hlookup
      by_cases Hv : «from» = voterId
      · subst Hv
        rw [GMap.lookup_insert] at Hlookup
        cases Hlookup
        rcases Hnv with rfl | Hnv
        · rw [leToU64_le ctx Hlen]
          unfold isHeartbeatAck
          iexists srvs
          iframe #
          ipureintro; exact Hnot
        · iapply Hacks_wits $$ %«from» %nv %Hnv
      · rw [GMap.lookup_insert_ne _ _ Hv] at Hlookup
        iapply Hacks_wits $$ %voterId %ackedIdx %Hlookup
    wp_if_destruct
    · have Hsome : acks !! «from» = some ((acks !! «from»).getD (zero_val w64)) := by
        cases h : acks !! «from» with
        | none =>
          rw [h, Option.getD_none, show zero_val w64 = W64 0 from rfl] at Hif
          word
        | some w => rfl
      wp_apply wp_mapInsert $$ Hacks as Hacks
      iapply HΦ
      ihave #Hw := Hfin _ (Or.inr Hsome) $$ Hacks_wits Hhb_ctx
      unfold ownReadOnly
      iexists ro, _, unconfirmedReads, read_reqs
      iframe # ∗
      ipureintro; exact ⟨Hoption, Hcount⟩
    · wp_apply wp_mapInsert $$ Hacks as Hacks
      iapply HΦ
      ihave #Hw := Hfin _ (Or.inl rfl) $$ Hacks_wits Hhb_ctx
      unfold ownReadOnly
      iexists ro, _, unconfirmedReads, read_reqs
      iframe # ∗
      ipureintro; exact ⟨Hoption, Hcount⟩

/-- Rocq `ownAckedIndexer`. The Rocq Texan triple (an `iProp`) is written out. -/
def ownAckedIndexer (i : interface.t_ok) (acks : GMap w64 w64) (I : IProp GF) : IProp GF :=
  iprop("HI" ∷ I ∗
    "#HAckedIndex" ∷ (∀ voterID : w64, □ ∀ Φ : val → IProp GF, I -∗
      ▷ (I -∗ Φ (PairV #((acks !! voterID).getD (W64 0)) #(decide ((acks !! voterID).isSome)))) -∗
      WP (App (Val #(methods i.ty go!"AckedIndex" i.v)) (Val #voterID)) {{ Φ }}))

end wps

/-- Rocq `Axiom JointConfig.wp_CommittedIndex`. (Rocq's statement does not bind
the `quorum` package assumptions; here they are bound explicitly.) -/
axiom JointConfig.wp_CommittedIndex (cfg : GSet w64)
    [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]
    (l : interface.t_ok) (acks : GMap w64 w64) (c : v3.quorum.JointConfig.t) (voters_ref : Loc)
    (voters : GMap w64 Unit) (I : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
        "Hl" ∷ ownAckedIndexer l acks I ∗
        "%Hc" ∷ ⌜c.arr = [voters_ref, map.nil]⌝ ∗
        "voters" ∷ voters_ref ↦$ voters ∗
        "%Hvoters_cfg" ∷ ⌜domSet voters = cfg⌝ }}
      (App (Val (c @!! v3.quorum.JointConfig @!! go!"CommittedIndex")) (Val #(interface.ok l)))
    {{ (c : w64), RET #c; ownAckedIndexer l acks I ∗
        voters_ref ↦$ voters ∗
        ⌜0 ≤ sint.Z c ∧
          ∃ srvs, IsQuorum cfg srvs ∧
            (∀ s, s ∈ srvs → sint.Z c ≤ sint.Z ((acks !! s).getD (W64 0)))⌝ }}

theorem big_sepL2_drop {PROP : Type _} [BI PROP] [BIAffine PROP] {A B : Type _}
    (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B) (n : Nat) :
    ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) ⊢
      [∗list] k ↦ x;y ∈ l1.drop n;l2.drop n, Φ (n + k) x y := by
  induction n generalizing Φ l1 l2 with
  | zero => simp only [List.drop_zero, Nat.zero_add]; exact .rfl
  | succ n ih =>
    match l1, l2 with
    | [], [] => simp only [List.drop_nil]; exact affine
    | [], _ :: _ => exact false_elim
    | _ :: _, [] => exact false_elim
    | x :: xs, y :: ys =>
      refine BigSepL2.bigSepL2_cons.1.trans (sep_elim_right.trans ((ih (fun k => Φ (k + 1)) xs ys).trans ?_))
      simp only [List.drop_succ_cons]
      rw [show (fun k x y => Φ (n + k + 1) x y) = (fun k x y => Φ (n + 1 + k) x y) by
        funext k x y; rw [Nat.add_right_comm]]

section wps2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]


/-- Rocq `MsgReadIndex`. -/
def MsgReadIndex : w32 := W32 15

theorem raft.wp_sendMsgReadIndexresponse (γ : RaftNames) (r : Loc) (rf : v3.raft.t)
    (m : v3.raftpb.Message.t) :
    {{ "Hr" ∷ r ↦ rf ∗
        "Hrf" ∷ ownRaft (GF := GF) γ rf ∗
        "%HmType" ∷ ⌜m.Type' = MsgReadIndex⌝ ∗
        "#Hcom_in_term" ∷ True }}
      (App (App (Val (@! v3.sendMsgReadIndexResponse)) (Val #r)) (Val #m))
    {{ RET #(); True }} := by
  -- Unprovable as stated: `"#Hcom_in_term" ∷ True` is a placeholder (as in Rocq) for what
  -- `readOnly.addRequest` needs (`isRaftCommitInv`, `ownCommittedInTerm`,
  -- `isReadReqCtx`, and now the request-count bound `n < 2^64 - 1`), and `ownRaft`
  -- (an opaque axiom, see `raft.wp_committedEntryInCurrentTerm`) provides neither
  -- `ownReadOnly` for `rf.readOnly'` nor the state used by `bcastHeartbeat`
  -- (`trk.Visit` with a closure, `sendHeartbeat`, `send`, which calls `Logger` methods).
  sorry -- Rocq: Admitted

theorem raft.wp_stepLeader_MsgReadIndex (γ : RaftNames) (r : Loc) (rf : v3.raft.t)
    (m : v3.raftpb.Message.t) :
    {{ "Hr" ∷ r ↦ rf ∗
        "Hrf" ∷ ownRaft (GF := GF) γ rf ∗
        "%HmType" ∷ ⌜m.Type' = MsgReadIndex⌝ }}
      (App (App (Val (@! v3.stepLeader)) (Val #r)) (Val #m))
    {{ RET #(); True }} := by
  -- Unprovable as stated: `stepLeader` uses `raft` state (trk, readOnly, raftLog, ...) that only
  -- the opaque axiom `ownRaft` describes, and calls `sendMsgReadIndexResponse` and
  -- `committedEntryInCurrentTerm` (above). It also calls `r.trk.IsSingleton()`, whose (now proved)
  -- spec `ProgressTracker.wp_IsSingleton` needs the voter-map points-tos, which `ownRaft`
  -- does not provide.
  sorry -- Rocq: Admitted

set_option goose.wp.extras true in
set_option maxHeartbeats 1000000 in
theorem wp_readOnly_maybeAdvance (γ : RaftNames) (r : Loc) (term : w64)
    (c : v3.quorum.JointConfig.t) (voters_ref : Loc) (voters : GMap w64 Unit) (n : Nat) :
    0 < GMap.size cfg →
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "Hown" ∷ ownReadOnly cfg γ r term n ∗
        -- The config `c` is simple (not joint): first component is voters, second is empty.
        "%Hc" ∷ ⌜c.arr = [voters_ref, map.nil]⌝ ∗
        "voters" ∷ voters_ref ↦$ voters ∗
        "%Hvoters_cfg" ∷ ⌜domSet voters = cfg⌝ }}
      (App (Val (r @!! go.GoType.PointerType v3.readOnly @!! go!"maybeAdvance")) (Val #c))
    {{ (rs : slice.t) (reads : List Loc), RET #rs;
        ownReadOnly cfg γ r term n ∗
        voters_ref ↦$ voters ∗
        rs ↦* reads ∗
        -- Every returned read request has a valid read index witness.
        □ (∀ (i : Nat) (rp : Loc), ⌜reads[i]? = some rp⌝ →
            ∃ (read_req_ctx : GoString) (index : w64) (Φ : List (List w8) → IProp GF),
              isReadIndexRequest γ rp read_req_ctx index ∗
              isReadReqCtx γ read_req_ctx Φ ∗
              isReadIndex γ index Φ) }} := by
  intro Hsize
  wp_start as ⟨Hown, %Hc, voters, %Hvoters_cfg⟩
  iunfold ownReadOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave HAI : ownAckedIndexer (interface.mk (go.GoType.PointerType v3.readOnly) #r) acks
      iprop(r ↦ ro ∗ ro.acks' ↦$ acks) $$ [r Hacks]
  · unfold ownAckedIndexer
    isplitl [r Hacks]
    · iapply to_named; iframe
    iintro %voterID !> %Φ ⟨r, Hacks⟩ HΦ
    dsimp only [interface.mk]
    wp_method_call
    wp_call
    unfold v3.readOnly.AckedIndex.impl
    wp_auto
    wp_apply wp_map_lookup2 $$ Hacks as Hacks
    rw [show zero_val w64 = W64 0 from rfl]
    iapply HΦ
    iframe
  wp_apply JointConfig.wp_CommittedIndex cfg _ acks c voters_ref voters _ $$ [$HAI $voters]
    as %newConfirmedReads ⟨HAI, voters, %Hconfirm⟩
  · ipureintro; exact ⟨Hc, Hvoters_cfg⟩
  iunfold ownAckedIndexer at HAI
  icases HAI with ⟨⟨r, Hacks⟩, -⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ %slice.nil %([] : List Loc)
    ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    iframe Hnil voters
    isplitl
    · unfold ownReadOnly
      iexists ro, acks, unconfirmedReads, read_reqs
      iframe # ∗
      ipureintro; exact ⟨Hoption, Hcount⟩
    · imodintro
      iintro %i %rp %h
      simp at h
  obtain ⟨Hnew_nonneg, ack_q, Hack_quorum, Hq_le⟩ := Hconfirm
  -- an acked index is below the highest heartbeat index
  ihave %Hack_bounds : (⌜∀ (voter j : w64), acks !! voter = some j →
      uint.Z j ≤ uint.Z (ro.confirmedReads' + W64 unconfirmedReads.length)⌝ : IProp GF) $$ [Hhb_auth]
  · iintro %voter %j %Hin
    ihave #Hack := Hacks_wits $$ %voter %j %Hin
    iunfold isHeartbeatAck at Hack
    icases Hack with ⟨%srvs, #Hhb_ctx, -⟩
    have Hne : u64Le j ≠ [] := by
      intro h; have := u64Le_length j; rw [h] at this; simp at this
    icases ownHeartbeatAuth_agree srvs γ term (u64Le j) _ Hne $$ Hhb_ctx Hhb_auth with
      % ⟨-, Hagree⟩
    ipureintro
    rw [u64Le_to_word] at Hagree
    exact Hagree
  have Hin_bounds : uint.Z newConfirmedReads ≤
      uint.Z (ro.confirmedReads' + W64 unconfirmedReads.length) := by
    have Hq_size : 0 < GMap.size (ack_q ∩ cfg) := by unfold IsQuorum at Hack_quorum; omega
    obtain ⟨s, Hin_q⟩ := GMap.size_pos_elem_of _ Hq_size
    have Hs := Hq_le s ((GMap.elem_of_intersection _ _ _).mp Hin_q).1
    cases Hlookup : acks !! s with
    | none =>
      rw [Hlookup, Option.getD_none] at Hs
      exfalso; word
    | some j =>
      rw [Hlookup, Option.getD_some] at Hs
      have := Hack_bounds s j Hlookup
      word
  ihave %Hwf := ownSlice_wf _ _ _ $$ unconfirmedReads
  ihave %Hlen := ownSlice_len _ _ _ $$ unconfirmedReads
  have Hlen' : (unconfirmedReads.length : Int) = sint.Z ro.unconfirmedReads'.len := by
    rw [Hlen.1]; word
  have Hdiff : 0 ≤ sint.Z (newConfirmedReads - ro.confirmedReads') ∧
      sint.Z (newConfirmedReads - ro.confirmedReads') ≤ sint.Z ro.unconfirmedReads'.len := by
    constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word, by word⟩)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hdiff.1, Hdiff.2, Hwf.2⟩)]
  wp_auto
  dsimp only
  -- `k` reads are confirmed
  generalize Hk : sint.nat (newConfirmedReads - ro.confirmedReads') = k
  have Hk_le : k ≤ unconfirmedReads.length := by rw [← Hk, Hlen.1]; word
  have Hk_eq : (k : Int) = uint.Z (newConfirmedReads - ro.confirmedReads') := by rw [← Hk]; word
  ihave %Hrr_len := BigSepL2.bigSepL2_length $$ HunconfirmedReads
  icases (ownSlice_slice (newConfirmedReads - ro.confirmedReads') ro.unconfirmedReads'.len
      ro.unconfirmedReads' _ unconfirmedReads ⟨Hdiff.1, Hdiff.2, Int.le_refl _⟩).1 $$ unconfirmedReads
    with ⟨Hfront, Hback, -⟩
  rw [subslice_to_end _ _ _ (Nat.le_of_eq Hlen.1), Hk]
  ihave Hcap := (ownSliceCap_slice ro.unconfirmedReads' (newConfirmedReads - ro.confirmedReads')
      _ ⟨Hdiff.1, Hdiff.2, Hwf.2⟩).1 $$ unconfirmedReads_cap
  iapply HΦ $$ %_ %(unconfirmedReads.take k)
  iframe Hfront voters
  -- the remaining unconfirmed reads
  ihave #Hnew : (□ ([∗list] i ↦ r;x ∈ unconfirmedReads.drop k;read_reqs.drop k,
      "#readIndexRequest" ∷ isReadIndexRequest γ r x.1.1 x.1.2 ∗
      "#Hhb" ∷ isHeartbeatCtxStale γ term
        (u64Le (newConfirmedReads + W64 (i + 1 : Nat))) x.2 ∗
      "%Hstale_contains" ∷ ⌜unionList (((read_reqs.drop k).take i).map Prod.snd) ⊆ x.2⌝ ∗
      "#Hstale_or_safe" ∷ (⌜IsQuorum cfg x.2⌝ ∨
        (∃ Φ, isReadReqCtx γ x.1.1 Φ ∗ isReadIndex γ x.1.2 Φ))) : IProp GF) $$ []
  · imodintro
    ihave Hd := big_sepL2_drop _ unconfirmedReads read_reqs k $$ HunconfirmedReads
    iapply BigSepL2.bigSepL2_impl $$ Hd
    imodintro
    iintro %i %x1 %x2 %Hl1 %Hl2 ⟨#Hreq, #Hhb, %Hsc, #Hsos⟩
    rw [show ro.confirmedReads' + W64 ((k + i + 1 : Nat) : Int) =
        newConfirmedReads + W64 ((i + 1 : Nat) : Int) by
      rw [show ((k + i + 1 : Nat) : Int) = (k : Int) + ((i + 1 : Nat) : Int) by push_cast; omega,
        Hk_eq]
      word]
    iframe # ∗
    ipureintro
    rw [List.take_add, List.map_append, GMap.unionList_app] at Hsc
    rw [GMap.elem_of_subseteq] at Hsc ⊢
    intro y hy
    exact Hsc y ((GMap.elem_of_union _ _ _).mpr (Or.inr hy))
  rw [show ro.confirmedReads' + W64 (unconfirmedReads.length : Int) =
      newConfirmedReads + W64 ((unconfirmedReads.drop k).length : Int) by
    rw [List.length_drop, show ((unconfirmedReads.length - k : Nat) : Int) =
      (unconfirmedReads.length : Int) - k by omega, Hk_eq]
    word]
  isplitl
  · unfold ownReadOnly
    iexists { ro with
        unconfirmedReads' := slice.slice ro.unconfirmedReads' Loc
          (newConfirmedReads - ro.confirmedReads') ro.unconfirmedReads'.len,
        confirmedReads' := newConfirmedReads },
      acks, unconfirmedReads.drop k, read_reqs.drop k
    dsimp only
    iframe # ∗
    ipureintro; refine ⟨Hoption, ?_, Hcount.2⟩
    rw [List.length_drop, ← Hcount.1]
    have Hk' : (k : Int) = uint.Z newConfirmedReads - uint.Z ro.confirmedReads' := by
      rw [Hk_eq]; word
    have : (uint.nat newConfirmedReads : Int) = uint.Z newConfirmedReads := by word
    have : (uint.nat ro.confirmedReads' : Int) = uint.Z ro.confirmedReads' := by word
    omega
  · -- every returned read request has a valid read index witness
    imodintro
    iintro %i %rp %Hlookup
    rw [List.getElem?_take] at Hlookup
    by_cases Hik : i < k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hik)] at Hlookup
      obtain ⟨x2, Hl2⟩ : ∃ x2, read_reqs[i]? = some x2 := by
        have := (List.getElem?_eq_some_iff.mp Hlookup).1
        exact ⟨read_reqs[i]'(by omega), List.getElem?_eq_getElem _⟩
      ihave Hentry := BigSepL2.bigSepL2_lookup Hlookup Hl2 $$ HunconfirmedReads
      icases Hentry with ⟨#Hreq, #Hhb, %Hsc, (%Hstale_quorum | ⟨%Φ', #H1, #H2⟩)⟩
      rotate_left
      · iexists x2.1.1, x2.1.2, Φ'
        iframe #
      iexfalso
      obtain ⟨x, Hx_ack, Hx_stale⟩ := quorums_intersect cfg _ _ Hack_quorum Hstale_quorum
      have Hle := Hq_le x Hx_ack
      cases Hacks_lookup : acks !! x with
      | none =>
        rw [Hacks_lookup, Option.getD_none] at Hle
        exfalso; word
      | some j =>
        rw [Hacks_lookup, Option.getD_some] at Hle
        ihave #Hack := Hacks_wits $$ %x %j %Hacks_lookup
        iunfold isHeartbeatAck at Hack
        icases Hack with ⟨%srvs, #Hack, %Hnot_stale⟩
        have Hjb := Hack_bounds x j Hacks_lookup
        -- the read whose heartbeat context is `u64Le j`
        have Hm : uint.nat (j - ro.confirmedReads') - 1 < unconfirmedReads.length := by
          rw [Hlen.1]; word
        obtain ⟨ur_m, Hur⟩ : ∃ ur_m, unconfirmedReads[uint.nat (j - ro.confirmedReads') - 1]? =
            some ur_m := ⟨_, List.getElem?_eq_getElem Hm⟩
        obtain ⟨y, Hy⟩ : ∃ y, read_reqs[uint.nat (j - ro.confirmedReads') - 1]? = some y :=
          ⟨read_reqs[uint.nat (j - ro.confirmedReads') - 1]'(by omega), List.getElem?_eq_getElem _⟩
        ihave Hentry2 := BigSepL2.bigSepL2_lookup Hur Hy $$ HunconfirmedReads
        icases Hentry2 with ⟨-, #Hhb2, %Hsc2, -⟩
        iunfold isHeartbeatCtxStale at Hhb2
        icases Hhb2 with ⟨#Hhb2, -⟩
        rw [show ro.confirmedReads' +
            W64 (((uint.nat (j - ro.confirmedReads') - 1 + 1 : Nat)) : Int) = j by word]
        icases isHeartbeatCtx_agree γ term (u64Le j) srvs y.2 $$ Hack Hhb2 with %Heq
        subst Heq
        ipureintro
        apply Hnot_stale
        have Him : i ≤ uint.nat (j - ro.confirmedReads') - 1 := by
          have : (i : Int) < k := by exact_mod_cast Hik
          word
        rcases Nat.lt_or_eq_of_le Him with Him | Him
        · rw [GMap.elem_of_subseteq] at Hsc2
          apply Hsc2
          rw [GMap.elem_of_union_list]
          refine ⟨x2.2, ?_, Hx_stale⟩
          rw [List.mem_map]
          refine ⟨x2, ?_, rfl⟩
          rw [List.mem_iff_getElem?]
          exact ⟨i, by rw [List.getElem?_take, ite_eq_left_of_eq_true _ _ (eq_true Him)]; exact Hl2⟩
        · subst Him
          rw [Hl2] at Hy
          cases Hy
          exact Hx_stale
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hik)] at Hlookup
      cases Hlookup

set_option goose.wp.extras true in
set_option maxHeartbeats 1000000 in
theorem wp_readOnly_addRequest (γ : RaftNames) (r : Loc) (term commitIndex : w64)
    (req : v3.raftpb.Message.t) (read_req_ctx : GoString) (log : List (List w8)) (dq : DFrac)
    (Ψ : List (List w8) → IProp GF) (n : Nat) :
    {{ isPkgInit (PROP := IProp GF) raft ∗
        "#Hinv" ∷ isRaftCommitInv γ ∗
        "Hown" ∷ ownReadOnly cfg γ r term n ∗
        "Hcom" ∷ ownCommittedInTerm γ term log ∗
        "%HcommitIndex" ∷ ⌜uint.nat commitIndex = log.length⌝ ∗
        -- Lean deviation (Rocq: no such precondition; see `ownReadOnly`)
        "%Hn" ∷ ⌜n < 2 ^ 64 - 1⌝ ∗
        "Hctx" ∷ req.Context' ↦*{dq} read_req_ctx ∗
        "#Hread_ctx" ∷ isReadReqCtx γ read_req_ctx Ψ }}
      (App (App (Val (r @!! go.GoType.PointerType v3.readOnly @!! go!"addRequest"))
        (Val #commitIndex)) (Val #req))
    {{ RET #(); ownReadOnly cfg γ r term (n + 1) }} := by
  wp_start as ⟨#Hinv, Hown, Hcom, %HcommitIndex, %Hn, Hctx, #Hread_ctx⟩
  iunfold ownReadOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  irename «$sl0» => Hreq
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType v3.readIndexRequest) [«$sl0_ptr»]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_apply +noauto wp_slice_append (V := Loc) (t := go.GoType.PointerType v3.readIndexRequest)
    ro.unconfirmedReads' unconfirmedReads _ [«$sl0_ptr»] (DFrac.own 1)
    $$ [unconfirmedReads unconfirmedReads_cap Hsl]
  · iframe
  iintro %s' ⟨Hs', Hcap', -⟩
  iapply wp_fupd
  wp_auto_lc 1
  ihave #Hrc := Hread_ctx
  iunfold isReadReqCtx at Hrc
  icases Hrc with ⟨%γreq, -, -, #Hau⟩
  imod try_read cfg γ term log Ψ $$ [Hlc1 Hcom] with ⟨%stale_ids', #Hstale, Hcom, #Hmaybe_read⟩
  · iframe # ∗
    ipureintro
    rw [← HcommitIndex]; word
  ihave %Hrr_len := BigSepL2.bigSepL2_length $$ HunconfirmedReads
  imod ownHeartbeatAuth_new
      (unionList (read_reqs.map Prod.snd ++ [stale_ids'])) γ term _
      -- (Rocq: admitted overflow side condition; here from `Hcount` and `Hn`)
      (by have := Hcount.1; word)
      $$ Hhb_auth with ⟨Hhb_auth, #Hhb⟩
  ipersist Hreq
  ipersist Hctx
  -- witnesses for the servers in the new stale set
  ihave #Hstale'' : (□ (∀ id, ⌜id ∈ unionList (read_reqs.map Prod.snd ++ [stale_ids'])⌝ →
      ∃ term', isTermLb γ id term' ∗ ⌜sint.nat term < sint.nat term'⌝) : IProp GF) $$ []
  · imodintro
    iintro %id %Hin
    rw [GMap.unionList_app, GMap.elem_of_union] at Hin
    rcases Hin with Hin | Hin
    · -- `id` is in the stale set of an earlier read; the last one contains them all
      rcases List.eq_nil_or_concat read_reqs with Hnil | ⟨rr', y, Hrr⟩
      · subst Hnil; simp [unionList] at Hin
        exact absurd Hin (GMap.not_elem_of_empty _)
      subst Hrr
      simp only [List.concat_eq_append] at *
      have Hlt : rr'.length < unconfirmedReads.length := by simp at Hrr_len; omega
      obtain ⟨ur_l, Hur⟩ : ∃ x, unconfirmedReads[rr'.length]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      ihave Hentry := BigSepL2.bigSepL2_lookup (i := rr'.length) (x2 := y) Hur (by simp) $$ HunconfirmedReads
      icases Hentry with ⟨-, #Hhb', %Hsc, -⟩
      iunfold isHeartbeatCtxStale at Hhb'
      icases Hhb' with ⟨-, #Hw⟩
      iapply Hw $$ %id
      ipureintro
      rw [show (rr' ++ [y]).take rr'.length = rr' by simp] at Hsc
      simp only [List.map_append, List.map_cons, List.map_nil] at Hin
      rw [GMap.unionList_app, GMap.elem_of_union] at Hin
      rcases Hin with Hin | Hin
      · rw [GMap.elem_of_subseteq] at Hsc; exact Hsc id Hin
      · simp [unionList, GMap.elem_of_union] at Hin
        rcases Hin with Hin | Hin
        · exact Hin
        · exact absurd Hin (GMap.not_elem_of_empty _)
    · iapply Hstale $$ %id
      ipureintro
      simp [unionList, GMap.elem_of_union] at Hin
      rcases Hin with Hin | Hin
      · exact Hin
      · exact absurd Hin (GMap.not_elem_of_empty _)
  -- the reads queue with the new request
  ihave #Hnew : (□ ([∗list] i ↦ r;x ∈ unconfirmedReads ++ [«$sl0_ptr»];
      read_reqs ++ [((read_req_ctx, commitIndex), unionList (read_reqs.map Prod.snd ++ [stale_ids']))],
      "#readIndexRequest" ∷ isReadIndexRequest γ r x.1.1 x.1.2 ∗
      "#Hhb" ∷ isHeartbeatCtxStale γ term (u64Le (ro.confirmedReads' + W64 (i + 1 : Nat))) x.2 ∗
      "%Hstale_contains" ∷ ⌜unionList (((read_reqs ++
          [((read_req_ctx, commitIndex), unionList (read_reqs.map Prod.snd ++ [stale_ids']))]).take i).map
          Prod.snd) ⊆ x.2⌝ ∗
      "#Hstale_or_safe" ∷ (⌜IsQuorum cfg x.2⌝ ∨
        (∃ Φ, isReadReqCtx γ x.1.1 Φ ∗ isReadIndex γ x.1.2 Φ))) : IProp GF) $$ []
  · imodintro
    iapply (BigSepL2.bigSepL2_snoc).2
    isplitl
    · iapply BigSepL2.bigSepL2_impl $$ HunconfirmedReads
      imodintro
      iintro %i %x1 %x2 %Hl1 %Hl2 ⟨#Hreq', #Hhb', %Hsc, #Hsos⟩
      iframe # ∗
      ipureintro
      rw [List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.mp Hl2).1)]
      exact Hsc
    · rw [show ro.confirmedReads' + W64 ((unconfirmedReads.length + 1 : Nat) : Int) =
          ro.confirmedReads' + W64 (unconfirmedReads.length : Int) + W64 1 by word]
      dsimp only
      isplitr
      · unfold isReadIndexRequest
        iexists { req' := req, index' := commitIndex }
        iframe # ∗
        isplitr
        · ipureintro; rfl
        iexists Ψ
        iexact Hread_ctx
      isplitr
      · unfold isHeartbeatCtxStale
        iapply to_named
        iframe #
      isplitr
      · ipureintro
        rw [Hrr_len, List.take_left, GMap.unionList_app, GMap.elem_of_subseteq]
        intro x hx
        exact (GMap.elem_of_union _ _ _).mpr (Or.inl hx)
      icases Hmaybe_read with (#Hread | %Hq)
      · iright
        iexists Ψ
        iframe #
        rw [show W64 (log.length : Int) = commitIndex by rw [← HcommitIndex]; word]
        iexact Hread
      · ileft
        ipureintro
        refine quorums_subseteq cfg _ _ ?_ Hq
        rw [GMap.unionList_app, GMap.elem_of_subseteq]
        intro x hx
        refine (GMap.elem_of_union _ _ _).mpr (Or.inr ?_)
        simp [unionList, GMap.elem_of_union, hx]
  rw [show ro.confirmedReads' + W64 (unconfirmedReads.length : Int) + W64 1 =
      ro.confirmedReads' + W64 ((unconfirmedReads ++ [«$sl0_ptr»]).length : Int) by
    simp only [List.length_append, List.length_singleton]; word]
  imodintro
  iapply HΦ
  unfold ownReadOnly
  iexists { ro with unconfirmedReads' := s' }, acks, unconfirmedReads ++ [«$sl0_ptr»],
    read_reqs ++ [((read_req_ctx, commitIndex), unionList (read_reqs.map Prod.snd ++ [stale_ids']))]
  dsimp only
  iframe # ∗
  ipureintro; refine ⟨Hoption, ?_, by omega⟩
  simp only [List.length_append, List.length_singleton]
  omega

end wps2

end proof

end go_etcd_io.raft.v3_proof.readonly

end Perennial
