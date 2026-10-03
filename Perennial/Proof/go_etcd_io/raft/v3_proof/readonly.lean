/-
Port of `new/proof/go_etcd_io/raft/v3_proof/readonly.v`: the ReadIndex
(linearizable read) protocol of raft, its ghost state, and specs for the
`readOnly` methods.

See the Rocq file for the discussion of the protocol (and of the bug in the raft
library: https://github.com/etcd-io/etcd/issues/20418#issuecomment-3974901065,
https://github.com/etcd-io/raft/issues/392).

Lean notes:
* Everything lives in `namespace go_etcd_io.raft.v3_proof.readonly`: Rocq's
  `readonly.v` defines its own `raft_names` record, shadowing the axiomatized
  `raft_names` of `protocol.v`.
* Rocq's `Context (cfg : gset w64)` is an explicit section variable `cfg`.
* `own_term`/`is_term_lb`: Rocq owns `{[node_id := ●MN n]}` in a
  `gmap w64 mono_natR` camera. `allG` has no `gmap` CMRA code (only `gmapUR`
  as a unital camera, and `gmap_viewR`), so here the per-node ghost name is
  found through a persistent ghost map: `node_id ↪[term_gn]□ γn ∗
  mono_nat_auth_own γn 1 n` (resp. `mono_nat_lb_own γn n`). Neither is used
  in any lemma of this file except as an opaque persistent witness.
* Deviations from Rocq (statements/definitions):
  - `own_readOnly` takes the number `n` of read requests added so far, with
    `"%Hcount"`; `wp_readOnly_recvAck` and `wp_readOnly_maybeAdvance` keep `n`,
    `wp_readOnly_addRequest` requires `n < 2^64 - 1` and returns `n + 1`. This
    makes the overflow side condition admitted in Rocq provable.
  - `wp_ProgressTracker__IsSingleton`: Rocq's (trusted) statement
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
open scoped gmap

namespace go_etcd_io.raft.v3_proof.readonly

/-- Rocq `raft_names`. -/
structure raft_names where
  mk ::
  commited_gn : GName
  term_gn : GName
  config_gn : GName
  reads_gn : GName
  read_req_gn : GName
  heartbeat_gn : GName

section proof
variable (cfg : gset w64)

section global_proof
variable {GF : BundledGFunctors} [InvGS GF] [allG GF]

/-- Rocq `N`. -/
def N : Namespace := nroot

/-! ### Ghost state for the raft protocol -/

abbrev own_commit_auth (γ : raft_names) (log : List (List w8)) : IProp GF :=
  mono_list_auth_own γ.commited_gn (1 : Qp).half log
abbrev own_commit (γ : raft_names) (log : List (List w8)) : IProp GF :=
  mono_list_auth_own γ.commited_gn (1 : Qp).half log
abbrev is_commit (γ : raft_names) (log : List (List w8)) : IProp GF :=
  mono_list_lb_own γ.commited_gn log

instance is_commit_pers (γ : raft_names) (log : List (List w8)) :
    Persistent (is_commit (GF := GF) γ log) := by
  unfold is_commit; infer_instance

/-- Rocq `own_term` (see the file header for the encoding). -/
def own_term (γ : raft_names) (node_id term : w64) : IProp GF :=
  iprop(∃ γn : GName, node_id ↪[γ.term_gn]□ γn ∗ mono_nat_auth_own γn 1 (sint.nat term))
/-- Rocq `is_term_lb` (see the file header for the encoding). -/
def is_term_lb (γ : raft_names) (node_id term : w64) : IProp GF :=
  iprop(∃ γn : GName, node_id ↪[γ.term_gn]□ γn ∗ mono_nat_lb_own γn (sint.nat term))

instance is_term_lb_pers (γ : raft_names) (node_id term : w64) :
    Persistent (is_term_lb (GF := GF) γ node_id term) := by
  unfold is_term_lb; infer_instance

def own_unused_heartbeat_ctx (γ : raft_names) (term : w64) (ctx : go_string) : IProp GF :=
  iprop(∃ (per_term_gn ctx_gn : GName),
    term ↪[γ.heartbeat_gn]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghost_var ctx_gn (DFrac.own 1) (∅ : gset w64))

def is_heartbeat_ctx (γ : raft_names) (term : w64) (ctx : go_string) (srvs : gset w64) :
    IProp GF :=
  iprop(∃ (per_term_gn ctx_gn : GName),
    term ↪[γ.heartbeat_gn]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghost_var ctx_gn DFrac.discard srvs)

instance is_heartbeat_ctx_pers (γ : raft_names) (term : w64) (ctx : go_string)
    (srvs : gset w64) : Persistent (is_heartbeat_ctx (GF := GF) γ term ctx srvs) := by
  unfold is_heartbeat_ctx; infer_instance

theorem is_heartbeat_ctx_agree (γ : raft_names) (term : w64) (ctx : go_string)
    (srvs1 srvs2 : gset w64) :
    ⊢ is_heartbeat_ctx (GF := GF) γ term ctx srvs1 -∗
      is_heartbeat_ctx γ term ctx srvs2 -∗
      ⌜srvs1 = srvs2⌝ := by
  unfold is_heartbeat_ctx
  iintro ⟨%gn1, %cgn1, #Ht1, #Hc1, #Hv1⟩ ⟨%gn2, %cgn2, #Ht2, #Hc2, #Hv2⟩
  icases ghost_map_elem_agree term γ.heartbeat_gn _ _ gn1 gn2 $$ Ht1 Ht2 with %Heq1
  subst Heq1
  icases ghost_map_elem_agree ctx gn1 _ _ cgn1 cgn2 $$ Hc1 Hc2 with %Heq2
  subst Heq2
  icases dghost_var_agree cgn1 srvs1 _ srvs2 _ $$ Hv1 Hv2 with %Heq3
  ipureintro
  exact Heq3

/-! ### Propositions defined in terms of the primitive ghost state.

This proof assumes there's only one configuration (for now). -/

/-- Rocq `Axiom own_committed_in_term`. -/
axiom own_committed_in_term {GF : BundledGFunctors} (γ : raft_names) (term : w64)
  (log : List (List w8)) : IProp GF
/-- Rocq `Axiom is_committed_in_term`. -/
axiom is_committed_in_term {GF : BundledGFunctors} (γ : raft_names) (term : w64)
  (log : List (List w8)) : IProp GF
/-- Rocq `Axiom is_committed_in_term_pers`. -/
axiom is_committed_in_term_pers {GF : BundledGFunctors} (γ : raft_names) (term : w64)
  (log : List (List w8)) : Persistent (is_committed_in_term (GF := GF) γ term log)
attribute [instance] is_committed_in_term_pers

/-- Rocq `is_quorum`. -/
def is_quorum (quorum : gset w64) : Prop :=
  gmap.size cfg < 2 * gmap.size (quorum ∩ cfg)

theorem quorums_intersect (q1 q2 : gset w64) :
    is_quorum cfg q1 → is_quorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 := by
  intro Hsize1 Hsize2
  by_cases Hempty : q1 ∩ q2 = ∅
  · exfalso
    have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg := by
      rw [gmap.elem_of_subseteq]; set_solver
    have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) := by
      rw [gmap.elem_of_disjoint]
      intro x h1 h2
      rw [gmap.elem_of_intersection] at h1 h2
      have : x ∈ q1 ∩ q2 := (gmap.elem_of_intersection _ _ _).mpr ⟨h1.1, h2.1⟩
      rw [Hempty] at this
      exact gmap.not_elem_of_empty _ this
    have Hle := gmap.subseteq_size Hunion
    rw [gmap.size_union Hdisj] at Hle
    unfold is_quorum at *
    omega
  · obtain ⟨x, Hx⟩ := gmap.set_choose_L _ Hempty
    exact ⟨x, by set_solver, by set_solver⟩

theorem quorums_subseteq (q1 q2 : gset w64) :
    q1 ⊆ q2 → is_quorum cfg q1 → is_quorum cfg q2 := by
  intro Hsub Hsize
  unfold is_quorum at *
  have Hs : q1 ∩ cfg ⊆ q2 ∩ cfg := by
    rw [gmap.elem_of_subseteq] at *; set_solver
  have := gmap.subseteq_size Hs
  omega

/-- Rocq `is_stale_term`. -/
def is_stale_term (γ : raft_names) (term : w64) : IProp GF :=
  iprop(∃ quorum : gset w64,
    "%Hquorum" ∷ ⌜is_quorum cfg quorum⌝ ∗
    "#Hterm_lbs" ∷
      □ (∀ id, ⌜id ∈ quorum⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜sint.nat term < sint.nat term'⌝))

instance is_stale_term_pers (γ : raft_names) (term : w64) :
    Persistent (is_stale_term (GF := GF) cfg γ term) := by
  unfold is_stale_term; infer_instance

/-- Rocq `Axiom committed_in_term_agree`. -/
axiom committed_in_term_agree {GF : BundledGFunctors} (γ : raft_names) (term : w64)
    (log1 log2 : List (List w8)) :
  ⊢ own_committed_in_term (GF := GF) γ term log1 -∗
    is_committed_in_term γ term log2 -∗
    ⌜log2 <+: log1⌝

/-- Rocq `Axiom committed_in_term_stale`: when own and is have different terms,
the own term is stale. -/
axiom committed_in_term_stale (cfg : gset w64) {GF : BundledGFunctors} [allG GF]
    (γ : raft_names) (term1 term2 : w64) (log1 log2 : List (List w8)) :
  term1 ≠ term2 →
  ⊢ own_committed_in_term (GF := GF) γ term1 log1 -∗
    is_committed_in_term γ term2 log2 -∗
    is_stale_term cfg γ term1

/-! TODO (Rocq): set this up to confirm backwards compatibility (i.e. if some raft
servers run the new code and some run the old code, system is still safe; only
the leader needs to run the new code in order for the system to tolerate
duplicate ReadIndex requests). -/

/-- Rocq `own_reads`: ownership of the reads queue, an authoritative monotone
list of `(start_index, saved_pred_gname)` pairs. The gnames are hidden
internally; the caller sees only `readsΦ`. -/
def own_reads (γ : raft_names) (readsΦ : List (w64 × (List (List w8) → IProp GF))) : IProp GF :=
  iprop(∃ l : List (w64 × GName),
    ⌜l.map Prod.fst = readsΦ.map Prod.fst⌝ ∗
    mono_list_auth_own γ.reads_gn 1 l ∗
    ∀ (i : Nat) (si : w64) (Φ : List (List w8) → IProp GF) (gn : GName),
      ⌜readsΦ[i]? = some (si, Φ)⌝ →
      ⌜l[i]? = some (si, gn)⌝ →
      saved_pred_own gn DFrac.discard Φ)

/-- Rocq `is_in_reads`: persistent witness that `(start_index, Φ)` is tracked in
the reads queue. -/
def is_in_reads (γ : raft_names) (si : w64) (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(∃ (i : Nat) (gn : GName),
    mono_list_idx_own γ.reads_gn i (si, gn) ∗
    saved_pred_own gn DFrac.discard Φ)

instance is_in_reads_persistent (γ : raft_names) (si : w64) (Φ : List (List w8) → IProp GF) :
    Persistent (is_in_reads γ si Φ) := by
  unfold is_in_reads; infer_instance

/-- Insert a new read entry at the end of the list, obtaining a persistent witness. -/
theorem reads_insert (γ : raft_names) (readsΦ : List (w64 × (List (List w8) → IProp GF)))
    (si : w64) (Φ : List (List w8) → IProp GF) :
    ⊢ own_reads γ readsΦ ==∗
      own_reads γ (readsΦ ++ [(si, Φ)]) ∗ is_in_reads γ si Φ := by
  unfold own_reads is_in_reads
  iintro ⟨%l, %Hfst, Hauth, #Hfor⟩
  imod saved_pred_alloc Φ DFrac.discard DFrac.valid_discard with ⟨%gn, #Hgn⟩
  imod mono_list_auth_own_update_app [(si, gn)] $$ Hauth with ⟨Hauth, #Hlb⟩
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
    · iapply mono_list_idx_own_get l.length (si, gn) ?_ $$ Hlb
      simp
    · iexact Hgn

/-- Agreement: the witness corresponds to an entry in `readsΦ` with a
propositionally equal predicate (up to `▷`). -/
theorem reads_agree (γ : raft_names) (readsΦ : List (w64 × (List (List w8) → IProp GF)))
    (si : w64) (Φ : List (List w8) → IProp GF) (x : List (List w8)) :
    ⊢ own_reads γ readsΦ -∗
      is_in_reads γ si Φ -∗
      ∃ (i : Nat) (Ψ : List (List w8) → IProp GF),
        ⌜readsΦ[i]? = some (si, Ψ)⌝ ∗
        ▷ (Φ x ≡ Ψ x) := by
  unfold own_reads is_in_reads
  iintro ⟨%l, %Hfst, Hauth, #Hfor⟩ ⟨%i, %gn, #Hidx, #Hgn⟩
  icases mono_list_auth_idx_lookup γ.reads_gn 1 l i (si, gn) $$ Hauth Hidx with %Hl
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

/-- Rocq `is_raft_commit_inv`. `Hread_aus`: permission to linearize reads on all
future logs (for any `Φ` stored in the reads queue, firing its AU against the
current committed log produces `Φ` applied to that log). `Hread_wits`:
witnesses that reads were linearized on every index starting at their
respective starting index. -/
def is_raft_commit_inv (γ : raft_names) : IProp GF :=
  inv Ncommit iprop(∃ (term : w64) (log : List (List w8))
      (readsΦ : List (w64 × (List (List w8) → IProp GF))),
    "commit" ∷ own_commit_auth γ log ∗
    "#Hcommit" ∷ is_committed_in_term γ term log ∗
    "reads" ∷ own_reads γ readsΦ ∗
    "#Hread_aus" ∷ □ (∀ (Φ : List (List w8) → IProp GF), ⌜Φ ∈ readsΦ.map Prod.snd⌝ →
        ∀ log : List (List w8),
          own_commit_auth γ log ={⊤ \ ↑N}=∗ own_commit_auth γ log ∗ Φ log) ∗
    "#Hread_wits" ∷ □ (∀ (start_index : w64) (Φ : List (List w8) → IProp GF),
        ⌜(start_index, Φ) ∈ readsΦ⌝ → ∀ index : w64,
          ⌜uint.nat start_index ≤ uint.nat index ∧ uint.nat index ≤ log.length⌝ →
          Φ (log.take (uint.nat index))))

instance is_raft_commit_inv_pers (γ : raft_names) :
    Persistent (is_raft_commit_inv (GF := GF) γ) := by
  unfold is_raft_commit_inv; infer_instance

/-- Rocq `is_read_index`: a read index witness. Given any committed log at least
as long as `index`, opening the invariant at mask `⊤` lets us fire the stored
AU to get `Φ log`. Needs `£ 2`: one credit to open the invariant (strip `▷`),
one to strip the `▷` from `saved_pred_agree`. -/
def is_read_index (γ : raft_names) (index : w64) (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(□ (∀ log : List (List w8), ⌜uint.nat index ≤ log.length⌝ → ⌜log.length < 2 ^ 64⌝ →
       £ 2 -∗ is_commit γ log ={⊤}=∗ Φ log))

instance is_read_index_pers (γ : raft_names) (index : w64) (Φ : List (List w8) → IProp GF) :
    Persistent (is_read_index γ index Φ) := by
  unfold is_read_index; infer_instance

theorem is_in_reads_to_valid (γ : raft_names) (i j : w64) (Φ : List (List w8) → IProp GF) :
    "#Hinv" ∷ is_raft_commit_inv γ ∗
    "#Hr" ∷ is_in_reads γ j Φ ∗
    "%Hj" ∷ ⌜uint.nat j ≤ uint.nat i⌝ ⊢
    is_read_index γ i Φ := by
  iintro ⟨#Hinv, #Hr, %Hj⟩
  unfold is_read_index
  imodintro
  iintro %log_wit %Hlog_wit %Hoverflow ⟨Hlc, Hlc2⟩ #Hlog_wit
  unfold is_raft_commit_inv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icases mono_list_auth_lb_valid γ.commited_gn _ log log_wit $$ commit Hlog_wit with % ⟨-, Hle⟩
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
theorem try_read (γ : raft_names) (term : w64) (log : List (List w8))
    (Φ : List (List w8) → IProp GF) :
    "Hlc" ∷ £ 1 ∗
    "%Hno_overflow" ∷ ⌜log.length < 2 ^ 64⌝ ∗
    "#Hinv" ∷ is_raft_commit_inv γ ∗
    "Hcom" ∷ own_committed_in_term γ term log ∗
    "#Hau" ∷ □ (|={⊤ \ ↑N, ∅}=> ∃ log, own_commit γ log ∗
      (own_commit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)) ⊢
    |={⊤}=> ∃ stale_ids : gset w64,
      □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', is_term_lb γ id term' ∗
          ⌜sint.nat term < sint.nat term'⌝) ∗
      own_committed_in_term γ term log ∗
      (is_read_index γ (W64 log.length) Φ ∨ ⌜is_quorum cfg stale_ids⌝) := by
  iintro ⟨Hlc, %Hno_overflow, #Hinv, Hcom, #Hau⟩
  ihave #Hinv2 := Hinv
  iunfold is_raft_commit_inv at Hinv2
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
          own_commit_auth γ log0 ={⊤ \ ↑N}=∗ own_commit_auth γ log0 ∗ Φ0 log0) : IProp GF) $$ []
    · imodintro
      iintro %Φ0 %Hin %log0 Hca
      rw [List.map_append, List.mem_append] at Hin
      rcases Hin with Hin | Hin
      · iapply Hread_aus $$ %Φ0 %Hin %log0 Hca
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at Hin
        subst Hin
        imod Hau with ⟨%log_au, Hcommit, Hclose'⟩
        icases mono_list_auth_own_agree γ.commited_gn _ _ log0 log_au $$ Hca Hcommit with
          % ⟨-, Heq⟩
        subst Heq
        imod Hclose' $$ Hcommit with #HΦ
        imodintro
        iframe # ∗
    -- Close the invariant with the extended reads list.
    imod (fupd_mask_subseteq (PROP := IProp GF) mask_diff_Ncommit) with Hmask
    imod Hau with ⟨%log', Hcom', Hclose'⟩
    icases mono_list_auth_own_agree γ.commited_gn _ _ log' inv_log $$ Hcom' Hcommit_auth with
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
      exact absurd Hid (gmap.not_elem_of_empty _)
    iframe Hcom
    ileft
    iapply is_in_reads_to_valid γ (W64 log.length) (W64 log'.length) Φ
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
    iunfold is_stale_term at Hstale
    icases Hstale with ⟨%quorum, %Hquorum, #Hterm_lbs⟩
    iexists quorum
    iframe # ∗
    iright
    ipureintro
    exact Hquorum

/-- Rocq `is_heartbeat_ctx_stale`. -/
def is_heartbeat_ctx_stale (γ : raft_names) (term : w64) (ctx : go_string)
    (stale_ids : gset w64) : IProp GF :=
  iprop(is_heartbeat_ctx γ term ctx stale_ids ∗
    □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', is_term_lb γ id term' ∗
        ⌜sint.nat term < sint.nat term'⌝))

instance is_heartbeat_ctx_stale_pers (γ : raft_names) (term : w64) (ctx : go_string)
    (stale_ids : gset w64) : Persistent (is_heartbeat_ctx_stale (GF := GF) γ term ctx stale_ids) := by
  unfold is_heartbeat_ctx_stale; infer_instance

/-- Rocq `is_HeartbeatRequest`. -/
def is_HeartbeatRequest (γ : raft_names) (term : w64) (ctx : List w8) : IProp GF :=
  iprop(∃ stale_ids, is_heartbeat_ctx_stale γ term ctx stale_ids)

/-- Rocq `is_HeartbeatResp`: confirms that `from` was not stale back when `ctx`
was first used in `term`. -/
def is_HeartbeatResp (γ : raft_names) («from» : w64) (term : w64) (ctx : List w8) : IProp GF :=
  iprop(∃ srvs, is_heartbeat_ctx γ term ctx srvs ∗ ⌜«from» ∉ srvs⌝)

/-- Rocq `is_heartbeat_ack`: witnesses that `from` acknowledged heartbeat
context `ctx` in `term`, confirming `from` was not stale at that point. Similar
to `is_HeartbeatResp` but used as a precondition for `recvAck`. -/
def is_heartbeat_ack (γ : raft_names) («from» : w64) (term : w64) (ctx : go_string) : IProp GF :=
  iprop(∃ srvs, is_heartbeat_ctx γ term ctx srvs ∗ ⌜«from» ∉ srvs⌝)

instance is_heartbeat_ack_pers (γ : raft_names) («from» : w64) (term : w64) (ctx : go_string) :
    Persistent (is_heartbeat_ack (GF := GF) γ «from» term ctx) := by
  unfold is_heartbeat_ack; infer_instance

theorem heartbeat_ack_not_stale (γ : raft_names) («from» : w64) (term : w64) (ctx : go_string)
    (stale_ids : gset w64) :
    ⊢ is_heartbeat_ctx (GF := GF) γ term ctx stale_ids -∗
      is_heartbeat_ack γ «from» term ctx -∗
      ⌜«from» ∉ stale_ids⌝ := by
  iintro #Hctx #Hack
  unfold is_heartbeat_ack
  icases Hack with ⟨%srvs, #Hctx', %Hnot_in⟩
  icases is_heartbeat_ctx_agree γ term ctx stale_ids srvs $$ Hctx Hctx' with %Heq
  subst Heq
  ipureintro
  exact Hnot_in

theorem start_heartbeat (stale_ids : gset w64) (γ : raft_names) (term : w64) (ctx : go_string) :
    ⊢ □ (∀ id, ⌜id ∈ stale_ids⌝ → ∃ term', is_term_lb (GF := GF) γ id term' ∗
          ⌜sint.nat term < sint.nat term'⌝) -∗
      own_unused_heartbeat_ctx γ term ctx ==∗
      is_heartbeat_ctx_stale γ term ctx stale_ids := by
  iintro #Hstale Hunused
  unfold own_unused_heartbeat_ctx
  icases Hunused with ⟨%per_term_gn, %ctx_gn, #Hterm, #Hctx, Hvar⟩
  imod dghost_var_update stale_ids ctx_gn _ $$ Hvar with Hvar
  imod dghost_var_persist ctx_gn 1 stale_ids $$ Hvar with #Hvar
  imodintro
  unfold is_heartbeat_ctx_stale is_heartbeat_ctx
  isplitl
  · iexists per_term_gn, ctx_gn
    iframe # ∗
  · iexact Hstale

/-- Rocq `own_read_req_ctx`. -/
def own_read_req_ctx (γ : raft_names) (read_req_ctx : go_string) : IProp GF :=
  iprop(∃ γreq : GName,
    "#Hγreq" ∷ read_req_ctx ↪[γ.read_req_gn]□ γreq ∗
    "Hreq" ∷ saved_pred_own γreq (DFrac.own 1) (fun (_ : List (List w8)) => iprop(True)))

/-- Rocq `is_read_req_ctx`. -/
def is_read_req_ctx (γ : raft_names) (read_req_ctx : go_string)
    (Φ : List (List w8) → IProp GF) : IProp GF :=
  iprop(∃ γreq : GName,
    "#Hγreq" ∷ read_req_ctx ↪[γ.read_req_gn]□ γreq ∗
    "#Hreq" ∷ saved_pred_own γreq DFrac.discard Φ ∗
    "#Hau" ∷ □ (|={⊤ \ ↑N, ∅}=> ∃ log, own_commit γ log ∗
      (own_commit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)))

instance is_read_req_ctx_pers (γ : raft_names) (read_req_ctx : go_string)
    (Φ : List (List w8) → IProp GF) : Persistent (is_read_req_ctx γ read_req_ctx Φ) := by
  unfold is_read_req_ctx; infer_instance

theorem start_req_ctx (Φ : List (List w8) → IProp GF) (req_ctx : go_string) (index : w64)
    (γ : raft_names) :
    own_read_req_ctx γ req_ctx ∗
    □ (|={⊤ \ ↑N, ∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅, ⊤ \ ↑N}=∗ □ Φ log)) ⊢
    |={⊤}=> is_read_req_ctx γ req_ctx Φ := by
  iintro ⟨Hown, #Hau⟩
  iNamed Hown
  imod saved_pred_update Φ γreq _ $$ Hreq with Hreq
  imod saved_pred_persist γreq _ Φ $$ Hreq with #Hreq
  imodintro
  unfold is_read_req_ctx
  iexists γreq
  iframe # ∗

/-- Rocq `is_MsgReadIndex`. -/
def is_MsgReadIndex (γ : raft_names) (read_req_ctx : go_string) : IProp GF :=
  iprop(∃ Φ, is_read_req_ctx γ read_req_ctx Φ)

/-- Rocq `is_MsgReadIndexResp`. -/
def is_MsgReadIndexResp (γ : raft_names) (read_req_ctx : go_string) (index : w64) : IProp GF :=
  iprop(∃ Φ, is_read_req_ctx γ read_req_ctx Φ ∗ is_read_index γ index Φ)

/-- If a quorum of servers acked a heartbeat context, and the stale set for that
context were also a quorum, they would intersect — but each acking server is
provably NOT in the stale set. Contradiction. -/
theorem heartbeat_ack_quorum_not_stale (γ : raft_names) (term : w64) (ctx : go_string)
    (stale_ids ack_srvs : gset w64) :
    is_quorum cfg ack_srvs →
    is_quorum cfg stale_ids →
    ⊢ is_heartbeat_ctx (GF := GF) γ term ctx stale_ids -∗
      □ (∀ id, ⌜id ∈ ack_srvs⌝ → is_heartbeat_ack γ id term ctx) -∗
      False := by
  intro Hack_quorum Hstale_quorum
  iintro #Hctx #Hacks
  obtain ⟨x, Hx_ack, Hx_stale⟩ := quorums_intersect cfg _ _ Hack_quorum Hstale_quorum
  ihave #Hack_x := Hacks $$ %x %Hx_ack
  icases heartbeat_ack_not_stale γ x term ctx stale_ids $$ Hctx Hack_x with %Hnot
  exact absurd Hx_stale Hnot

end global_proof

/-- Rocq `Axiom own_raft`. -/
axiom own_raft [ffi_syntax] {GF : BundledGFunctors} (γ : raft_names) (rf : v3.raft.t) : IProp GF

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- Lean addition: `array_acc`, putting back the same element. -/
theorem array_acc_same {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : loc) (i : Int)
    (dq : DFrac) (n : Int) (a : array.t V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typed_pointsto (GF := GF) p a dq ⊢
      iprop(typed_pointsto (array_index_ref V i p) v dq ∗
        (typed_pointsto (array_index_ref V i p) v dq -∗ typed_pointsto p a dq)) := by
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
theorem wp_ProgressTracker__IsSingleton (p : loc) (dq : DFrac) (pt : v3.tracker.ProgressTracker.t)
    (v0 v1 : loc) (m0 m1 : gmap w64 Unit) (dq0 dq1 : DFrac) :
    {{ "Hp" ∷ p ↦{dq} pt ∗
        "%Hvoters" ∷ ⌜pt.Config'.Voters'.arr = [v0, v1]⌝ ∗
        "Hm0" ∷ (v0 ↦${dq0} m0 : IProp GF) ∗
        "Hm1" ∷ (v1 ↦${dq1} m1 : IProp GF) }}
      (App (Val (p @!! go.type.PointerType v3.tracker.ProgressTracker @!! go!"IsSingleton"))
        (Val #()))
    {{ RET #(decide (W64 (gmap.size m0) = W64 1 ∧ W64 (gmap.size m1) = W64 0));
        p ↦{dq} pt ∗ v0 ↦${dq0} m0 ∗ v1 ↦${dq1} m1 }} := by
  wp_start as ⟨Hp, %Hvoters, Hm0, Hm1⟩
  icases typed_pointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases typed_pointsto_not_null_dup _ _ _ $$ Config with ⟨Config, %HnnC⟩
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
    iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def, named]
    iframe Progress Votes MaxInflight MaxInflightBytes
    iapply typed_pointsto_combine _ _ _ HnnC
    simp only [TypedPointsto.typed_pointsto_def, named]
    iframe
  · rw [show decide (W64 ↑m0.size = W64 1 ∧ W64 ↑m1.size = W64 0) = false from
      decide_eq_false (fun h => Hif h.1)]
    iapply HΦ
    iframe Hm0 Hm1
    iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def, named]
    iframe Progress Votes MaxInflight MaxInflightBytes
    iapply typed_pointsto_combine _ _ _ HnnC
    simp only [TypedPointsto.typed_pointsto_def, named]
    iframe

theorem wp_raft__committedEntryInCurrentTerm (r : loc) (rf : v3.raft.t) (γ : raft_names) :
    {{ r ↦ rf ∗ own_raft (GF := GF) γ rf }}
      (App (Val (r @!! go.type.PointerType v3.raft @!! go!"committedEntryInCurrentTerm"))
        (Val #()))
    {{ (c : Bool), RET #c; r ↦ rf ∗ own_raft γ rf ∗
        if c then ∃ l, is_committed_in_term γ rf.Term' l else True }} := by
  -- Unprovable: `own_raft` is an opaque axiom (as in Rocq). It gives neither ownership of
  -- `rf.raftLog` (needed to run `raftLog.term`, which calls the `Storage` interface methods
  -- `Term`/`FirstIndex`/`LastIndex` and `Logger.Panicf`) nor any link between the terms in the
  -- log and `is_committed_in_term` (also an axiom). Replacing `own_raft` by a definition would
  -- need representation predicates for `raftLog`/`unstable`, specs for user-supplied `Storage`
  -- and `Logger` implementations, and a ghost protocol relating storage terms to
  -- `is_committed_in_term`; none of these exist (in Rocq or here).
  sorry -- Rocq: Admitted (trusted)

/-- Rocq `is_readIndexRequest`. -/
def is_readIndexRequest (γ : raft_names) (r : loc) (read_req_ctx : go_string) (index : w64) :
    IProp GF :=
  iprop(∃ read_req : v3.readIndexRequest.t,
    "#r" ∷ r ↦□ read_req ∗
    "#ctx" ∷ read_req.req'.Context' ↦*□ read_req_ctx ∗
    "%Hindex" ∷ ⌜read_req.index' = index⌝ ∗
    "#His_read" ∷ (∃ Φ, is_read_req_ctx γ read_req_ctx Φ))

instance is_readIndexRequest_pers (γ : raft_names) (r : loc) (read_req_ctx : go_string)
    (index : w64) : Persistent (is_readIndexRequest (GF := GF) γ r read_req_ctx index) := by
  unfold is_readIndexRequest; infer_instance

/-- Rocq `own_heartbeat_auth`. -/
def own_heartbeat_auth (γ : raft_names) (term : w64) (highest_index : w64) : IProp GF :=
  iprop(∃ (per_term_gn : GName) (used : gmap go_string GName),
    term ↪[γ.heartbeat_gn]□ per_term_gn ∗
    ghost_map_auth per_term_gn 1 used ∗
    ⌜∀ k, k ∈ used → k = [] ∨ k.length = 8 ∧ uint.Z (le_to_u64 k) ≤ uint.Z highest_index⌝)

/-- Rocq `own_readOnly`. The entries of `read_reqs` are
`((read_req_ctx, index), stale_ids)`.

Lean deviation: an extra parameter `n`, the number of read requests added
so far (`confirmedReads + len(unconfirmedReads)` without wrap-around), with
`"%Hcount" : uint.nat confirmedReads + len unconfirmedReads = n ∧ n < 2^64`.
The heartbeat context of a new request is `u64_le (n + 1)`, which must not
wrap around to an already used context, so `wp_readOnly_addRequest` requires
`n < 2^64 - 1` (Rocq: no `n`, and the overflow side condition is admitted). -/
def own_readOnly (γ : raft_names) (r : loc) (term : w64) (n : Nat) : IProp GF :=
  iprop(∃ (ro : v3.readOnly.t) (acks : gmap w64 w64) (unconfirmedReads : List loc)
      (read_reqs : List ((go_string × w64) × gset w64)),
    "r" ∷ r ↦ ro ∗
    "Hacks" ∷ ro.acks' ↦$ acks ∗
    "#Hacks_wits" ∷ □ (∀ (voterId ackedIdx : w64),
        ⌜acks !! voterId = some ackedIdx⌝ →
        is_heartbeat_ack γ voterId term (u64_le ackedIdx)) ∗
    "%Hoption" ∷ ⌜ro.option' = W64 0⌝ ∗ -- equals ReadOnlySafe
    "%Hcount" ∷ ⌜uint.nat ro.confirmedReads' + unconfirmedReads.length = n ∧ n < 2 ^ 64⌝ ∗
    "unconfirmedReads" ∷ ro.unconfirmedReads' ↦* unconfirmedReads ∗
    "unconfirmedReads_cap" ∷ own_slice_cap loc ro.unconfirmedReads' (DFrac.own 1) ∗
    "#HunconfirmedReads" ∷ □ ([∗list] i ↦ r; x ∈ unconfirmedReads; read_reqs,
        "#readIndexRequest" ∷ is_readIndexRequest γ r x.1.1 x.1.2 ∗
        "#Hhb" ∷ is_heartbeat_ctx_stale γ term
          (u64_le (ro.confirmedReads' + W64 (i + 1 : Nat))) x.2 ∗
        "%Hstale_contains" ∷ ⌜union_list ((read_reqs.take i).map Prod.snd) ⊆ x.2⌝ ∗
        "#Hstale_or_safe" ∷ (⌜is_quorum cfg x.2⌝ ∨
          (∃ Φ, is_read_req_ctx γ x.1.1 Φ ∗ is_read_index γ x.1.2 Φ))) ∗
    "Hhb_auth" ∷ own_heartbeat_auth γ term (ro.confirmedReads' + W64 unconfirmedReads.length))

theorem own_heartbeat_auth_new (stale_ids : gset w64) (γ : raft_names) (term : w64)
    (highest_index : w64) :
    uint.Z highest_index < 2 ^ 64 - 1 →
    ⊢ own_heartbeat_auth (GF := GF) γ term highest_index ==∗
      own_heartbeat_auth γ term (highest_index + W64 1) ∗
      is_heartbeat_ctx γ term (u64_le (highest_index + W64 1)) stale_ids := by
  intro Hno
  unfold own_heartbeat_auth is_heartbeat_ctx
  iintro ⟨%per_term_gn, %used, #Hp, Hauth, %Hused⟩
  imod dghost_var_alloc stale_ids with ⟨%gn, H⟩
  imod dghost_var_persist gn 1 stale_ids $$ H with #H
  have Hfresh : used.lookup (u64_le (highest_index + W64 1)) = none := by
    cases h : used.lookup (u64_le (highest_index + W64 1)) with
    | none => rfl
    | some v =>
      exfalso
      have hmem : u64_le (highest_index + W64 1) ∈ used := by
        rw [gmap.mem_iff]; exact Option.isSome_iff_exists.mpr ⟨v, h⟩
      rcases Hused _ hmem with h1 | ⟨-, h2⟩
      · have := u64_le_length (highest_index + W64 1)
        rw [h1] at this; simp at this
      · rw [u64_le_to_word] at h2
        word
  imod ghost_map_insert_persist (u64_le (highest_index + W64 1)) gn Hfresh $$ Hauth
    with ⟨Hauth, #Hk⟩
  imodintro
  isplitl [Hauth]
  · iexists per_term_gn, _
    iframe # ∗
    ipureintro
    intro k hk
    have hk' := (gmap.lookup_insert_is_Some used _ k gn).mp hk
    rcases hk' with rfl | ⟨-, hk'⟩
    · right
      rw [u64_le_to_word, u64_le_length]
      exact ⟨rfl, by word⟩
    · rcases Hused k hk' with h | ⟨h1, h2⟩
      · left; exact h
      · right; exact ⟨h1, by word⟩
  · iexists per_term_gn, gn
    iframe #

theorem own_heartbeat_auth_agree (stale_ids : gset w64) (γ : raft_names) (term : w64)
    (ctx : go_string) (highest_index : w64) :
    ctx ≠ [] →
    ⊢ is_heartbeat_ctx (GF := GF) γ term ctx stale_ids -∗
      own_heartbeat_auth γ term highest_index -∗
      ⌜ctx.length = 8 ∧ uint.Z (le_to_u64 ctx) ≤ uint.Z highest_index⌝ := by
  intro Hctx
  unfold own_heartbeat_auth is_heartbeat_ctx
  iintro ⟨%gn1, %cgn1, #Hp, #Hfrag, -⟩ ⟨%gn2, %used, #Hp2, Hauth, %Hin⟩
  icases ghost_map_elem_agree term γ.heartbeat_gn _ _ gn1 gn2 $$ Hp Hp2 with %Heq
  subst Heq
  icases ghost_map_lookup $$ Hauth Hfrag with %Hl
  ipureintro
  have hmem : ctx ∈ used := by
    rw [gmap.mem_iff]; exact Option.isSome_iff_exists.mpr ⟨cgn1, Hl⟩
  rcases Hin ctx hmem with h | h
  · exact absurd h Hctx
  · exact h

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
theorem wp_readOnly_recvAck (γ : raft_names) (r : loc) (term : w64) («from» : w64)
    (ctx_sl : slice.t) (ctx : List w8) (v : w64) (n : Nat) :
    {{ is_pkg_init (PROP := IProp GF) raft ∗
        "Hown" ∷ own_readOnly cfg γ r term n ∗
        "Hctx" ∷ ctx_sl ↦* ctx ∗
        "#Hack" ∷ is_heartbeat_ack γ «from» term ctx }}
      (App (App (Val (r @!! go.type.PointerType v3.readOnly @!! go!"recvAck")) (Val #«from»))
        (Val #ctx_sl))
    {{ RET #(); own_readOnly cfg γ r term n }} := by
  wp_start as ⟨Hown, Hctx, #Hack⟩
  iunfold own_readOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  wp_if_destruct
  · iapply HΦ
    unfold own_readOnly
    iexists ro, acks, unconfirmedReads, read_reqs
    iframe # ∗
    ipureintro; exact ⟨Hoption, Hcount⟩
  · wp_apply wp_map_lookup1 $$ Hacks as Hacks
    ihave %Hctx_len := own_slice_len _ _ _ $$ Hctx
    iunfold is_heartbeat_ack at Hack
    icases Hack with ⟨%srvs, #Hhb_ctx, %Hnot⟩
    have Hne : ctx ≠ [] := by
      intro h; rw [h] at Hctx_len; simp at Hctx_len; apply Hif; word
    icases own_heartbeat_auth_agree srvs γ term ctx _ Hne $$ Hhb_ctx Hhb_auth with
      % ⟨Hlen, Hbounds⟩
    rw [show ctx = ctx ++ [] by simp]
    wp_apply encoding.binary.wp_LittleEndian_Uint64 ctx_sl ctx _ [] Hlen $$ [$Hctx] as Hctx
    wp_func_call
    wp_call
    rw [List.append_nil]
    -- the new acked index `nv` has a heartbeat-ack witness
    have Hfin : ∀ nv : w64, (nv = le_to_u64 ctx ∨ acks !! «from» = some nv) →
        ⊢ (□ (∀ (voterId ackedIdx : w64), ⌜acks !! voterId = some ackedIdx⌝ →
              is_heartbeat_ack (GF := GF) γ voterId term (u64_le ackedIdx))) -∗
          is_heartbeat_ctx γ term ctx srvs -∗
          □ (∀ (voterId ackedIdx : w64), ⌜(<[«from» := nv]> acks) !! voterId = some ackedIdx⌝ →
              is_heartbeat_ack γ voterId term (u64_le ackedIdx)) := by
      intro nv Hnv
      iintro #Hacks_wits #Hhb_ctx
      imodintro
      iintro %voterId %ackedIdx %Hlookup
      by_cases Hv : «from» = voterId
      · subst Hv
        rw [gmap.lookup_insert] at Hlookup
        cases Hlookup
        rcases Hnv with rfl | Hnv
        · rw [le_to_u64_le ctx Hlen]
          unfold is_heartbeat_ack
          iexists srvs
          iframe #
          ipureintro; exact Hnot
        · iapply Hacks_wits $$ %«from» %nv %Hnv
      · rw [gmap.lookup_insert_ne _ _ Hv] at Hlookup
        iapply Hacks_wits $$ %voterId %ackedIdx %Hlookup
    wp_if_destruct
    · have Hsome : acks !! «from» = some ((acks !! «from»).getD (zero_val w64)) := by
        cases h : acks !! «from» with
        | none =>
          rw [h, Option.getD_none, show zero_val w64 = W64 0 from rfl] at Hif
          word
        | some w => rfl
      wp_apply wp_map_insert $$ Hacks as Hacks
      iapply HΦ
      ihave #Hw := Hfin _ (Or.inr Hsome) $$ Hacks_wits Hhb_ctx
      unfold own_readOnly
      iexists ro, _, unconfirmedReads, read_reqs
      iframe # ∗
      ipureintro; exact ⟨Hoption, Hcount⟩
    · wp_apply wp_map_insert $$ Hacks as Hacks
      iapply HΦ
      ihave #Hw := Hfin _ (Or.inl rfl) $$ Hacks_wits Hhb_ctx
      unfold own_readOnly
      iexists ro, _, unconfirmedReads, read_reqs
      iframe # ∗
      ipureintro; exact ⟨Hoption, Hcount⟩

/-- Rocq `own_AckedIndexer`. The Rocq Texan triple (an `iProp`) is written out. -/
def own_AckedIndexer (i : interface.t_ok) (acks : gmap w64 w64) (I : IProp GF) : IProp GF :=
  iprop("HI" ∷ I ∗
    "#HAckedIndex" ∷ (∀ voterID : w64, □ ∀ Φ : val → IProp GF, I -∗
      ▷ (I -∗ Φ (PairV #((acks !! voterID).getD (W64 0)) #(decide ((acks !! voterID).isSome)))) -∗
      WP (App (Val #(methods i.ty go!"AckedIndex" i.v)) (Val #voterID)) {{ Φ }}))

end wps

/-- Rocq `Axiom wp_JointConfig__CommittedIndex`. (Rocq's statement does not bind
the `quorum` package assumptions; here they are bound explicitly.) -/
axiom wp_JointConfig__CommittedIndex (cfg : gset w64)
    [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF]
    [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]
    (l : interface.t_ok) (acks : gmap w64 w64) (c : v3.quorum.JointConfig.t) (voters_ref : loc)
    (voters : gmap w64 Unit) (I : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
        "Hl" ∷ own_AckedIndexer l acks I ∗
        "%Hc" ∷ ⌜c.arr = [voters_ref, map.nil]⌝ ∗
        "voters" ∷ voters_ref ↦$ voters ∗
        "%Hvoters_cfg" ∷ ⌜domSet voters = cfg⌝ }}
      (App (Val (c @!! v3.quorum.JointConfig @!! go!"CommittedIndex")) (Val #(interface.ok l)))
    {{ (c : w64), RET #c; own_AckedIndexer l acks I ∗
        voters_ref ↦$ voters ∗
        ⌜0 ≤ sint.Z c ∧
          ∃ srvs, is_quorum cfg srvs ∧
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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

local notation "raft" => pkg_id.go_etcd_io.raft.v3

/-- Rocq `MsgReadIndex`. -/
def MsgReadIndex : w32 := W32 15

theorem wp_raft__sendMsgReadIndexresponse (γ : raft_names) (r : loc) (rf : v3.raft.t)
    (m : v3.raftpb.Message.t) :
    {{ "Hr" ∷ r ↦ rf ∗
        "Hrf" ∷ own_raft (GF := GF) γ rf ∗
        "%HmType" ∷ ⌜m.Type' = MsgReadIndex⌝ ∗
        "#Hcom_in_term" ∷ True }}
      (App (App (Val (@! v3.sendMsgReadIndexResponse)) (Val #r)) (Val #m))
    {{ RET #(); True }} := by
  -- Unprovable as stated: `"#Hcom_in_term" ∷ True` is a placeholder (as in Rocq) for what
  -- `readOnly.addRequest` needs (`is_raft_commit_inv`, `own_committed_in_term`,
  -- `is_read_req_ctx`, and now the request-count bound `n < 2^64 - 1`), and `own_raft`
  -- (an opaque axiom, see `wp_raft__committedEntryInCurrentTerm`) provides neither
  -- `own_readOnly` for `rf.readOnly'` nor the state used by `bcastHeartbeat`
  -- (`trk.Visit` with a closure, `sendHeartbeat`, `send`, which calls `Logger` methods).
  sorry -- Rocq: Admitted

theorem wp_raft__stepLeader_MsgReadIndex (γ : raft_names) (r : loc) (rf : v3.raft.t)
    (m : v3.raftpb.Message.t) :
    {{ "Hr" ∷ r ↦ rf ∗
        "Hrf" ∷ own_raft (GF := GF) γ rf ∗
        "%HmType" ∷ ⌜m.Type' = MsgReadIndex⌝ }}
      (App (App (Val (@! v3.stepLeader)) (Val #r)) (Val #m))
    {{ RET #(); True }} := by
  -- Unprovable as stated: `stepLeader` uses `raft` state (trk, readOnly, raftLog, ...) that only
  -- the opaque axiom `own_raft` describes, and calls `sendMsgReadIndexResponse` and
  -- `committedEntryInCurrentTerm` (above). It also calls `r.trk.IsSingleton()`, whose (now proved)
  -- spec `wp_ProgressTracker__IsSingleton` needs the voter-map points-tos, which `own_raft`
  -- does not provide.
  sorry -- Rocq: Admitted

set_option goose.wp.extras true in
set_option maxHeartbeats 1000000 in
theorem wp_readOnly_maybeAdvance (γ : raft_names) (r : loc) (term : w64)
    (c : v3.quorum.JointConfig.t) (voters_ref : loc) (voters : gmap w64 Unit) (n : Nat) :
    0 < gmap.size cfg →
    {{ is_pkg_init (PROP := IProp GF) raft ∗
        "Hown" ∷ own_readOnly cfg γ r term n ∗
        -- The config `c` is simple (not joint): first component is voters, second is empty.
        "%Hc" ∷ ⌜c.arr = [voters_ref, map.nil]⌝ ∗
        "voters" ∷ voters_ref ↦$ voters ∗
        "%Hvoters_cfg" ∷ ⌜domSet voters = cfg⌝ }}
      (App (Val (r @!! go.type.PointerType v3.readOnly @!! go!"maybeAdvance")) (Val #c))
    {{ (rs : slice.t) (reads : List loc), RET #rs;
        own_readOnly cfg γ r term n ∗
        voters_ref ↦$ voters ∗
        rs ↦* reads ∗
        -- Every returned read request has a valid read index witness.
        □ (∀ (i : Nat) (rp : loc), ⌜reads[i]? = some rp⌝ →
            ∃ (read_req_ctx : go_string) (index : w64) (Φ : List (List w8) → IProp GF),
              is_readIndexRequest γ rp read_req_ctx index ∗
              is_read_req_ctx γ read_req_ctx Φ ∗
              is_read_index γ index Φ) }} := by
  intro Hsize
  wp_start as ⟨Hown, %Hc, voters, %Hvoters_cfg⟩
  iunfold own_readOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave HAI : own_AckedIndexer (interface.mk (go.type.PointerType v3.readOnly) #r) acks
      iprop(r ↦ ro ∗ ro.acks' ↦$ acks) $$ [r Hacks]
  · unfold own_AckedIndexer
    isplitl [r Hacks]
    · iapply to_named; iframe
    iintro %voterID !> %Φ ⟨r, Hacks⟩ HΦ
    dsimp only [interface.mk]
    wp_method_call
    wp_call
    unfold v3.«readOnly__AckedIndexⁱᵐᵖˡ»
    wp_auto
    wp_apply wp_map_lookup2 $$ Hacks as Hacks
    rw [show zero_val w64 = W64 0 from rfl]
    iapply HΦ
    iframe
  wp_apply wp_JointConfig__CommittedIndex cfg _ acks c voters_ref voters _ $$ [$HAI $voters]
    as %newConfirmedReads ⟨HAI, voters, %Hconfirm⟩
  · ipureintro; exact ⟨Hc, Hvoters_cfg⟩
  iunfold own_AckedIndexer at HAI
  icases HAI with ⟨⟨r, Hacks⟩, -⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ %slice.nil %([] : List loc)
    ihave Hnil := own_slice_nil (V := loc) (GF := GF) (DFrac.own 1)
    iframe Hnil voters
    isplitl
    · unfold own_readOnly
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
    iunfold is_heartbeat_ack at Hack
    icases Hack with ⟨%srvs, #Hhb_ctx, -⟩
    have Hne : u64_le j ≠ [] := by
      intro h; have := u64_le_length j; rw [h] at this; simp at this
    icases own_heartbeat_auth_agree srvs γ term (u64_le j) _ Hne $$ Hhb_ctx Hhb_auth with
      % ⟨-, Hagree⟩
    ipureintro
    rw [u64_le_to_word] at Hagree
    exact Hagree
  have Hin_bounds : uint.Z newConfirmedReads ≤
      uint.Z (ro.confirmedReads' + W64 unconfirmedReads.length) := by
    have Hq_size : 0 < gmap.size (ack_q ∩ cfg) := by unfold is_quorum at Hack_quorum; omega
    obtain ⟨s, Hin_q⟩ := gmap.size_pos_elem_of _ Hq_size
    have Hs := Hq_le s ((gmap.elem_of_intersection _ _ _).mp Hin_q).1
    cases Hlookup : acks !! s with
    | none =>
      rw [Hlookup, Option.getD_none] at Hs
      exfalso; word
    | some j =>
      rw [Hlookup, Option.getD_some] at Hs
      have := Hack_bounds s j Hlookup
      word
  ihave %Hwf := own_slice_wf _ _ _ $$ unconfirmedReads
  ihave %Hlen := own_slice_len _ _ _ $$ unconfirmedReads
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
  icases (own_slice_slice (newConfirmedReads - ro.confirmedReads') ro.unconfirmedReads'.len
      ro.unconfirmedReads' _ unconfirmedReads ⟨Hdiff.1, Hdiff.2, Int.le_refl _⟩).1 $$ unconfirmedReads
    with ⟨Hfront, Hback, -⟩
  rw [subslice_to_end _ _ _ (Nat.le_of_eq Hlen.1), Hk]
  ihave Hcap := (own_slice_cap_slice ro.unconfirmedReads' (newConfirmedReads - ro.confirmedReads')
      _ ⟨Hdiff.1, Hdiff.2, Hwf.2⟩).1 $$ unconfirmedReads_cap
  iapply HΦ $$ %_ %(unconfirmedReads.take k)
  iframe Hfront voters
  -- the remaining unconfirmed reads
  ihave #Hnew : (□ ([∗list] i ↦ r;x ∈ unconfirmedReads.drop k;read_reqs.drop k,
      "#readIndexRequest" ∷ is_readIndexRequest γ r x.1.1 x.1.2 ∗
      "#Hhb" ∷ is_heartbeat_ctx_stale γ term
        (u64_le (newConfirmedReads + W64 (i + 1 : Nat))) x.2 ∗
      "%Hstale_contains" ∷ ⌜union_list (((read_reqs.drop k).take i).map Prod.snd) ⊆ x.2⌝ ∗
      "#Hstale_or_safe" ∷ (⌜is_quorum cfg x.2⌝ ∨
        (∃ Φ, is_read_req_ctx γ x.1.1 Φ ∗ is_read_index γ x.1.2 Φ))) : IProp GF) $$ []
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
    rw [List.take_add, List.map_append, gmap.union_list_app] at Hsc
    rw [gmap.elem_of_subseteq] at Hsc ⊢
    intro y hy
    exact Hsc y ((gmap.elem_of_union _ _ _).mpr (Or.inr hy))
  rw [show ro.confirmedReads' + W64 (unconfirmedReads.length : Int) =
      newConfirmedReads + W64 ((unconfirmedReads.drop k).length : Int) by
    rw [List.length_drop, show ((unconfirmedReads.length - k : Nat) : Int) =
      (unconfirmedReads.length : Int) - k by omega, Hk_eq]
    word]
  isplitl
  · unfold own_readOnly
    iexists { ro with
        unconfirmedReads' := slice.slice ro.unconfirmedReads' loc
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
        iunfold is_heartbeat_ack at Hack
        icases Hack with ⟨%srvs, #Hack, %Hnot_stale⟩
        have Hjb := Hack_bounds x j Hacks_lookup
        -- the read whose heartbeat context is `u64_le j`
        have Hm : uint.nat (j - ro.confirmedReads') - 1 < unconfirmedReads.length := by
          rw [Hlen.1]; word
        obtain ⟨ur_m, Hur⟩ : ∃ ur_m, unconfirmedReads[uint.nat (j - ro.confirmedReads') - 1]? =
            some ur_m := ⟨_, List.getElem?_eq_getElem Hm⟩
        obtain ⟨y, Hy⟩ : ∃ y, read_reqs[uint.nat (j - ro.confirmedReads') - 1]? = some y :=
          ⟨read_reqs[uint.nat (j - ro.confirmedReads') - 1]'(by omega), List.getElem?_eq_getElem _⟩
        ihave Hentry2 := BigSepL2.bigSepL2_lookup Hur Hy $$ HunconfirmedReads
        icases Hentry2 with ⟨-, #Hhb2, %Hsc2, -⟩
        iunfold is_heartbeat_ctx_stale at Hhb2
        icases Hhb2 with ⟨#Hhb2, -⟩
        rw [show ro.confirmedReads' +
            W64 (((uint.nat (j - ro.confirmedReads') - 1 + 1 : Nat)) : Int) = j by word]
        icases is_heartbeat_ctx_agree γ term (u64_le j) srvs y.2 $$ Hack Hhb2 with %Heq
        subst Heq
        ipureintro
        apply Hnot_stale
        have Him : i ≤ uint.nat (j - ro.confirmedReads') - 1 := by
          have : (i : Int) < k := by exact_mod_cast Hik
          word
        rcases Nat.lt_or_eq_of_le Him with Him | Him
        · rw [gmap.elem_of_subseteq] at Hsc2
          apply Hsc2
          rw [gmap.elem_of_union_list]
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
theorem wp_readOnly_addRequest (γ : raft_names) (r : loc) (term commitIndex : w64)
    (req : v3.raftpb.Message.t) (read_req_ctx : go_string) (log : List (List w8)) (dq : DFrac)
    (Ψ : List (List w8) → IProp GF) (n : Nat) :
    {{ is_pkg_init (PROP := IProp GF) raft ∗
        "#Hinv" ∷ is_raft_commit_inv γ ∗
        "Hown" ∷ own_readOnly cfg γ r term n ∗
        "Hcom" ∷ own_committed_in_term γ term log ∗
        "%HcommitIndex" ∷ ⌜uint.nat commitIndex = log.length⌝ ∗
        -- Lean deviation (Rocq: no such precondition; see `own_readOnly`)
        "%Hn" ∷ ⌜n < 2 ^ 64 - 1⌝ ∗
        "Hctx" ∷ req.Context' ↦*{dq} read_req_ctx ∗
        "#Hread_ctx" ∷ is_read_req_ctx γ read_req_ctx Ψ }}
      (App (App (Val (r @!! go.type.PointerType v3.readOnly @!! go!"addRequest"))
        (Val #commitIndex)) (Val #req))
    {{ RET #(); own_readOnly cfg γ r term (n + 1) }} := by
  wp_start as ⟨#Hinv, Hown, Hcom, %HcommitIndex, %Hn, Hctx, #Hread_ctx⟩
  iunfold own_readOnly at Hown
  icases Hown with ⟨%ro, %acks, %unconfirmedReads, %read_reqs, Hown⟩
  iNamed Hown
  wp_auto
  irename «$sl0» => Hreq
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := loc) (t := go.type.PointerType v3.readIndexRequest) [«$sl0_ptr»]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_apply +noauto wp_slice_append (V := loc) (t := go.type.PointerType v3.readIndexRequest)
    ro.unconfirmedReads' unconfirmedReads _ [«$sl0_ptr»] (DFrac.own 1)
    $$ [unconfirmedReads unconfirmedReads_cap Hsl]
  · iframe
  iintro %s' ⟨Hs', Hcap', -⟩
  iapply wp_fupd
  wp_auto_lc 1
  ihave #Hrc := Hread_ctx
  iunfold is_read_req_ctx at Hrc
  icases Hrc with ⟨%γreq, -, -, #Hau⟩
  imod try_read cfg γ term log Ψ $$ [Hlc1 Hcom] with ⟨%stale_ids', #Hstale, Hcom, #Hmaybe_read⟩
  · iframe # ∗
    ipureintro
    rw [← HcommitIndex]; word
  ihave %Hrr_len := BigSepL2.bigSepL2_length $$ HunconfirmedReads
  imod own_heartbeat_auth_new
      (union_list (read_reqs.map Prod.snd ++ [stale_ids'])) γ term _
      -- (Rocq: admitted overflow side condition; here from `Hcount` and `Hn`)
      (by have := Hcount.1; word)
      $$ Hhb_auth with ⟨Hhb_auth, #Hhb⟩
  ipersist Hreq
  ipersist Hctx
  -- witnesses for the servers in the new stale set
  ihave #Hstale'' : (□ (∀ id, ⌜id ∈ union_list (read_reqs.map Prod.snd ++ [stale_ids'])⌝ →
      ∃ term', is_term_lb γ id term' ∗ ⌜sint.nat term < sint.nat term'⌝) : IProp GF) $$ []
  · imodintro
    iintro %id %Hin
    rw [gmap.union_list_app, gmap.elem_of_union] at Hin
    rcases Hin with Hin | Hin
    · -- `id` is in the stale set of an earlier read; the last one contains them all
      rcases List.eq_nil_or_concat read_reqs with Hnil | ⟨rr', y, Hrr⟩
      · subst Hnil; simp [union_list] at Hin
        exact absurd Hin (gmap.not_elem_of_empty _)
      subst Hrr
      simp only [List.concat_eq_append] at *
      have Hlt : rr'.length < unconfirmedReads.length := by simp at Hrr_len; omega
      obtain ⟨ur_l, Hur⟩ : ∃ x, unconfirmedReads[rr'.length]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      ihave Hentry := BigSepL2.bigSepL2_lookup (i := rr'.length) (x2 := y) Hur (by simp) $$ HunconfirmedReads
      icases Hentry with ⟨-, #Hhb', %Hsc, -⟩
      iunfold is_heartbeat_ctx_stale at Hhb'
      icases Hhb' with ⟨-, #Hw⟩
      iapply Hw $$ %id
      ipureintro
      rw [show (rr' ++ [y]).take rr'.length = rr' by simp] at Hsc
      simp only [List.map_append, List.map_cons, List.map_nil] at Hin
      rw [gmap.union_list_app, gmap.elem_of_union] at Hin
      rcases Hin with Hin | Hin
      · rw [gmap.elem_of_subseteq] at Hsc; exact Hsc id Hin
      · simp [union_list, gmap.elem_of_union] at Hin
        rcases Hin with Hin | Hin
        · exact Hin
        · exact absurd Hin (gmap.not_elem_of_empty _)
    · iapply Hstale $$ %id
      ipureintro
      simp [union_list, gmap.elem_of_union] at Hin
      rcases Hin with Hin | Hin
      · exact Hin
      · exact absurd Hin (gmap.not_elem_of_empty _)
  -- the reads queue with the new request
  ihave #Hnew : (□ ([∗list] i ↦ r;x ∈ unconfirmedReads ++ [«$sl0_ptr»];
      read_reqs ++ [((read_req_ctx, commitIndex), union_list (read_reqs.map Prod.snd ++ [stale_ids']))],
      "#readIndexRequest" ∷ is_readIndexRequest γ r x.1.1 x.1.2 ∗
      "#Hhb" ∷ is_heartbeat_ctx_stale γ term (u64_le (ro.confirmedReads' + W64 (i + 1 : Nat))) x.2 ∗
      "%Hstale_contains" ∷ ⌜union_list (((read_reqs ++
          [((read_req_ctx, commitIndex), union_list (read_reqs.map Prod.snd ++ [stale_ids']))]).take i).map
          Prod.snd) ⊆ x.2⌝ ∗
      "#Hstale_or_safe" ∷ (⌜is_quorum cfg x.2⌝ ∨
        (∃ Φ, is_read_req_ctx γ x.1.1 Φ ∗ is_read_index γ x.1.2 Φ))) : IProp GF) $$ []
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
      · unfold is_readIndexRequest
        iexists { req' := req, index' := commitIndex }
        iframe # ∗
        isplitr
        · ipureintro; rfl
        iexists Ψ
        iexact Hread_ctx
      isplitr
      · unfold is_heartbeat_ctx_stale
        iapply to_named
        iframe #
      isplitr
      · ipureintro
        rw [Hrr_len, List.take_left, gmap.union_list_app, gmap.elem_of_subseteq]
        intro x hx
        exact (gmap.elem_of_union _ _ _).mpr (Or.inl hx)
      icases Hmaybe_read with (#Hread | %Hq)
      · iright
        iexists Ψ
        iframe #
        rw [show W64 (log.length : Int) = commitIndex by rw [← HcommitIndex]; word]
        iexact Hread
      · ileft
        ipureintro
        refine quorums_subseteq cfg _ _ ?_ Hq
        rw [gmap.union_list_app, gmap.elem_of_subseteq]
        intro x hx
        refine (gmap.elem_of_union _ _ _).mpr (Or.inr ?_)
        simp [union_list, gmap.elem_of_union, hx]
  rw [show ro.confirmedReads' + W64 (unconfirmedReads.length : Int) + W64 1 =
      ro.confirmedReads' + W64 ((unconfirmedReads ++ [«$sl0_ptr»]).length : Int) by
    simp only [List.length_append, List.length_singleton]; word]
  imodintro
  iapply HΦ
  unfold own_readOnly
  iexists { ro with unconfirmedReads' := s' }, acks, unconfirmedReads ++ [«$sl0_ptr»],
    read_reqs ++ [((read_req_ctx, commitIndex), union_list (read_reqs.map Prod.snd ++ [stale_ids']))]
  dsimp only
  iframe # ∗
  ipureintro; refine ⟨Hoption, ?_, by omega⟩
  simp only [List.length_append, List.length_singleton]
  omega

end wps2

end proof

end go_etcd_io.raft.v3_proof.readonly

end Perennial
