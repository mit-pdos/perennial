/-
Port of `new/golang/theory/chan/idioms/future.v`: the future channel idiom.

Multiple workers fulfill promises independently and a single consumer awaits all
results (e.g. the replicated search pattern from Rob Pike's "Go Concurrency Patterns").

How to use:
1. Initialize a channel for use as a future with `start_future`.
2. For each producer, allocate a `Fulfill` with `future_alloc_promise`, giving it a
   predicate contract `P_i` that describes what that producer will provide.
3. Each worker sends its result using `wp_future_fulfill`, providing
   `Fulfill γ contract ∗ contract v`, bundled as `Fulfilled γ v`.
4. The consumer receives using `wp_future_await`; each receive resolves one contract
   from `pending`, returning `P v` for some `P` that was removed from `pending`.
5. When `pending` is empty, all contracts have been satisfied.

Matching happens *at receive time*: each receive identifies which contract was
fulfilled (via ghost state agreement) and removes it from `pending`.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

structure future_names where
  chan_name : chan_names
  pending_set_name : GName

section future
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

/-- `Fulfill γ contract` is a token representing a registered contract. The holder
commits to eventually sending a value `v` satisfying `contract v`. Internally, it holds
half of a saved predicate and an auth_set fragment. -/
def Fulfill (γ : future_names) (contract : V → IProp GF) : IProp GF :=
  iprop(∃ (gn : GName), saved_pred_own gn (DFrac.own (1 : Qp).half) contract ∗
    auth_set_frag γ.pending_set_name gn)

/-- `Fulfilled γ v` bundles a `Fulfill` with evidence that the contract is satisfied. This
is what gets transferred through the channel. -/
def Fulfilled (γ : future_names) (v : V) : IProp GF :=
  iprop(∃ contract, Fulfill γ contract ∗ contract v)

/-- `Await γ pending` is the consumer's tracking state. `pending` is the list of contracts
not yet matched to a received value. -/
def Await (γ : future_names) (pending : List (V → IProp GF)) : IProp GF :=
  iprop(∃ (pending_map : gmap GName (V → IProp GF)),
    auth_set_auth γ.pending_set_name (domSet pending_map) ∗
    ⌜((map_to_list pending_map).map Prod.snd).Perm pending⌝ ∗
    [∗map] gn ↦ P ∈ pending_map, saved_pred_own gn (DFrac.own (1 : Qp).half) P)

/-- The future invariant. -/
def future_inv (γ : future_names) : IProp GF :=
  iprop(∃ (s : chanstate.t V), "Hch" ∷ own_chan γ.chan_name V s ∗
    (match s with
     | .Buffered msgs => iprop([∗list] v ∈ msgs, Fulfilled γ v)
     | .SndPending v => Fulfilled γ v
     | .SndCommit v => Fulfilled γ v
     | .Idle | .RcvPending | .RcvCommit => iprop(True)
     | _ => iprop(False)))

variable (V) in
/-- `is_future γ ch` is the persistent channel invariant. The channel carries `Fulfilled`
tokens — values bundled with their contract evidence. -/
def is_future (γ : future_names) (ch : loc) : IProp GF :=
  iprop(is_chan ch γ.chan_name V ∗ inv nroot (future_inv (V := V) γ))

instance is_future_pers (γ : future_names) (ch : loc) : Persistent (is_future V (GF := GF) γ ch) := by
  unfold is_future; infer_instance

theorem map_to_list_snd_insert {K A : Type} [DecidableEq K] (m : gmap K A) (k : K) (v : A)
    (h : m !! k = none) :
    ((map_to_list (<[k := v]> m)).map Prod.snd).Perm (v :: (map_to_list m).map Prod.snd) :=
  (gmap.map_to_list_insert m k v h).map Prod.snd

theorem map_to_list_snd_delete {K A : Type} [DecidableEq K] (m : gmap K A) (k : K) (v : A)
    (h : m !! k = some v) :
    ((map_to_list m).map Prod.snd).Perm (v :: (map_to_list (gmap.delete k m)).map Prod.snd) :=
  (gmap.map_to_list_delete m k v h).map Prod.snd

theorem Permutation_cons_split {A : Type} (x : A) (l l' : List A) (h : l.Perm (x :: l')) :
    ∃ pre post, l = pre ++ x :: post ∧ l'.Perm (pre ++ post) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem (h.symm.subset (List.mem_cons_self))
  refine ⟨pre, post, rfl, ?_⟩
  have h2 : (x :: l').Perm (x :: (pre ++ post)) := h.symm.trans List.perm_middle
  exact h2.cons_inv

theorem start_future (ch : loc) (γ : chan_names) (s : chanstate.t V)
    (Hs : s = .Idle ∨ s = .Buffered []) :
    ⊢ is_chan ch γ V -∗ own_chan γ V s ={⊤}=∗
      ∃ γmf, is_future V γmf ch ∗ Await (V := V) γmf [] := by
  iintro #Hch Hoc
  imod auth_set_init (A := GName) with ⟨%γpending, Hset_auth⟩
  imod inv_alloc nroot ⊤ (future_inv (V := V) ⟨γ, γpending⟩) $$ [Hoc] with #Hinv
  · inext
    unfold future_inv
    iexists s
    iframe
    rcases Hs with rfl | rfl <;> dsimp only
    · itrivial
    · iapply BigSepL.bigSepL_nil.2; iempintro
  imodintro
  iexists ⟨γ, γpending⟩
  isplitl []
  · unfold is_future; iframe #
  unfold Await
  iexists ∅
  rw [gmap.dom_empty_L]
  iframe
  isplitl []
  · ipureintro; rw [gmap.map_to_list_empty]; exact .nil
  · iapply BigSepM.bigSepM_empty.2; iempintro

theorem future_alloc_promise (γ : future_names) (ch : loc) (contract : V → IProp GF)
    (pending : List (V → IProp GF)) :
    ⊢ is_future V γ ch -∗ Await γ pending ={⊤}=∗
      Fulfill γ contract ∗ Await γ (pending ++ [contract]) := by
  iintro #Hmf HAwait
  unfold Await
  icases HAwait with ⟨%pending_map, Hauth, %Hperm, Hfrags⟩
  imod saved_pred_alloc_cofinite contract ((map_to_list pending_map).map Prod.fst) (DFrac.own 1)
    DFrac.valid_own_one with ⟨%gn, %Hfresh, Hpred⟩
  have Hnone : pending_map !! gn = none := by
    cases h : pending_map !! gn with
    | none => rfl
    | some P =>
      exfalso; apply Hfresh
      exact List.mem_map.2 ⟨(gn, P), (gmap.elem_of_map_to_list _ _ _).2 h, rfl⟩
  icases saved_pred_halves _ _ $$ Hpred with ⟨Hpred1, Hpred2⟩
  imod auth_set_alloc gn _ _ ((gmap.not_elem_of_dom _ _).2 Hnone) $$ Hauth with ⟨Hauth, Hfrag⟩
  imodintro
  isplitl [Hpred1 Hfrag]
  · unfold Fulfill; iexists gn; iframe
  iexists (<[gn := contract]> pending_map)
  rw [gmap.dom_insert_L]
  iframe Hauth
  isplitl []
  · ipureintro
    exact (map_to_list_snd_insert _ _ _ Hnone).trans
      ((Hperm.cons contract).trans (List.perm_append_singleton contract pending).symm)
  · iapply (BigSepM.bigSepM_insert (Φ := fun gn (P : V → IProp GF) =>
      saved_pred_own (GF := GF) gn (DFrac.own (1 : Qp).half) P) Hnone).2
    iframe

theorem future_fulfill_au (γ : future_names) (ch : loc) (v : V) (Φ : IProp GF) :
    ⊢ is_future V γ ch -∗ £ 1 ∗ £ 1 ∗ £ 1 ∗ Fulfilled γ v -∗ ▷ (True -∗ Φ) -∗
      send_au γ.chan_name v Φ := by
  unfold is_future send_au
  iintro ⟨#Hisch, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3, HFulfilled⟩ Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold future_inv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HFulfilled] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HFulfilled
    imodintro
    iapply Hau
    itrivial
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HFulfilled] with -
    · inext; iexists .SndPending v; iframe
    imodintro
    unfold send_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hoc1, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc1
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .Idle; iframe
      imodintro
      iapply Hau
      itrivial
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HFulfilled] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iapply Hau
    itrivial
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_future_fulfill (γ : future_names) (ch : loc) (v : V) :
    {{ is_future V γ ch ∗ Fulfilled γ v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hmf, HFulfilled⟩ HΦ
  ihave #Hch : is_chan ch γ.chan_name V $$ [Hmf]
  · unfold is_future; icases Hmf with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply future_fulfill_au γ ch v (Φ #()) $$ Hmf [$Hlc1 $Hlc2 $Hlc3 $HFulfilled]
  inext
  iintro _
  iapply HΦ
  itrivial

/-- Matching a received `Fulfilled` against the pending contracts (Rocq: the `Hmatch`
assertion inside `future_await_au`). -/
theorem future_match (γ : future_names) (pending : List (V → IProp GF)) (v_rcv : V) :
    ⊢ £ 1 -∗ Fulfilled γ v_rcv -∗ Await γ pending ={⊤}=∗
      ∃ (P : V → IProp GF) (pre post : List (V → IProp GF)),
        ⌜pending = pre ++ P :: post⌝ ∗ P v_rcv ∗ Await γ (pre ++ post) := by
  unfold Fulfilled Fulfill Await
  iintro Hlc ⟨%contract_f, ⟨%gn_f, Hpred_f, Hfrag_f⟩, Hcontract_v⟩
    ⟨%pending_map, Hauth, %Hperm, Hfrags⟩
  ihave %Hin := auth_set_elem _ _ _ $$ Hauth Hfrag_f
  obtain ⟨P, Hlookup⟩ := (gmap.elem_of_dom _ _).1 Hin
  icases (BigSepM.bigSepM_delete (Φ := fun gn (P : V → IProp GF) =>
      saved_pred_own (GF := GF) gn (DFrac.own (1 : Qp).half) P) Hlookup).1 $$ Hfrags
    with ⟨Hpred_p, Hfrags_rest⟩
  ihave Hag := saved_pred_agree gn_f _ _ P contract_f v_rcv $$ Hpred_p Hpred_f
  imod lc_fupd_elim_later $$ Hlc Hag with #Hag
  ihave HPv := internal_eq_rewrite_wand $$ Hag Hcontract_v
  imod auth_set_dealloc _ _ _ $$ [Hauth Hfrag_f] with Hauth
  · iframe
  have Hcons : pending.Perm (P :: (map_to_list (gmap.delete gn_f pending_map)).map Prod.snd) :=
    Hperm.symm.trans (map_to_list_snd_delete _ _ _ Hlookup)
  obtain ⟨pre, post, Hsplit, Hrest_perm⟩ := Permutation_cons_split _ _ _ Hcons
  imodintro
  iexists P, pre, post
  iframe HPv
  isplitl []
  · ipureintro; exact Hsplit
  iexists (gmap.delete gn_f pending_map)
  rw [gmap.dom_delete_L]
  isplitl [Hauth]
  · iexact Hauth
  isplitl []
  · ipureintro; exact Hrest_perm
  · iexact Hfrags_rest

/-- The core receive lemma. Each receive:
1. pulls a `Fulfilled γ v` from the channel invariant,
2. uses saved predicate agreement to identify which contract was fulfilled,
3. removes the matched contract from `pending`,
4. returns `P v` directly to the caller. -/
theorem future_await_au (γ : future_names) (ch : loc) (pending : List (V → IProp GF))
    (Φ : V → Bool → IProp GF) :
    ⊢ is_future V γ ch -∗ £ 1 ∗ £ 1 ∗ £ 1 ∗ Await γ pending -∗
      ▷ (∀ (v : V) (P : V → IProp GF) (pre post : List (V → IProp GF)),
          ⌜pending = pre ++ P :: post⌝ -∗ P v -∗ Await γ (pre ++ post) -∗ Φ v true) -∗
      recv_au γ.chan_name V Φ := by
  unfold is_future recv_au
  iintro ⟨#Hisch, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3, HAwait⟩ Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold future_inv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v_rcv, msgs'⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.cons =>
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HF, Hi⟩
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered msgs'; iframe
    imod future_match _ _ _ $$ Hlc3 HF HAwait with ⟨%P, %pre, %post, %Hsplit, HP, HAwait⟩
    imodintro
    iapply Hau $$ %v_rcv %P %pre %post %Hsplit HP HAwait
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvPending; iframe
    imodintro
    unfold recv_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hoc1, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc1
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .Idle; iframe
      imod future_match _ _ _ $$ Hlc3 Hi HAwait with ⟨%P, %pre, %post, %Hsplit, HP, HAwait⟩
      imodintro
      iapply Hau $$ %v %P %pre %post %Hsplit HP HAwait
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imod future_match _ _ _ $$ Hlc3 Hi HAwait with ⟨%P, %pre, %post, %Hsplit, HP, HAwait⟩
    imodintro
    iapply Hau $$ %v %P %pre %post %Hsplit HP HAwait
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_future_await (γ : future_names) (ch : loc) (pending : List (V → IProp GF)) :
    {{ is_future V γ ch ∗ Await γ pending }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (P : V → IProp GF) (pre post : List (V → IProp GF)), RET (PairV #v #true);
        ⌜pending = pre ++ P :: post⌝ ∗ P v ∗ Await γ (pre ++ post) }} := by
  iintro %Φ ⟨#Hmf, HAwait⟩ HΦ
  ihave #Hch : is_chan ch γ.chan_name V $$ [Hmf]
  · unfold is_future; icases Hmf with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chan_name $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply future_await_au γ ch pending (fun v ok => Φ (PairV #v #ok)) $$ Hmf
    [$Hlc1 $Hlc2 $Hlc3 $HAwait]
  inext
  iintro %v %P %pre %post %Hsplit HP HAwait
  iapply HΦ
  iframe
  ipureintro
  exact Hsplit

end future

end Perennial
