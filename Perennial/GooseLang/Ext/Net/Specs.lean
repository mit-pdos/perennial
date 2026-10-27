/-
Iris reasoning principles for the network extension.

Notes:
* The global ghost state is a `genHeapGS` from addresses to message sets:
  `a n↦{q} ms` says that the messages sent to the address `a` are `ms`. The
  local ghost state is the node's address (`netAddr`), with no camera: the
  local interpretation says that the node's address is `netAddr`.
* The specs hold for any program whose extensions include the network
  (`HasExt netExt`), with an injective encoding of strings as values (as the Go
  model's `go.BasicIntoValInj` has). Both are logically atomic, so that the
  messages' points-to can come from an invariant shared by the nodes.
-/
module

public import Iris.BI.Lib.GenHeap
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Ext.Net.Impl
public import Perennial.GooseLang.Ext.GenHeap
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost state -/

class NetGpreS (GF : BundledGFunctors) where
  netPreGHeapG : genHeapPreS GoString (GSet NetMsg) GF (GMap GoString)

class NetGS (GF : BundledGFunctors) where
  netHeapG : genHeapGS GoString (GSet NetMsg) GF (GMap GoString)

/-- The local ghost state of the network: the node's address. -/
structure NetNodeGS (GF : BundledGFunctors) where
  addr : GoString

section net
variable {GF : BundledGFunctors}

/-- The interpretation of the network. -/
def netCtx (hG : NetGS GF) (n : NetState) : IProp GF :=
  genHeapInterp (G := hG.netHeapG) n

/-- The messages sent to the address `a` are `ms`. -/
def netPointsto (hG : NetGS GF) (a : GoString) (q : DFrac) (ms : GSet NetMsg) : IProp GF :=
  pointsTo (G := hG.netHeapG) a q ms

instance netPointsto_timeless (hG : NetGS GF) (a : GoString) (q : DFrac) (ms : GSet NetMsg) :
    Timeless (netPointsto hG a q ms) := by
  unfold netPointsto; infer_instance

theorem net_global_init (hPre : NetGpreS GF) (n : NetState) :
    ⊢@{IProp GF} |==> ∃ hG : NetGS GF, netCtx hG n ∗
      [∗map] a ↦ ms ∈ n, netPointsto hG a (.own 1) ms := by
  letI := hPre.netPreGHeapG
  imod genHeap_init (H := GMap GoString) n with ⟨%names, H1, H2, -⟩
  imodintro
  iexists (⟨names⟩ : NetGS GF)
  isplitl [H1]
  · unfold netCtx; iexact H1
  · unfold netPointsto; iexact H2

end net

/-- The ghost state of the network. The program gets the ownership of the
initial network, and each node the knowledge of its address. -/
instance net_interp : ExtInterp netExt where
  LocalGS := NetNodeGS
  GlobalGS := NetGS
  localCtx hL me := iprop(⌜me = hL.addr⌝)
  globalCtx := netCtx
  PreG := NetGpreS
  initgP _ := True
  initP _ _ := True
  globalStart hG n := iprop([∗map] a ↦ ms ∈ n, netPointsto hG a (.own 1) ms)
  localStart hL me := iprop(⌜hL.addr = me⌝)
  global_init _ hPre n _ := net_global_init hPre n
  local_init _ _ me _ _ := by
    iapply bupd_intro
    iexists (⟨me⟩ : NetNodeGS _)
    isplitl [] <;> ipureintro <;> rfl

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseNetGS : NetGS GF := extGlobalGS netExt

/-- The address of the node. -/
abbrev netAddr : GoString := (extLocalGS netExt (L := L) : NetNodeGS GF).addr

/- Notations `a n↦{q} ms` and `a n↦ ms`. -/
namespace net_ext
scoped notation:50 a:51 " n↦{" q "} " ms:50 => netPointsto gooseNetGS a q ms
scoped notation:50 a:51 " n↦ " ms:50 => netPointsto gooseNetGS a (DFrac.own 1) ms
end net_ext
open net_ext

theorem net_local_ctx_eq (me : GoString) :
    ExtInterp.localCtx (E := netExt) (extLocalGS netExt (L := L) (GF := GF)) me ⊣⊢
      iprop(⌜me = netAddr (L := L) (GF := GF)⌝) := .rfl

theorem net_global_ctx_eq (n : NetState) :
    ExtInterp.globalCtx (E := netExt) (extGlobalGS netExt) n ⊣⊢
      genHeapInterp (G := (gooseNetGS (G := G)).netHeapG) n := .rfl

/-- `Send(to, data)`, logically atomic: the message `(netAddr, data)` joins the
messages of `to`. -/
theorem wp_NetSend_atomic (to : GoString) (data : List w8) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ ms : GSet NetMsg, to n↦ ms ∗
      (to n↦ (ms ∪ {[⟨netAddr (L := L), data⟩]}) ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp netExt.name "Send" (Val (PairV (#to) (#data)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep "Send" (PairV (#to) (#data)) Φ (by simp [val.isPanic])
  iintro %h %me %n Hheap Hl Hg
  imod HAU with ⟨%ms, Hc, Hclose⟩
  icases (net_local_ctx_eq me).mp $$ Hl with %Hme
  icases (net_global_ctx_eq n).mp $$ Hg with Hg
  unfold netPointsto
  icases genHeap_lookup (G := (gooseNetGS (G := G)).netHeapG) $$ Hg Hc with %Heq
  change n !! to = some ms at Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, me, _, rfl, rfl, to, data, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %me' %n' %Hst _
  obtain ⟨rfl, rfl, to', data', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hto, Hdata⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj Hto
  obtain rfl := go.intoVal_inj (V := List w8) Hdata
  have Hmsgs : n.msgs to = ms := by simp [NetState.msgs, Heq]
  rw [Hmsgs, Hme]
  imod genHeap_update' (G := (gooseNetGS (G := G)).netHeapG)
    (v₂ := ms ∪ {[⟨netAddr (L := L), data⟩]}) $$ [Hg Hc] with ⟨Hg, Hc⟩
  · iframe
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hheap
  isplitr
  · iapply (net_local_ctx_eq _).mpr; ipureintro; rfl
  isplitl [Hg]
  · iapply (net_global_ctx_eq _).mpr; iexact Hg
  iapply wp_value'
  iexact HΦ

/-- `Recv()`, logically atomic: some message `m` sent to the node's address,
returned as `(m.sender, m.data)`. The update is used only when the receive
returns (the step at which it waits use nothing). -/
theorem wp_NetRecv_atomic (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ (q : DFrac) (ms : GSet NetMsg), netAddr (L := L) n↦{q} ms ∗
      ∀ m, ⌜m ∈ ms⌝ -∗ netAddr (L := L) n↦{q} ms ={∅,E}=∗
        Φ (PairV (#m.sender) (#m.data)))
    ⊢ WP (ExternalOp netExt.name "Recv" (Val (#()))) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro HAU
  iapply wp_extStep "Recv" (#()) Φ (by simp)
  iintro %h %me %n Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, me, n, rfl, rfl, rfl, rfl, .inl rfl⟩
  inext
  iintro %e' %h' %me' %n' %Hst _
  obtain ⟨rfl, rfl, -, rfl, Hcase⟩ := Hst
  imod Hclose
  rcases Hcase with rfl | ⟨m, Hm, rfl⟩
  · -- the receive waits
    imodintro
    iframe Hheap Hl Hg
    iapply IH
    iexact HAU
  · -- the receive returns `m`
    imod HAU with ⟨%q, %ms, Hc, Hclose⟩
    icases (net_local_ctx_eq _).mp $$ Hl with %Hme
    icases (net_global_ctx_eq _).mp $$ Hg with Hg
    unfold netPointsto
    icases genHeap_lookup (G := (gooseNetGS (G := G)).netHeapG) $$ Hg Hc with %Heq
    change _ !! netAddr (L := L) = some ms at Heq
    have Hm' : m ∈ ms := by
      rw [Hme] at Hm
      simpa [NetState.msgs, Heq] using Hm
    imod Hclose $$ %m %Hm' Hc with HΦ
    imodintro
    iframe Hheap
    isplitr
    · iapply (net_local_ctx_eq _).mpr; ipureintro; exact Hme
    isplitl [Hg]
    · iapply (net_global_ctx_eq _).mpr; iexact Hg
    iapply wp_value'
    iexact HΦ

end lifting

end Perennial
