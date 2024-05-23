From Perennial.program_proof.mvcc Require Import txnsite_prelude tid_proof.
From Goose.github_com.mit_pdos.vmvcc Require Export txnsite.

Section repr.
  Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*@ type TxnSite struct {                                                   @*)
(*@     latch   *cfmutex.CFMutex                                            @*)
(*@     sid     uint64                                                      @*)
(*@     tids    []uint64                                                    @*)
(*@     // TODO: should only need 3 for padding                             @*)
(*@     padding [4]uint64                                                   @*)
(*@ }                                                                       @*)
Definition own_txnsite (txnsite : loc) (sid : u64) γ : iProp Σ :=
  ∃ (tidsactive : Slice.t) (tidsactiveL : list u64) (tidsactiveM : gset nat),
    "Htids" ∷ txnsite ↦[TxnSite :: "tids"] (to_val tidsactive) ∗
    "Hsid" ∷ txnsite ↦[TxnSite :: "sid"] #sid ∗
    "HactiveL" ∷ typed_slice.own_slice tidsactive uint64T (DfracOwn 1) tidsactiveL ∗
    "HactiveAuth" ∷ site_active_tids_half_auth γ sid tidsactiveM ∗
    "%HactiveLM" ∷ ⌜list_to_set ((λ tid, uint.nat tid) <$> tidsactiveL) = tidsactiveM⌝ ∗
    "%HactiveND" ∷ ⌜NoDup tidsactiveL⌝ ∗
    "Hsidtok" ∷ sid_own γ sid.

Definition is_txnsite (site : loc) (sid : u64) γ : iProp Σ :=
  ∃ (latch : loc) (proph : proph_id),
    "#Hlatch" ∷ readonly (site ↦[TxnSite :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnsite site sid γ) ∗
    "#Hinvtid" ∷ have_gentid γ ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinvsst" ∷ mvcc_inv_sst γ proph ∗
    "%HsidBounded" ∷ ⌜(uint.Z sid) < N_TXN_SITES⌝.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_txnsite _ _ _)) => unfold own_txnsite : core.
