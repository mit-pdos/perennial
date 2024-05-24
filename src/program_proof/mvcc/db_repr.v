From Perennial.program_proof.mvcc Require Import txn_prelude txnsite_repr.
From Perennial.program_proof.mvcc Require Import index_proof.

Section repr.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*@ type DB struct {                                                        @*)
(*@     // Mutex protecting @sid.                                           @*)
(*@     latch *cfmutex.CFMutex                                              @*)
(*@     // Next site ID to assign.                                          @*)
(*@     sid   uint64                                                        @*)
(*@     // All transaction sites.                                           @*)
(*@     sites []*txnsite.TxnSite                                            @*)
(*@     // Index.                                                           @*)
(*@     idx   *index.Index                                                  @*)
(*@     // Global prophecy variable (for verification purpose).             @*)
(*@     proph machine.ProphId                                               @*)
(*@ }                                                                       @*)
Definition own_db (db : loc) : iProp Σ := 
  ∃ (sidcur : u64),
    "Hsidcur" ∷ db ↦[DB :: "sid"] #sidcur ∗
    "%HsidcurB" ∷ ⌜(uint.Z sidcur) < N_TXN_SITES⌝ ∗
    "_" ∷ True.

Definition is_db (db : loc) γ : iProp Σ := 
  ∃ (latch : loc) (sites : Slice.t) (idx : loc)
    (sitesL : list loc) (p : proph_id),
    "#Hlatch" ∷ readonly (db ↦[DB :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_db db) ∗
    "#Hidx" ∷ readonly (db ↦[DB :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Hsites" ∷ readonly (db ↦[DB :: "sites"] (to_val sites)) ∗
    "#HsitesS" ∷ readonly (own_slice_small sites ptrT (DfracOwn 1) (to_val <$> sitesL)) ∗
    "%HsitesLen" ∷ ⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝ ∗
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ sitesL, is_txnsite site sid γ) ∗
    "#Hp" ∷ readonly (db ↦[DB :: "proph"] #p) ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinvsst" ∷ mvcc_inv_sst γ p.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_db _)) => unfold own_db : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (is_db _ _)) => unfold is_db : core.
