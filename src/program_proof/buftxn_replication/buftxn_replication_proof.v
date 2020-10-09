From Perennial.algebra Require Import liftable liftable2.

From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof.
From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn buftxn_replication.
From Perennial.program_proof Require Import buftxn.buftxn_proof buftxn.idealized_buftxn_spec.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice crash_lock.
From Perennial.goose_lang.ffi Require Import disk_prelude.

Section goose_lang.
  Context `{!buftxnG Σ}.

  Context (N:namespace).
  Context (P: Block → iProp Σ).

  Implicit Types (l:loc) (σ:Block) (a:addr).

  Local Definition txnN := N .@ "txn".
  Local Definition lockN := N .@ "lock".

  Definition rb_rep a0 a1 σ (mapsto: addr → object → iProp Σ) : iProp Σ :=
    "Ha0" ∷ mapsto a0 (existT _ (bufBlock σ)) ∗
    "Ha1" ∷ mapsto a1 (existT _ (bufBlock σ)) ∗
    (* NOTE(tej): it would be easy enough to make rb_rep's non-map part
    persistent (actually empty) if we didn't put this in the predicate but
    instead factored it out (and repeated it in the linv and cinv) *)
    "HP" ∷ P σ.

  Global Instance rb_rep_liftable a0 a1 σ : Liftable (rb_rep a0 a1 σ).
  Proof. apply _. Qed.

  Definition rb_linv l γ: iProp Σ :=
    ∃ a0 a1 σ i,
      "a0" ∷ l ↦[RepBlock.S :: "a0"] (addr2val a0) ∗
      "a1" ∷ l ↦[RepBlock.S :: "a1"] (addr2val a1) ∗
      "#rb_durable" ∷ txn_durable γ i ∗
      "rb_rep" ∷ rb_rep a0 a1 σ
                   (λ a v, modify_token γ a v ∗
                           ephemeral_val_from γ.(buftxn_async_name) i a v).

  Definition rb_cinv a0 a1 l γ: iProp Σ :=
    ∃ σ i, rb_rep a0 a1 σ (ephemeral_val_from γ.(buftxn_async_name) i) ∗
           txn_durable γ i.

  Definition is_rep_block l: iProp Σ :=
    ∃ γ (txn_l m_l: loc),
    "#txn" ∷ readonly (l ↦[RepBlock.S :: "txn"] #txn_l) ∗
    "#m" ∷ readonly (l ↦[RepBlock.S :: "m"] #m_l) ∗
    (* TODO: make this a crash lock with cinv *)
    "#His_lock" ∷ is_lock lockN #m_l (rb_linv l γ) ∗
    "#Htxn" ∷ is_txn_system txnN txn_l γ.

  Theorem wp_RepBlock__Read l Q :
    {{{ "#Hrb" ∷ is_rep_block l ∗
        "Hfupd" ∷ (∀ σ, P σ ={⊤}=∗ P σ ∗ Q σ)
    }}}
      RepBlock__Read #l
    {{{ s σ, RET slice_val s; is_slice s u8T 1 σ ∗ Q σ }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wp_call.
    wp_loadField.
    wp_apply (lock.acquire_spec with "His_lock").
    iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_pures.
    wp_loadField.
    (* TODO: oops, forgot to prove a wp for Begin *)
  Abort.

End goose_lang.
