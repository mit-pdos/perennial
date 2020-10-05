From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import async_inode.

(* TODO: alloc_crash_proof must be imported early since otherwise it messes up a
bunch of things, like Z_scope, encode, and val *)
From Perennial.algebra Require Import own_discrete.
From Perennial.program_proof.examples Require Import alloc_crash_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import into_val typed_slice.

From Perennial.program_proof Require Import marshal_block disk_lib.

Definition InodeMaxBlocks: Z := 511.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Module inode.
  Record t :=
    mk { (* addresses consumed by this inode *)
         addrs: gset u64;
         durable_blocks: list Block;
         buffered_blocks: list Block;
      }.
  Global Instance _eta: Settable _ := settable! mk <addrs; durable_blocks; buffered_blocks>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := (length σ.(durable_blocks) + length σ.(buffered_blocks))%nat ≤ InodeMaxBlocks.
  Definition size σ : nat := (length σ.(durable_blocks) + length σ.(buffered_blocks))%nat.
End inode.

Hint Unfold inode.wf InodeMaxBlocks : word.

Section goose.
Context `{!heapG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

(* The client picks the namespaces that we use for everything. *)
Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t) (addr: u64).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_inode_durable addr σ (addrs: list u64) : iProp Σ :=
  ∃ (hdr: Block),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hencoded" ∷ ⌜block_encodes hdr ([EncUInt64 (length addrs)] ++ (EncUInt64 <$> addrs))⌝ ∗
    "%Haddrs_set" ∷ ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
    "Hhdr" ∷ int.val addr d↦ hdr ∗
    "Hdata" ∷ [∗ list] a;b ∈ addrs;σ.(inode.durable_blocks), int.val a d↦ b
.
Local Hint Extern 1 (environments.envs_entails _ (is_inode_durable _ _ _)) => unfold is_inode_durable : core.

Theorem is_inode_durable_read addr σ addrs :
  is_inode_durable addr σ addrs -∗
    ∃ hdr,
      "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
      "%Hencoded" ∷ ⌜block_encodes hdr ([EncUInt64 (length addrs)] ++ (EncUInt64 <$> addrs))⌝ ∗
      "%Haddrs_set" ∷ ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
      "Hhdr" ∷ int.val addr d↦ hdr ∗
      "Hdata" ∷ ([∗ list] a;b ∈ addrs;σ.(inode.durable_blocks), int.val a d↦ b) ∗
      "Hdurable" ∷ □(int.val addr d↦ hdr -∗
                    ([∗ list] a;b ∈ addrs;σ.(inode.durable_blocks), int.val a d↦ b) -∗
                   is_inode_durable addr σ addrs).
Proof.
  iNamed 1.
  iExists _; iFrame "∗ %".
  iIntros "!> Hhdr Hdata".
  iExists _; iFrame "∗ %".
Qed.

(* XXX: from append_log_example but maybe this just needs to be defined in some kind of disk.v prelude *)
Definition blocks_slice (bk_s: Slice.t) (bks: list Slice.t) (bs: list Block): iProp Σ :=
  ∃ q, is_slice bk_s (slice.T byteT) 1 bks ∗
   [∗ list] _ ↦ b_s;b ∈ bks;bs , is_block b_s q b.

Lemma blocks_slice_length bk_s bks bs :
  blocks_slice bk_s bks bs -∗ ⌜length bks = length bs⌝.
Proof.
  iDestruct 1 as (?) "(_&Hslices)".
  iDestruct (big_sepL2_length with "Hslices") as "%".
  auto.
Qed.

Lemma blocks_slice_length' bk_s bks bs :
  blocks_slice bk_s bks bs -∗ ⌜length bks = int.nat bk_s.(Slice.sz)⌝.
Proof.
  iDestruct 1 as (?) "(Hs&_)".
  iDestruct (is_slice_sz with "Hs") as "%".
  eauto.
Qed.

Definition inode_linv (l:loc) (addr:u64) σ : iProp Σ :=
  ∃ (addr_s: Slice.t) (buffered_s: Slice.t) bks (addrs: list u64),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "Hdurable" ∷ is_inode_durable addr σ addrs ∗
    "buffered" ∷ l ↦[Inode.S :: "buffered"] (slice_val buffered_s) ∗
    "Hbuffered" ∷ blocks_slice buffered_s bks σ.(inode.buffered_blocks) ∗
    "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
    "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
.
Local Hint Extern 1 (environments.envs_entails _ (inode_linv _ _ _)) => unfold inode_linv : core.

Definition inode_cinv addr σ: iProp Σ :=
  ∃ addrs, is_inode_durable addr σ addrs.
Local Hint Extern 1 (environments.envs_entails _ (inode_cinv _ _)) => unfold inode_cinv : core.

Existing Instance persistent_discretizable.
Instance inode_cinv_discretizable addr σ:
  Discretizable (inode_cinv addr σ).
Proof. apply _. Qed.

Instance into_disc_inode_linv l addr σ:
  IntoDiscrete (inode_linv l addr σ) (inode_cinv addr σ).
Proof. rewrite /IntoDiscrete. iIntros "H". iNamed "H". iModIntro. iExists _; eauto. Qed.

Definition inode_state l (d_ref: loc) (lref: loc) addr : iProp Σ :=
  "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d_ref) ∗
  "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
  "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr).

Definition is_inode l k P (addr: u64) : iProp Σ :=
  ∃ (d_ref:loc) (lref: loc),
    "Hro_state" ∷ inode_state l d_ref lref addr ∗
    "#Hlock" ∷ is_crash_lock inodeN k #lref
              (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ)
              (∃ σ, "Hlockcinv" ∷ inode_cinv addr σ ∗ "HP" ∷ P σ).

Definition pre_inode l addr σ : iProp Σ :=
  ∃ (d_ref:loc) (lref: loc),
    "Hro_state" ∷ inode_state l d_ref lref addr ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hlockinv" ∷ inode_linv l addr σ.

Global Instance into_disc_pre_inode l addr σ :
  IntoDiscrete (pre_inode l addr σ) (inode_cinv addr σ).
Proof. rewrite /IntoDiscrete. iNamed 1. iModIntro. iFrame. Qed.

Global Instance is_inode_crash l addr σ :
  IntoCrash (inode_linv l addr σ) (λ _, ∃ addrs, is_inode_durable addr σ addrs)%I.
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iExists addrs.
  iFrame.
  auto.
Qed.

Theorem inode_linv_to_cinv l addr σ :
  inode_linv l addr σ -∗ inode_cinv addr σ.
Proof.
  iNamed 1.
  iExists _; iFrame.
Qed.

Theorem pre_inode_to_cinv l addr σ :
  pre_inode l addr σ -∗ inode_cinv addr σ.
Proof.
  iNamed 1.
  iApply inode_linv_to_cinv; iFrame.
Qed.

Global Instance is_inode_Persistent l k P addr :
  Persistent (is_inode l k P addr).
Proof. apply _. Qed.

(* TODO: these are copied from the circ proof *)

Definition block0: Block :=
  list_to_vec (replicate (Z.to_nat 4096) (U8 0)).

Lemma replicate_zero_to_block0 :
  replicate (int.nat 4096) (zero_val byteT) =
  Block_to_vals block0.
Proof.
  change (zero_val byteT) with #(U8 0).
  change (int.nat 4096) with (Z.to_nat 4096).
  rewrite /Block_to_vals /block0.
  reflexivity.
Qed.

(* to initialize the system, we use this theorem to turn a zero block into a
valid post-crash inode state, which we can then recover with the usual [Open]
recovery procedure. *)
Theorem init_inode addr :
  int.val addr d↦ block0 -∗ inode_cinv addr (inode.mk ∅ [] []).
Proof.
  iIntros "Hhdr".
  iExists [], block0.
  cbv [inode.durable_blocks big_sepL2].
  iFrame "Hhdr".
  iPureIntro.
  split_and!.
  - rewrite /inode.wf /=.
    cbv; congruence.
  - reflexivity.
  - reflexivity.
Qed.

Theorem is_inode_alloc {k} l P addr σ :
  ▷ P σ -∗
  pre_inode l addr σ ={⊤}=∗
  is_inode l (S k) P addr ∗
  <disc> |C={⊤}_(S k)=> (∃ σ', inode_cinv addr σ' ∗ P σ').
   (* Crash condition has [P] without extra ▷ because [alloc_crash_lock] strips that later for us. *)
Proof.
  iIntros "HP Hinode"; iNamed "Hinode".
  iMod (alloc_crash_lock_cfupd inodeN k
                           (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ)%I
                           (∃ σ, "Hlockcinv" ∷ inode_cinv addr σ ∗ "HP" ∷ P σ)%I
            with "Hfree_lock [] [Hlockinv HP]") as "[His_lock $]".
  { iIntros "!> Hlock"; iNamed "Hlock".
    iExists _; iFrame.
    iApply inode_linv_to_cinv; auto. }
  { eauto with iFrame. }
  iFrame.
  iModIntro.
  iExists _, _; iFrame.
Qed.

Lemma wf_clear_buffered σ :
  inode.wf σ →
  inode.wf (set inode.buffered_blocks (λ _ : list Block, []) σ).
Proof. rewrite /inode.wf //=. lia. Qed.

Local Hint Resolve wf_clear_buffered : core.

Theorem wpc_Open k {d:loc} {addr σ} :
  {{{ inode_cinv addr σ }}}
    async_inode.Open #d #addr @ NotStuck; k; ⊤
  {{{ l, RET #l; pre_inode l addr (set inode.buffered_blocks (λ _, []) σ) }}}
  {{{ inode_cinv addr σ }}}.
Proof.
  iIntros (Φ Φc) "Hinode HΦ"; iNamed "Hinode".
  iAssert (□ (int.val addr d↦ hdr ∗
              ([∗ list] a;b ∈ addrs;σ.(inode.durable_blocks), int.val a d↦ b) -∗
              inode_cinv addr σ))%I as "#Hinode".
  { iIntros "!> (?&?)". eauto 10 with iFrame. }
  iDestruct (big_sepL2_length with "Hdata") as %Hblocklen.
  rewrite /Open.
  wpc_pures.
  { iLeft in "HΦ". iModIntro. iNext. iApply "HΦ". iApply ("Hinode" with "[$]"). }
  iCache with "HΦ Hhdr Hdata".
  { crash_case. iApply ("Hinode" with "[$]"). }
  wpc_pures.
  wpc_apply (wpc_Read with "Hhdr").
  iSplit; [ | iNext ].
  { iLeft in "HΦ". iModIntro. iNext. iIntros "Hhdr". iApply "HΦ". iApply ("Hinode" with "[$]"). }
  iIntros (s) "(Hhdr&Hs)".
  wpc_frame.
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  wp_apply (wp_new_dec with "Hs"); first eauto.
  iIntros (dec) "Hdec".
  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ addrs [] with "[Hdec]").
  { rewrite Hblocklen. word. }
  { rewrite app_nil_r; iFrame. }
  iIntros (addr_s) "[_ Haddrs]".
  wp_pures.
  rewrite -wp_fupd.
  wp_apply wp_new_free_lock.
  iIntros (lref) "Hlock".
  replace (slice.nil) with (slice_val (Slice.nil)); auto.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "inode".
  iDestruct (struct_fields_split with "inode") as "(d&m&addr&addrs&buffered&_)".
  iMod (readonly_alloc_1 with "d") as "#d".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "addr") as "#addr".
  iModIntro.
  iNamed 1.
  iApply "HΦ".
  iExists _, _; iFrame.
  iSplitR.
  { iFrame "#". }
  iExists _, (Slice.nil), [], addrs. iFrame "% ∗".
  iSplitL "".
  { eauto. }
  iSplitR ""; last first.
  { rewrite /blocks_slice.
    iExists 1%Qp. rewrite big_sepL2_nil. rewrite right_id.
    by iApply is_slice_nil. }
  iExists _. iFrame "% ∗".
  iPureIntro; eauto.
Qed.

Theorem is_inode_durable_addrs addr σ addrs :
  is_inode_durable addr σ addrs -∗
  ⌜list_to_set addrs = σ.(inode.addrs)⌝.
Proof.
  iNamed 1.
  iFrame "%".
Qed.

Theorem is_inode_durable_size addr σ addrs :
  is_inode_durable addr σ addrs -∗ ⌜length addrs = length σ.(inode.durable_blocks)⌝.
Proof.
  iNamed 1.
  iDestruct (big_sepL2_length with "Hdata") as "$".
Qed.

Definition used_blocks_pre l σ addrs: iProp Σ :=
  ∃ addr_s,
    "%Haddr_set" ∷ ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
    "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
    "Haddrs" ∷ is_slice addr_s uint64T 1 addrs.

(* this lets the caller frame out the durable state for the crash invariant and
the memory state for UsedBlocks *)
Theorem pre_inode_read_addrs l addr σ :
  pre_inode l addr σ -∗
  ∃ addrs, used_blocks_pre l σ addrs ∗
           is_inode_durable addr σ addrs ∗
           (used_blocks_pre l σ addrs -∗
            is_inode_durable addr σ addrs -∗
            pre_inode l addr σ).
Proof.
  iNamed 1.
  iNamed "Hlockinv".
  iDestruct (is_inode_durable_addrs with "Hdurable") as "%Haddr_set".
  iExists addrs.
  iSplitL "addrs Haddrs".
  { iExists _; iFrame "% ∗". }
  iFrame.
  iNamed 1.
  iIntros "Hdurable".
  iExists _, _; iFrame.
  iExists _, _, _, _; iFrame "∗ %".
Qed.

Theorem wp_Inode__UsedBlocks {l σ addrs} :
  {{{ used_blocks_pre l σ addrs }}}
    Inode__UsedBlocks #l
  {{{ (s:Slice.t), RET (slice_val s);
      is_slice s uint64T 1 addrs ∗
      ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
      (is_slice s uint64T 1 addrs -∗ used_blocks_pre l σ addrs) }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  iApply "HΦ".
  iFrame "∗ %".
  iIntros "Haddrs".
  iExists _; iFrame.
Qed.

Theorem wpc_Inode__UsedBlocks {k} {l σ addr} :
  {{{ pre_inode l addr σ  }}}
    Inode__UsedBlocks #l @ NotStuck; k; ⊤
  {{{ (s:Slice.t) (addrs: list u64), RET (slice_val s);
      is_slice s uint64T 1 addrs ∗
      ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
      (is_slice s uint64T 1 addrs -∗ pre_inode l addr σ) ∧ inode_cinv addr σ }}}
  {{{ inode_cinv addr σ }}}.
Proof.
  iIntros (Φ Φc) "Hinode HΦ"; iNamed "Hinode".
  (* TODO: wpc_call is broken here (maybe because the only redex is an App) *)
  rewrite /Inode__UsedBlocks.
  wpc_pures.
  { iLeft in "HΦ". iModIntro. iNext. by iApply "HΦ". }
  iNamed "Hlockinv".
  wpc_frame "HΦ Hdurable".
  { crash_case.
    iExists _; iFrame. }
  wp_loadField.
  iNamed 1.
  iApply "HΦ".
  iFrame "Haddrs".
  iDestruct (is_inode_durable_addrs with "Hdurable") as "%Haddr_set".
  iSplitR; first auto.
  iSplit.
  - iIntros "Haddrs".
    iExists _, _; iFrame.
    iExists _, _, _, _; iFrame "∗ %".
  - iExists _; eauto.
Qed.

Theorem wpc_Inode__Read {k} {l k' P addr} {off: u64} :
  (S k < k')%nat →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (S k') P addr ∗
      "Hfupd" ∷ (<disc> ▷ Φc ∧ ▷ ∀ σ mb,
        ⌜mb = (σ.(inode.durable_blocks) ++ σ.(inode.buffered_blocks)) !! int.nat off⌝ ∗
        ▷ P σ -∗ |NC={⊤}=> ▷ P σ ∗ (<disc> ▷ Φc ∧ ∀ s,
          match mb with Some b => (∃ q, is_block s q b) | None => ⌜s = Slice.nil⌝ end -∗ Φ (slice_val s))) -∗
    WPC Inode__Read #l #off @ NotStuck; (S k); ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  wpc_call.
  { by iLeft in "Hfupd". }
  { by iLeft in "Hfupd". }
  iCache with "Hfupd".
  { by iLeft in "Hfupd". }
  wpc_pures.
  wpc_bind_seq.
  wpc_frame.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); first by set_solver.
  iIntros "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  (* XXX: todo, iNamed needs to be better about later *)
  iIntros "H". iDestruct "H" as (?) "(>H1&HP)". iNamed "H1".
  iEval (rewrite /named) in "HP".
  iMod (fupd_later_to_disc with "HP") as "HP".

  iCache with "Hfupd Hlockinv HP".
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. }
  wpc_call.
  wpc_bind (_ ≥ _)%E.
  iNamed "Hlockinv".
  iCache with "Hfupd HP Hdurable".
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
  iDestruct (is_inode_durable_size with "Hdurable") as %Hlen1.
  wpc_frame.
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen2.
  autorewrite with len in Hlen2.
  wp_apply wp_slice_len.
  iDestruct (blocks_slice_length with "Hbuffered") as %Hlen3.
  iDestruct (blocks_slice_length' with "Hbuffered") as %Hlen4.
  iDestruct "Hbuffered" as (q) "(Hbuffered&His_blocks)".
  wp_loadField.
  iDestruct (is_slice_sz with "Hbuffered") as %Hlen5.
  autorewrite with len in Hlen3.
  wp_apply wp_slice_len.
  wp_pures.
  iNamed 1.
  wpc_if_destruct.
  -
    iApply ncfupd_wpc.
    iSplit.
    { iLeft in "Hfupd". iModIntro. iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
    iRight in "Hfupd".
    iMod (own_disc_fupd_elim with "HP") as "HP".
    iMod ("Hfupd" $! σ None with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      rewrite lookup_ge_None_2 //.
      rewrite app_length.
      (* XXX show that this sum doesn't overflow *)
      assert (int.val (word.add addr_s.(Slice.sz) buffered_s.(Slice.sz)) =
              int.val (addr_s.(Slice.sz)) + int.val (buffered_s.(Slice.sz))) as Heq.
      { admit. }
      word.
    }
    iMod (fupd_later_to_disc with "HP") as "HP".
    iApply wpc_fupd. iModIntro.
    wpc_pures.
    { iLeft in "HQ". iModIntro. iFrame "HQ". eauto 10 with iFrame. }
    iMod (own_disc_fupd_elim with "HP") as "HP".
    iModIntro.
    iSplitR "HP addrs Haddrs Hdurable buffered His_blocks Hbuffered"; last first.
    { iNext. iExists _. iFrame. eauto 10 with iFrame. }
    iIntros "His_locked".
    iSplit; first by iLeft in "HQ". (* TODO(Ralf): can we avoid this double-proof? *)
    iCache with "HQ"; first by iLeft in "HQ".
    wpc_pures.
    wpc_frame "HQ".
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    wp_pures.
    iNamed 1.
    iRight in "HQ".
    change slice.nil with (slice_val Slice.nil).
    iApply "HQ"; iFrame.
    auto.
  -
    iDestruct (is_slice_split with "Haddrs") as "[Haddrs_small Haddrs]".
    wpc_pures.
    wpc_bind (_ > _)%E.
    wpc_frame.
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.
    iNamed 1.
    wpc_if_destruct.
    * wpc_pures.
      wpc_frame_seq.
      destruct (list_lookup_lt _ addrs (int.nat off)) as [addr' Hlookup].
      { word. }
      wp_loadField.
      wp_apply (wp_SliceGet _ _ _ _ _ addrs with "[$Haddrs_small //]").
      iIntros "Haddrs_small"; iNamed 1.
      wpc_pures.
      iApply ncfupd_wpc. iSplit.
      { iLeft in "Hfupd". iModIntro. iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
      iDestruct (is_inode_durable_read with "Hdurable") as "H"; iNamed "H".
      iDestruct (big_sepL2_lookup_1_some with "Hdata") as "%Hblock_lookup"; eauto.
      destruct Hblock_lookup as [b0 Hlookup2].
      iDestruct (is_slice_split with "[$Haddrs_small $Haddrs]") as "Haddrs".
      iDestruct (big_sepL2_lookup_acc_disc with "Hdata") as "[Hb Hdata]"; eauto.
      iRight in "Hfupd".
      iMod (own_disc_fupd_elim with "HP") as "HP".
      iMod ("Hfupd" $! σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      iMod (fupd_later_to_disc with "HP") as "HP".
      iApply wpc_fupd. iModIntro.
      wpc_apply (wpc_Read with "Hb").
      iSplit.
      { iLeft in "HQ". iModIntro. iNext. iIntros "Hda".
        iSpecialize ("Hdata" with "Hda").
        iSpecialize ("Hdurable" with "Hhdr Hdata").
        iFrame. eauto 10 with iFrame. }
      iIntros "!>" (s) "[Hda Hb]".
      iDestruct (own_discrete_elim with "Hdata") as "Hdata".
      iSpecialize ("Hdata" with "Hda").
      iSpecialize ("Hdurable" with "Hhdr Hdata").
      iSplitR "Hdurable addrs Haddrs buffered Hbuffered His_blocks HP"; last first.
      { iMod (own_disc_fupd_elim with "HP"). iModIntro. iNext. iExists _. iFrame.
        eauto 10 with iFrame. }
      iModIntro.
      iIntros "His_locked".
      iSplit; first by iLeft in "HQ". (* TODO(Ralf): can we avoid this double-proof? *)
      iCache with "HQ"; first by iLeft in "HQ".
      wpc_frame.
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      wp_pures.
      iNamed 1.
      iApply "HQ".
      rewrite lookup_app_l; last word.
      rewrite Hlookup2.
      iDestruct (slice.is_slice_to_small with "Hb") as "Hb".
      iExists _. iFrame.
    * wpc_pures.
      iApply ncfupd_wpc.
      iSplit.
      { iLeft in "Hfupd". iModIntro. iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
      iRight in "Hfupd".
      iMod (own_disc_fupd_elim with "HP") as "HP".
      iMod ("Hfupd" $! σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      iMod (fupd_later_to_disc with "HP") as "HP".
      iApply wpc_fupd. iModIntro.
      wpc_frame "Hdurable HP HQ".
      { iLeft in "HQ". iModIntro. iNext. iFrame.
        iExists _. iFrame. iExists _; eauto. }
      wp_loadField.
      wp_bind (_ - _)%E.
      wp_pures.
      wp_apply wp_slice_len.
      wp_pures.
      wp_loadField.
      rewrite -(Qp_div_2 q).
      iEval (setoid_rewrite is_block_fractional) in "His_blocks".
      iEval (rewrite big_sepL2_sep) in "His_blocks".
      iDestruct "His_blocks" as "(His_blocks1&His_blocks2)".
      destruct (list_lookup_lt _ bks (int.nat (word.sub off addr_s.(Slice.sz)))) as [blk Hlookup].
      {
        assert (word.sub off (addr_s.(Slice.sz)) =
                int.val off - int.val addr_s.(Slice.sz)) as ->.
        { admit. }
        admit.
      }
      iDestruct (is_slice_small_read with "Hbuffered") as "(Hbuffered_small&Hbuffered_wand)".
      wp_apply (wp_SliceGet _ _ _ _ _ _ _ blk with "[$Hbuffered_small //]").
      iIntros "Hbuffered"; iNamed 1.
      iDestruct ("Hbuffered_wand" with "[$]") as "Hbuffered".
      iSplitR "Hdurable addrs Haddrs Haddrs_small buffered Hbuffered His_blocks1 HP"; last first.
      { iMod (own_disc_fupd_elim with "HP"). iModIntro. iNext. iExists _. iFrame.
        iExists _, _, _, _. iFrame. eauto. }
      iModIntro.
      iIntros "His_locked".
      iSplit; first by iLeft in "HQ". (* TODO(Ralf): can we avoid this double-proof? *)
      iCache with "HQ"; first by iLeft in "HQ".
      wpc_frame.
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      wp_pures.
      iNamed 1.
      iApply "HQ".
      rewrite lookup_app_r; last word.
      iDestruct (big_sepL2_lookup_1_some with "[$]") as %Hlookup2; eauto.
      destruct Hlookup2 as (?&Hlookup2).
      iDestruct (big_sepL2_lookup with "[$]") as "Hlookup"; eauto.
      assert (int.nat off - length σ.(inode.durable_blocks) =
              int.nat (word.sub off addr_s.(Slice.sz)))%nat as Heq_word.
      { word. }
      rewrite Heq_word Hlookup2. eauto.
Admitted.

Theorem wpc_Inode__Read_triple {k} {l k' P addr} {off: u64} Q :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (S k') P addr ∗
      "Hfupd" ∷ (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = (σ.(inode.durable_blocks) ++ σ.(inode.buffered_blocks)) !! int.nat off⌝ ∗
        ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off @ NotStuck; (S k); ⊤
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => ∃ q, is_block s q b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}
  {{{ True }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iApply wpc_Inode__Read; first done.
  iFrame "Hinode".
  iSplit.
  { iLeft in "HΦ". iModIntro. iApply "HΦ". done. }
  iNext. iIntros (σ mb) "[%Hσ HP]". iMod ("Hfupd" with "[$HP //]") as "[HP HQ]".
  iModIntro. iFrame "HP". iSplit.
  { iLeft in "HΦ". iModIntro. iApply "HΦ". done. }
  iIntros (s) "Hblock". iApply "HΦ". iFrame. done.
Qed.

Theorem wpc_Inode__Size {k} {l k' P addr}:
  (S k < k')%nat →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (S k') P addr ∗
      "Hfupd" ∷ (<disc> ▷ Φc ∧ ▷ (∀ σ (sz: u64),
          ⌜int.nat sz = inode.size σ⌝ ∗
          ▷ P σ -∗ |NC={⊤}=> ▷ P σ ∗ (<disc> ▷ Φc ∧ Φ (#sz: val)))) -∗
    WPC Inode__Size #l @ NotStuck; (S k); ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  rewrite /Inode__Size.
  wpc_pures; first by iLeft in "Hfupd".
  iCache with "Hfupd"; first by iLeft in "Hfupd".
  wpc_frame_seq.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iDestruct 1 as (σ) "(>Hlockinv&HP)".
  iMod (fupd_later_to_disc with "HP") as "HP".
  iApply ncfupd_wpc.
  iSplit.
  { iLeft in "Hfupd". do 2 iModIntro. iNext. eauto 10 with iFrame. }
  iEval (rewrite /named) in "HP".
  iNamed "Hlockinv".
  iNamed "Hlockinv".
  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (is_inode_durable_size with "Hdurable") as %Hblocks_length.
  iDestruct "Hbuffered" as (q) "(Hbuffered&His_blocks)".
  iDestruct (is_slice_sz with "Hbuffered") as %Hbuf_sz.

  iRight in "Hfupd".
  iMod (own_disc_fupd_elim with "HP") as "HP".
  iMod ("Hfupd" $! σ (word.add addr_s.(Slice.sz) buffered_s.(Slice.sz)) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    rewrite /inode.size.
    autorewrite with len in Haddrs_sz.
    autorewrite with len in Hbuf_sz.
    rewrite word.unsigned_add. admit.
    (* rewrite -Haddrs_sz //. *)
  }

  iMod (fupd_later_to_disc with "HP") as "HP".
  iModIntro.
  iCache with "HQ Hdurable HP".
  { iLeft in "HQ". iModIntro. iNext. iFrame. iExists _. iFrame.
    iExists _. eauto. }
  iApply wpc_fupd.
  wpc_frame.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  iNamed 1.
  iSplitR "HP addrs Haddrs Hdurable buffered Hbuffered His_blocks"; last first.
  { iMod (own_disc_fupd_elim with "HP") as "HP". iModIntro. iNext.
    iExists _; iFrame. iExists _, _, _, _. iFrame. eauto. }
  iIntros "!> His_locked".
  iSplit; first by iLeft in "HQ".
  iCache with "HQ"; first by iLeft in "HQ".
  wpc_pures.
  wpc_frame.
  wp_loadField.
  wp_apply (crash_lock.release_spec with "His_locked"); auto.
  wp_pures.
  iNamed 1.
  by iRight in "HQ".
Admitted.

Theorem wpc_Inode__Size_triple {k} {l k' P addr} (Q: u64 -> iProp Σ) (Qc: iProp Σ) :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (S k') P addr ∗
      "HQc" ∷ (∀ a, Q a -∗ <disc> ▷ Qc) ∗
      "Hfupd" ∷ (<disc> ▷ Qc ∧ (∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q sz))
  }}}
    Inode__Size #l @ NotStuck; (S k); ⊤
  {{{ sz, RET #sz; Q sz }}}
  {{{ Qc }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iApply wpc_Inode__Size; first done.
  iFrame "Hinode".
  iSplit.
  { iLeft in "Hfupd". iLeft in "HΦ". iModIntro. by iApply "HΦ". }
  iNext. iIntros (σ mb) "[%Hσ HP]". iMod ("Hfupd" with "[$HP //]") as "[HP HQ]".
  iModIntro. iFrame "HP". iSplit.
  { iSpecialize ("HQc" with "[$]"). iLeft in "HΦ". iModIntro. by iApply "HΦ". }
  iApply "HΦ". done.
Qed.

Theorem wp_Inode__mkHdr {stk E} l addr_s addrs :
  length addrs ≤ InodeMaxBlocks ->
  {{{ "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
      "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
  }}}
    Inode__mkHdr #l @ stk; E
  {{{ s b, RET (slice_val s);
      is_block s 1 b ∗
      ⌜block_encodes b ([EncUInt64 (U64 $ length addrs)] ++ (EncUInt64 <$> addrs))⌝ ∗
      "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
      "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
  }}}.
Proof.
  iIntros (Hbound Φ) "Hpre HΦ"; iNamed "Hpre".
  wp_call.
  wp_apply wp_new_enc; iIntros (enc) "Henc".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen.
  wp_apply wp_slice_len.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_loadField.
  iDestruct (is_slice_split with "Haddrs") as "[Haddrs Hcap]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Haddrs]").
  { word. }
  iIntros "[Henc Haddrs]".
  iDestruct (is_slice_split with "[$Haddrs $Hcap]") as "Haddrs".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (??) "(%Henc&Hs)".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  eapply block_encodes_eq; eauto.
  rewrite app_nil_l.
  repeat (f_equal; try word).
Qed.

Theorem wlog_assume_l {PROP:bi} (φ: Prop) (P: PROP) :
  φ →
  (⌜φ⌝ -∗ P) -∗
  ⌜φ⌝ ∗ P.
Proof.
  iIntros (H) "Himpl".
  iSplitR; auto.
  iApply ("Himpl" with "[//]").
Qed.

Lemma is_inode_durable_wf addr σ addrs :
  is_inode_durable addr σ addrs -∗
  ⌜inode.wf σ⌝.
Proof.
  iNamed 1.
  iFrame "%".
Qed.

Definition reserve_fupd E (Palloc: alloc.t → iProp Σ) : iProp Σ :=
  ∀ (σ σ': alloc.t) ma,
    ⌜match ma with
     | Some a => a ∈ alloc.free σ ∧ σ' = <[a:=block_reserved]> σ
     | None => σ' = σ ∧ alloc.free σ = ∅
     end⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc σ'.

(* free really means unreserve (we don't have a way to unallocate something
marked used) *)
Definition free_fupd E (Palloc: alloc.t → iProp Σ) (a:u64) : iProp Σ :=
  ∀ (σ: alloc.t),
    ⌜σ !! a = Some block_reserved⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_free]> σ).

(* This is useless because you need to do this together with some other action. *)
Definition use_fupd E (Palloc: alloc.t → iProp Σ) (a: u64): iProp Σ :=
  (∀ σ : alloc.t,
      ⌜σ !! a = Some block_reserved⌝ -∗
      ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_used]> σ)).

Lemma is_inode_durable_append addr addrs b0 σ :
  (inode.wf (set inode.buffered_blocks (λ bs : list Block, bs ++ [b0]) σ)) →
  is_inode_durable addr (set inode.buffered_blocks (λ bs : list Block, bs ++ [b0]) σ) addrs ≡
  is_inode_durable addr σ addrs.
Proof.
  rewrite /is_inode_durable //=. iIntros (Hwf).
  f_equiv => ?. f_equiv. rewrite /inode.wf.
  iSplit; iIntros (Hle); try eauto.
  iPureIntro. rewrite /= app_length in Hle. lia.
Qed.

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.

Theorem wpc_Inode__Append {k} {l k' P addr} q (b_s: Slice.t) (b0: Block) :
  (S k < k')%nat →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (S k') P addr ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "Hfupd" ∷ (<disc> ▷ Φc ∧ ▷ (Φ #false ∧ ∀ σ σ',
        ⌜σ' = set inode.buffered_blocks (λ bs, bs ++ [b0]) σ⌝ -∗
        ⌜inode.wf σ⌝ -∗
         ▷ P σ -∗ |NC={⊤}=> ▷ P σ' ∗ (<disc> ▷ Φc ∧ Φ #true))) -∗
  WPC Inode__Append #l (slice_val b_s) @ NotStuck; (S k); ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  rewrite /Inode__Append.
  wpc_pures; first by iLeft in "Hfupd".
  wpc_pures; first by iLeft in "Hfupd".
  iCache with "Hfupd"; first by iLeft in "Hfupd".
  wpc_frame_seq.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iDestruct 1 as (σ) "(>Hlockinv&HP)".
  iEval (rewrite /named) in "HP".
  iNamed "Hlockinv".
  iNamed "Hlockinv".
  iMod (fupd_later_to_disc with "HP") as "HP".
  iApply wpc_ncfupd.
  iCache with "Hfupd HP Hdurable".
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
  wpc_frame.

  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (blocks_slice_length with "Hbuffered") as %Hlen3.
  iDestruct (blocks_slice_length' with "Hbuffered") as %Hlen4.
  iDestruct "Hbuffered" as (q') "(Hbuffered&His_blocks)".
  iDestruct (is_slice_sz with "Hbuffered") as %Hbuf_sz.
  rewrite /Inode__append.
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  - iNamed 1.
    iMod (own_disc_fupd_elim with "HP") as "HP".
    iModIntro.
    iSplitR "HP addrs Haddrs Hdurable buffered His_blocks Hbuffered"; last first.
    { iNext. iExists _; iFrame "HP". iExists _, _, _, _. iFrame. eauto. }
    iIntros "His_locked". iSplit; first by iLeft in "Hfupd".
    wpc_pures.
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    wp_pures.
    iNamed 1. iRight in "Hfupd". by iLeft in "Hfupd".
  - wp_loadField.
    wp_apply (@wp_SliceAppend with "Hbuffered").
    iIntros (buffered_s').
    iIntros "Hbuffered".
    wp_apply (wp_storeField with "buffered").
    { rewrite /field_ty/Inode.S //=. apply slice_val_ty. (* XXX: why doesn't automation find this? *) }
    iIntros "buffered". wp_pures.
    iNamed 1.
    iRight in "Hfupd". iRight in "Hfupd".
    iMod (own_disc_fupd_elim with "HP") as "HP".
    iMod ("Hfupd" $! _ _ with "[//] [//] HP") as "(HP&HΦ)".
    iModIntro.
    iSplitR "HP addrs Haddrs Hdurable buffered His_blocks Hbuffered Hbdata"; last first.
    { iNext. iExists _; iFrame "HP". iExists _, _, _, _. iFrame.
      iApply wlog_assume_l.
      { rewrite /inode.wf /=.
        autorewrite with len; simpl.
        rewrite /InodeMaxBlocks.
        admit.
      }
      iIntros (Hwf').
      rewrite is_inode_durable_append //. iFrame.
      assert (∃ qmin qrest qrest', q = qmin + qrest ∧ q' = qmin + qrest')%Qp as (qmin&qrest&qrest'&Hqrest&Hqrest').
      { admit. }
      rewrite Hqrest Hqrest'. iExists qmin.
      rewrite big_sepL2_snoc. iSplitR "Hbdata"; last first.
      { rewrite is_block_fractional. iDestruct "Hbdata" as "($&_)". }
      iApply (big_sepL2_mono with "His_blocks").
      iIntros (?????) "H".
      { rewrite is_block_fractional. iDestruct "H" as "($&_)". }
    }
    iIntros "His_locked". iSplit; first by iLeft in "HΦ".
    iCache with "HΦ"; first by iLeft in "HΦ".
    wpc_frame.
    wp_pures.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    wp_pures.
    iNamed 1.
    by iRight in "HΦ".
Admitted.

Theorem wpc_Inode__flushOne {k}
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (alloc_ref: loc) (b_s: Slice.t) σ (b0: Block) bs :
  σ.(inode.buffered_blocks) = b0 :: bs →
  (S k < n)%nat →
  (S k < k')%nat →
  inodeN ## allocN →
  ∀ Φ Φc,
      "Hlockinv" ∷ inode_linv l addr σ ∗
      "HP" ∷ ▷ P σ ∗
      "Hinode" ∷ is_inode l (S k') P addr ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (<disc> ▷ Φc
        ∧ ▷ (("Hlockinv" ∷ inode_linv l addr σ ∗
                           "HP" ∷ ▷ P σ ∗
                           "Hinode" ∷ is_inode l (S k') P addr -∗
                           Φ #false)
        ∧ ∀ addr',
        let σ' :=
          set inode.buffered_blocks (λ _, bs)
               (set inode.durable_blocks (λ bs, bs ++ [b0]) (set inode.addrs ({[addr']} ∪.) σ)) in
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s -∗ |NC={⊤ ∖ ↑allocN}=>
           ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗
           (<disc> ▷ Φc ∧ ("Hlockinv" ∷ inode_linv l addr σ' ∗
                           "HP" ∷ ▷ P σ' ∗
                           "Hinode" ∷ is_inode l (S k') P addr -∗
                           Φ #true)))) -∗
  WPC Inode__flushOne #l #alloc_ref @ NotStuck; (S k); ⊤ {{ Φ }}
    {{ Φc ∗  (∃ σ0, "Hlockcinv" ∷ inode_cinv addr σ0 ∗ "HP" ∷ P σ0)  }}.
Proof.
  iIntros (Hbuf_list ??? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  iMod (fupd_later_to_disc with "HP") as "HP".
  wpc_call.
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. }
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. }
  iCache with "Hfupd HP Hlockinv".
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. }
  wpc_pures.
  wpc_frame_seq.
  wp_apply (wp_Reserve _ _ _ (λ ma, emp)%I with "[$Halloc]"); auto.
  { (* Reserve fupd *)
    iIntros (σa σa' ma Htrans) "HP".
    iMod ("Halloc_fupd" with "[] HP"); eauto. }
  iIntros (a ok) "Hblock".
  iNamed 1.
  wpc_pures.
  wpc_if_destruct.
  - iApply wpc_ncfupd. wpc_pures.
    iRight in "Hfupd".
    iLeft in "Hfupd". iApply "Hfupd". iMod (own_disc_fupd_elim with "HP").
    iFrame. iModIntro. iExists _, _. iFrame "#".
  - iDestruct "Hblock" as "[_ Hb]".
    iNamed "Hlockinv".
    iDestruct (is_inode_durable_size with "Hdurable") as %Hlendurable.
    iCache with "Hfupd HP Hdurable".
    { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }
    wpc_pures.
    wpc_bind_seq.
    wpc_frame.

    wp_loadField.

    iDestruct (blocks_slice_length with "Hbuffered") as %Hlen.
    iDestruct (blocks_slice_length' with "Hbuffered") as %Hlen'.
    iDestruct "Hbuffered" as (q') "(Hbuffered&His_blocks)".
    iDestruct (is_slice_small_read with "Hbuffered") as "(Hbuffered_small&Hbuffered_wand)".
    iDestruct (big_sepL2_lookup_2_some _ _ _ O with "His_blocks") as "%Hblock_lookup"; eauto.
    { rewrite Hbuf_list //. }
    destruct Hblock_lookup as (blk&Hblock_lookup).
    wp_apply (wp_SliceGet _ _ _ _ 1%Qp bks _ _ with "[$Hbuffered_small]").
    { iPureIntro; eauto. }
    iIntros "Hbuffered_small".
    iNamed 1.
    wpc_pures.

    wpc_bind_seq.
    wpc_frame.
    wp_loadField.
    wp_apply (wp_SliceSkip').
    { iPureIntro.
      cut (1 ≤ int.nat buffered_s.(Slice.sz)); first by word.
      rewrite -Hlen' Hlen Hbuf_list /=. lia.
    }
    wp_apply (wp_storeField with "buffered").
    { rewrite /field_ty/Inode.S //=. apply slice_val_ty. (* XXX: why doesn't automation find this? *) }
    iIntros "buffered".
    iNamed 1.
    wpc_pures.

    wpc_bind_seq.
    iApply (prepare_reserved_block_reuse with "Hb"); auto.
    { lia. }
    iSplit; first by iFromCache.
    iIntros ">Hb Hreserved".
    iDeexHyp "Hb".
    iAssert (□ ∀ b0, int.val a d↦ b0 ∗
                      (Φc) -∗
                      (Φc ∗ block_cinv Ψ γalloc a))%I as "#Hbc".
    { iIntros "!>" (b') "(Hb & Hfupd)".
      iSplitL "Hfupd"; first done.
      iApply block_cinv_free_pred.
      iExists _; iFrame. }


    iCache with "Hfupd Hb HP Hdurable".
    {  iLeft in "Hfupd". iModIntro. iFrame. iNext. iSplitR "Hb"; last first.
       { rewrite /block_cinv. iLeft. rewrite /Ψ. eauto. }
       iExists _.  iFrame. iExists _. iFrame. }

    iDestruct (big_sepL2_lookup_acc with "His_blocks") as "[Hbdata His_blocks_wand]"; eauto.
    { rewrite Hbuf_list /=; eauto. }

    wpc_apply (wpc_Write' with "[$Hb $Hbdata]").
    iSplit.
    { iLeft in "Hfupd". iModIntro. iNext.
      iIntros "[Hb|Hb]"; iDestruct ("Hbc" with "[$]") as "($&$)";
        iFrame; iExists _; iFrame; iExists _; iFrame.
    }
    iIntros "!> [Hda Hbdata]".
    iDestruct ("His_blocks_wand" with "Hbdata") as "His_blocks".
    iFrame "Hreserved".
    iSplitR "Hda"; last first.
    { instantiate (1:=λ _, _); simpl.
      iSplitL; [ iAccu | ].
      iModIntro.
      iIntros "Hda".
      iApply block_cinv_free_pred. iExists _; iFrame. }
    iIntros "Hreserved".
    iSplit; first iFromCache.
    wpc_pures.
    wpc_call.

    wpc_bind_seq.
    wpc_frame_seq.
    wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Haddrs]").
    iIntros (addr_s') "Haddrs".
    Transparent slice.T.
    wp_storeField.
    Opaque slice.T.
    iNamed 1.
    wpc_pures.
    wpc_frame_seq.
    wp_apply (wp_Inode__mkHdr with "[$addrs $Haddrs]").
    { autorewrite with len; simpl.
      rewrite /inode.wf in Hwf.
      rewrite Hbuf_list /= in Hwf.
      lia. }
    iIntros (s b') "(Hb&%Hencoded'&?&?)"; iNamed.
    iNamed 1.
    wpc_pures.
    wpc_loadField.

    iApply (prepare_reserved_block with "Hreserved"); auto; try lia.
    iSplit; first iFromCache.
    iIntros ">Hda Hreserved".
    (* hide this horrible postcondition for now *)
    match goal with
    | |- envs_entails _ (wpc _ _ _ _ ?Φ0 _) => set (Φ':=Φ0)
    end.
    wpc_apply (wpc_Write_ncfupd with "[$Hb]").
    iSplit.
    { iLeft in "Hfupd". iModIntro. iNext. iSplitR "Hda".
      * iFrame. iExists _; iFrame. iExists _; iFrame.
      * iApply block_cinv_free_pred. iExists _; iFrame. }
    iNamed "Hdurable".
    iRight in "Hfupd".
    iRight in "Hfupd".
    set (σ' := (set inode.buffered_blocks (λ _ : list Block, bs)
                                              (set inode.durable_blocks (λ bs0 : list Block, bs0 ++ [b0])
                                                 (set inode.addrs (union {[a]}) σ)))).
    iSpecialize ("Hfupd" $! a with "[% //]").

    iMod (mark_used _ _ _ _ _ _ (▷ P σ' ∗
           (<disc> ▷ Φc ∧ ("Hlockinv" ∷ inode_linv l addr σ' ∗
                           "HP" ∷ ▷ P σ' ∗
                           "Hinode" ∷ is_inode l (S k') P addr -∗
                           Φ #true)))%I
            with "Hreserved [HP Hfupd]") as "Hget_used".
    { solve_ndisj. }
    { clear.
      iIntros (s Hreserved) "HPalloc".
      iMod (own_disc_fupd_elim with "HP") as "HP".
      iMod ("Hfupd" with "[% //] [$HP $HPalloc]") as "(HP&HPalloc&HQ)".
      iFrame. eauto. }

    iModIntro.
    iExists _; iFrame.
    iNext.
    iIntros "Hhdr".
    iMod "Hget_used" as "[ (HP&HQ) Hused]".
    iAssert (is_inode_durable addr
              (set inode.buffered_blocks (λ _ : list Block, bs)
               (set inode.durable_blocks (λ bs : list Block, bs ++ [b0])
                    (set inode.addrs (union {[a]}) σ)))
               (addrs ++ [a]))
            with "[Hhdr Hdata Hda]" as "Hdurable".
    { iExists _; iFrame "∗ %".
      iSplitR.
      { iPureIntro.
        rewrite /inode.wf /= in Hwf *.
        rewrite Hbuf_list /= in Hwf *.
        autorewrite with len; simpl.
        lia. }
      iSplitR.
      { iPureIntro.
        simpl.
        rewrite list_to_set_app_L.
        simpl.
        set_solver. }
      simpl; auto. }
    iDestruct (is_inode_durable_wf with "Hdurable") as %Hwf'.
    iCache (<disc> ▷ Φc)%I with "HQ".
    { by iLeft in "HQ". }
    iMod (fupd_later_to_disc with "HP") as "HP".
    iModIntro.
    match goal with
    | |- envs_entails _ (<disc> (▷ (?P ∗ _)) ∧ _) =>
      iCache (<disc> ▷ P)%I with "HQ HP Hdurable"
    end.
    { iLeft in "HQ". iModIntro. iNext. iFrame. iExists _; iFrame; iExists _; iFrame. }
    iCache (block_cinv Ψ γalloc a) with "Hused".
    { iApply block_cinv_from_used; iFrame. }
    iSplit.
    { iLeft in "HQ". iModIntro. iNext. iFrame. iExists _; iFrame; iExists _; iFrame. }
    iIntros "Hb".
    subst Φ'; cbv beta.
    (* done applying wpc_Write_fupd *)
    iSplitR "Hused"; last (iFromCache).

    iSplit.
    { iLeft in "HQ". iModIntro. iNext. iFrame. iExists _; iFrame; iExists _; iFrame. }

    iApply wpc_fupd.
    wpc_pures.
    { iMod (own_disc_fupd_elim with "HP"). iModIntro. iRight in "HQ".
      iApply "HQ". iFrame.
      iDestruct ("Hbuffered_wand" with "[$]") as "Hbuffered".
      iSplitL "Hdurable buffered Hbuffered addrs Haddrs His_blocks".
      {
        destruct bks as [| ? bks'].
        { rewrite //= in Hblock_lookup. }
        iExists _, _, bks', _. iFrame "Hdurable buffered addrs Haddrs".
        iSplitL "".
        { iPureIntro. admit. }
        iExists _.
        rewrite /σ'/= Hbuf_list big_sepL2_cons. iDestruct "His_blocks" as "(_&$)".
        (* XXX: need lemmas about slice skip and is_slice ? *)
        admit.
      }
      iExists _, _. iFrame "#".
 }
Admitted.

Fixpoint flush_fupd P Palloc (σ: inode.t) Φ (Φc: iProp Σ) (buflist: list Block) : iProp Σ :=
  (<disc> ▷ Φc) ∧
  match buflist with
  | [] => ▷ Φ #false ∧
     (▷ P σ -∗ |NC={⊤}=> ▷ P σ ∗ (<disc> ▷ Φc ∧ Φ #true))
  | b0 :: bs => ▷(Φ #false ∧
    ∀ addr',
      let σ' :=
          set inode.buffered_blocks (λ _, bs)
               (set inode.durable_blocks (λ bs, bs ++ [b0]) (set inode.addrs ({[addr']} ∪.) σ)) in
      ⌜inode.wf σ⌝ -∗
      ∀ (s: alloc.t),
      ⌜s !! addr' = Some block_reserved⌝ -∗
       ▷ P σ ∗ ▷ Palloc s -∗ |NC={⊤ ∖ ↑allocN}=>
       ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ (flush_fupd P Palloc σ' Φ Φc bs))
  end%I.

Lemma flush_fupd_crash_elim P Palloc σ Φ Φc bs :
  flush_fupd P Palloc σ Φ Φc bs -∗ <disc> ▷ Φc.
Proof. destruct bs => /=; by rewrite and_elim_l. Qed.

(* We allow Flush to spuriously report a "failure" even if in fact the buffer is now empty *)
Lemma flush_fupd_false_case_elim P Palloc σ Φ Φc bs :
  flush_fupd P Palloc σ Φ Φc bs -∗ <disc> ▷ Φc ∧ ▷ Φ #false.
Proof.
  destruct bs => /=.
  - iIntros "H". iSplit.
    * by iLeft in "H".
    * iRight in "H". by iLeft in "H".
  - iIntros "H". iSplit.
    * by iLeft in "H".
    * iRight in "H". by iLeft in "H".
Qed.

Theorem wpc_Inode__Flush {k}
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (alloc_ref: loc) :
  (S k < n)%nat →
  (S k < k')%nat →
  inodeN ## allocN →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (S k') P addr ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (<disc> ▷ Φc ∧ (∀ σ, flush_fupd P Palloc σ Φ Φc σ.(inode.buffered_blocks))) -∗
  WPC Inode__Flush #l #alloc_ref @ NotStuck; (S k); ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  rewrite /Inode__Flush.
  wpc_pures; first by iLeft in "Hfupd".
  iCache with "Hfupd"; first by iLeft in "Hfupd".
  wpc_frame_seq.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iDestruct 1 as (σ) "(>Hlockinv&HP)".
  iEval (rewrite /named) in "HP".
  iNamed "Hlockinv".
  iNamed "Hlockinv".
  iMod (fupd_later_to_disc with "HP") as "HP".
  iApply wpc_ncfupd.
  iCache with "Hfupd HP Hdurable".
  { iLeft in "Hfupd". iModIntro. iNext. iFrame. iExists _; iFrame. iExists _. iFrame. }

  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (blocks_slice_length with "Hbuffered") as %Hlen3.
  iDestruct (blocks_slice_length' with "Hbuffered") as %Hlen4.
  iDestruct "Hbuffered" as (q') "(Hbuffered&His_blocks)".
  iDestruct (is_slice_sz with "Hbuffered") as %Hbuf_sz.
  rewrite /Inode__flush.
  wpc_call.
  wpc_bind_seq.
  iRight in "Hfupd". iSpecialize ("Hfupd" $! σ).
  wpc_apply (wpc_forBreak_cond'
               (λ _, ∃ σ addrs addr_s buffered_s bks q',
                     "Hwf" ∷ ⌜ inode.wf σ ⌝ ∗
                     "Hfupd" ∷ flush_fupd P Palloc σ Φ Φc σ.(inode.buffered_blocks) ∗
                     "Hdurable" ∷ is_inode_durable addr σ addrs ∗
                     "buffered" ∷ l ↦[Inode.S :: "buffered"] (slice_val buffered_s) ∗
                     "Hbuffered" ∷ is_slice buffered_s (slice.T byteT) 1 bks ∗
                     "His_blocks" ∷ ([∗ list] b_s;b ∈ bks;σ.(inode.buffered_blocks), is_block b_s q' b) ∗
                     "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
                     "Haddrs" ∷ is_slice addr_s uint64T 1 addrs ∗
                     "HP" ∷ <disc> ▷ P σ)%I
               ((Φc ∗ (∃ σ0, "Hlockcinv" ∷ inode_cinv addr σ0 ∗ "HP" ∷ P σ0)))%I); swap 2 4.
  { iIntros (?). iNamed 1. iDestruct (flush_fupd_crash_elim with "Hfupd") as "Hfupd".
    iModIntro. iNext. iFrame. iExists _. iClear "Hwf". iFrame. iExists _. iFrame.
  }
  { iExists _, _, _, _, _. iFrame. eauto. }
  { iModIntro. iNamed 1.
    iCache with "HP Hdurable Hfupd".
    {
      iDestruct (flush_fupd_crash_elim with "Hfupd") as "Hfupd".
      iModIntro. iNext. iFrame. iExists _.  iFrame. iExists _. iFrame.
    }
    wpc_pures.
    wpc_bind (_ > _)%E.
    wpc_frame.
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.
    iNamed 1.
    wpc_if_destruct.
    * wpc_pures.
      wpc_bind_seq.
      iMod (own_disc_fupd_elim with "HP") as "HP".
      destruct (σ0.(inode.buffered_blocks)) as [| b0 bs] eqn:Heq_buf.
      {
        iDestruct (is_slice_sz with "Hbuffered") as "%".
        iDestruct (big_sepL2_length with "His_blocks") as "%".
        exfalso. simpl in *.
        admit.
      }
      wpc_apply (@wpc_Inode__flushOne k l k' P addr Palloc γalloc domain n alloc_ref _ σ0 with "[-]").
      { eapply Heq_buf. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      iDestruct "Hwf" as "#Hwf".
      iSplitL "Hdurable buffered Hbuffered addrs Haddrs His_blocks Hwf".
      { iExists _, _, _, _. iFrame. iFrame "#". iExists _. rewrite Heq_buf. iFrame. }
      iFrame. iFrame "Halloc Halloc_fupd Hfree_fupd".
      iSplitL "".
      { iExists _, _. iFrame "#". }
      rewrite -/flush_fupd.
      iSplit.
      { iLeft in "Hfupd". eauto. }
      iNext. iSplit; last first.
      { iIntros.
        iRight in "Hfupd".
        iRight in "Hfupd".
        iMod ("Hfupd" with "[//] [//] [$]") as "(HP&HPalloc&Hfupd)".
        rewrite -/flush_fupd.
        iFrame "HP HPalloc".
        iModIntro.
        iSplit.
        { by iApply flush_fupd_crash_elim. }
        iNamed 1.
        iMod (fupd_later_to_disc with "HP") as "HP".
        wpc_pures.
        {
          iDestruct (flush_fupd_crash_elim with "Hfupd") as "Hfupd".
          iModIntro. iFrame. iModIntro. iExists _. iFrame.
        }
        iExists _. iSplit; first eauto.
        iNamed "Hlockinv".
        iDestruct "Hbuffered" as (q'') "(?&?)".
        iExists _, addrs1, addr_s1, _, bks1, q''. iFrame.
        eauto.
      }
      iNamed 1.
      iMod (fupd_later_to_disc with "HP") as "HP".
      wpc_pures.
      { iLeft in "Hfupd". iModIntro.  iNext. iFrame. iExists _. iFrame. }
      iExists _. iSplitL ""; first eauto.
      iNamed "Hlockinv". iNamed "Hbuffered".
      iExists σ0, _, _, _, _, _.
      rewrite -/flush_fupd.
      { rewrite Heq_buf. rewrite /=. iSplitL ""; first eauto.
        iSplitL "Hfupd".
        { iSplit; first by iLeft in "Hfupd". iNext. iRight in "Hfupd". eauto. }
        iFrame.
      }
    * wpc_pures. iExists _. iSplitL ""; first eauto.
      iExists _, _, _, _, _, _. iFrame.
  }
  iSplit.
  { iModIntro; eauto. }
  iNext.
  iNamed 1.
  iCache with "Hfupd HP Hdurable".
  {
      iDestruct (flush_fupd_crash_elim with "Hfupd") as "Hfupd".
      iModIntro. iNext. iFrame. iExists _.  iFrame. iExists _. iFrame.
  }
  wpc_pures.
  wpc_frame.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_if_destruct.
  - iNamed 1. iMod (own_disc_fupd_elim with "HP") as "HP".
    iSplitR "HP Hwf buffered Hbuffered His_blocks addrs Haddrs Hdurable"; last first.
    { iModIntro. iNext. iExists _. iFrame.
      iExists _, _, _, _. iFrame. iExists _. iFrame.
    }
    iModIntro. iIntros.
    iDestruct (flush_fupd_false_case_elim with "Hfupd") as "Hfupd".
    iSplit.
    { by iLeft in "Hfupd". }
    iCache with "Hfupd".
    { by iLeft in "Hfupd". }
    wpc_pures.
    iCache with "Hfupd".
    { by iLeft in "Hfupd". }
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$]"); auto.
    wp_pures. iNamed 1.
    iRight in "Hfupd".
    eauto.
  - iNamed 1. iMod (own_disc_fupd_elim with "HP") as "HP".
    (* TODO: argue that buffered_blocks must be = [] *)
    iDestruct (is_slice_sz with "Hbuffered") as "%".
    iDestruct (big_sepL2_length with "His_blocks") as "%".
    assert (int.nat buffered_s0.(Slice.sz) = 0)%nat.
    { admit. }
    assert (Hemptybuf: σ0.(inode.buffered_blocks) = []).
    { apply nil_length_inv. lia. }
    rewrite Hemptybuf.
    iRight in "Hfupd". iRight in "Hfupd".
    iMod ("Hfupd" with "HP") as "(HP&Hfupd)".
    iSplitR "HP Hwf buffered Hbuffered His_blocks addrs Haddrs Hdurable"; last first.
    { iModIntro. iNext. iExists _. iFrame.
      iExists _, _, _, _. iFrame. iExists _. iFrame.
      rewrite Hemptybuf. iFrame.
    }
    iModIntro. iIntros.
    iEval (simpl) in "Hfupd".
    iSplit.
    { by iLeft in "Hfupd". }
    iCache with "Hfupd".
    { by iLeft in "Hfupd". }
    wpc_pures.
    iCache with "Hfupd".
    { by iLeft in "Hfupd". }
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$]"); auto.
    wp_pures. iNamed 1.
    by iRight in "Hfupd".
    (* XXX track this down... *)
    Unshelve. exact addr_s.
Admitted.

End goose.

Section goose.
Context `{!heapG Σ}.
Context `{!allocG Σ}.

Context (P: inode.t → iProp Σ).

Instance inode_cinv_stable addr σ :
  IntoCrash (inode_cinv addr σ) (λ _, inode_cinv addr σ).
Proof.
  intros.
  hnf; iNamed 1.
  rewrite ?big_sepL2_alt.
  iDestruct "Hdata" as "(%Heq&Hl)".
  iCrash.
  iExists _, _. iFrame.
  rewrite ?big_sepL2_alt.
  iFrame. eauto.
Qed.

End goose.
