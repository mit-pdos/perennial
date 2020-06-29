From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import inode.

(* TODO: alloc_crash_proof must be imported early since otherwise it messes up a
bunch of things, like Z_scope, encode, and val *)
From Perennial.program_proof.examples Require Import alloc_crash_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import into_val typed_slice.

From Perennial.program_proof Require Import marshal_proof disk_lib.

Definition InodeMaxBlocks: Z := 511.

Module inode.
  Record t :=
    mk { (* addresses consumed by this inode *)
         addrs: gset u64;
         blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addrs; blocks>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ InodeMaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.

Hint Unfold inode.wf InodeMaxBlocks : word.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

(* The client picks the namespaces that we use for everything. *)
Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t) (addr: u64).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_inode_durable addr σ (addrs: list u64) : iProp Σ :=
  ∃ (extra: list u8) (hdr: Block),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (EncUInt64 <$> addrs)) ++ extra⌝ ∗
    "%Haddrs_set" ∷ ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
    "Hhdr" ∷ int.val addr d↦ hdr ∗
    (* TODO: this does not support reading lock-free; we could make it [∃ q,
    int.val a d↦{q} b], but that wouldn't support lock-free writes if we
    implemented those *)
    "Hdata" ∷ [∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b
.
Local Hint Extern 1 (environments.envs_entails _ (is_inode_durable _ _ _)) => unfold is_inode_durable : core.

Theorem is_inode_durable_read addr σ addrs :
  is_inode_durable addr σ addrs -∗
    ∃ extra hdr,
      "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
      "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (EncUInt64 <$> addrs)) ++ extra⌝ ∗
      "%Haddrs_set" ∷ ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
      "Hhdr" ∷ int.val addr d↦ hdr ∗
      "Hdata" ∷ ([∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b) ∗
      "Hdurable" ∷ □(int.val addr d↦ hdr -∗
                    ([∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b) -∗
                   is_inode_durable addr σ addrs).
Proof.
  iNamed 1.
  iExists _, _; iFrame "∗ %".
  iIntros "!> Hhdr Hdata".
  iExists _, _; iFrame "∗ %".
Qed.

Definition inode_linv (l:loc) (addr:u64) σ : iProp Σ :=
  ∃ (addr_s: Slice.t) (addrs: list u64),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "Hdurable" ∷ is_inode_durable addr σ addrs ∗
    "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
    "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
.
Local Hint Extern 1 (environments.envs_entails _ (inode_linv _ _ _)) => unfold inode_linv : core.

Definition inode_cinv addr σ: iProp Σ :=
  ∃ addrs, is_inode_durable addr σ addrs.
Local Hint Extern 1 (environments.envs_entails _ (inode_cinv _ _)) => unfold inode_cinv : core.

Definition inode_state l (d_ref: loc) (lref: loc) addr : iProp Σ :=
  "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d_ref) ∗
  "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
  "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr).

Definition is_inode l k P (addr: u64) : iProp Σ :=
  ∃ (d_ref:loc) (lref: loc),
    "Hro_state" ∷ inode_state l d_ref lref addr ∗
    "#Hlock" ∷ is_crash_lock inodeN inodeN k #lref
              (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ)
              (∃ σ, "Hlockcinv" ∷ inode_cinv addr σ ∗ "HP" ∷ P σ).

Definition pre_inode l addr σ : iProp Σ :=
  ∃ (d_ref:loc) (lref: loc),
    "Hro_state" ∷ inode_state l d_ref lref addr ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hlockinv" ∷ inode_linv l addr σ.

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
  int.val addr d↦ block0 -∗ inode_cinv addr (inode.mk ∅ []).
Proof.
  iIntros "Hhdr".
  iExists [], (replicate (int.nat (4096-8)) (U8 0)), block0.
  cbv [inode.blocks big_sepL2].
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
  is_inode l (LVL k) P addr ∗
  |C={⊤,∅}_(LVL (S k))=> (∃ σ', inode_cinv addr σ' ∗ P σ').
   (* Crash condition has [P] without extra ▷ because [alloc_crash_lock] strips that later for us. *)
Proof.
  iIntros "HP Hinode"; iNamed "Hinode".
  iMod (alloc_crash_lock_cfupd inodeN inodeN k
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

Theorem wpc_Open k E2 {d:loc} {addr σ} :
  {{{ inode_cinv addr σ }}}
    inode.Open #d #addr @ NotStuck; k; ⊤; E2
  {{{ l, RET #l; pre_inode l addr σ }}}
  {{{ inode_cinv addr σ }}}.
Proof.
  iIntros (Φ Φc) "Hinode HΦ"; iNamed "Hinode".
  iAssert (□ (int.val addr d↦ hdr ∗
              ([∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b) -∗
              inode_cinv addr σ))%I as "#Hinode".
  { iIntros "!> (?&?)". eauto 10 with iFrame. }
  iDestruct (big_sepL2_length with "Hdata") as %Hblocklen.
  rewrite /Open.
  wpc_pures.
  { iApply ("Hinode" with "[$]"). }
  iCache with "HΦ Hhdr Hdata".
  { crash_case. iApply ("Hinode" with "[$]"). }
  wpc_apply (wpc_Read with "Hhdr").
  iSplit; [ | iNext ].
  { iIntros "Hhdr"; iFromCache. }
  iIntros (s) "(Hhdr&Hs)".
  wpc_frame.
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  rewrite Hencoded.
  wp_apply (wp_NewDec with "Hs").
  iIntros (dec) "[Hdec %Hsz]".
  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ addrs _ nil with "[Hdec]").
  { rewrite app_nil_r; iFrame.
    iPureIntro.
    rewrite Hblocklen.
    word. }
  iIntros (addr_s) "[_ Haddrs]".
  wp_pures.
  rewrite -wp_fupd.
  wp_apply wp_new_free_lock.
  iIntros (lref) "Hlock".
  wp_apply wp_allocStruct; auto.
  iIntros (l) "inode".
  iDestruct (struct_fields_split with "inode") as "(d&m&addr&addrs&_)".
  iMod (readonly_alloc_1 with "d") as "#d".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "addr") as "#addr".
  iModIntro.
  iNamed 1.
  iApply "HΦ".
  iExists _, _; iFrame.
  iSplitR.
  { iFrame "#". }
  iExists _, _; iFrame "% ∗".
  iExists _, _; iFrame "% ∗".
Qed.

Theorem is_inode_durable_addrs addr σ addrs :
  is_inode_durable addr σ addrs -∗
  ⌜list_to_set addrs = σ.(inode.addrs)⌝.
Proof.
  iNamed 1.
  iFrame "%".
Qed.

Theorem is_inode_durable_size addr σ addrs :
  is_inode_durable addr σ addrs -∗ ⌜length addrs = length σ.(inode.blocks)⌝.
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
  iExists _, _; iFrame "∗ %".
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


Theorem wpc_Inode__Read {k E2} {l k' P addr} {off: u64} :
  (S k < k')%nat →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hfupd" ∷ (Φc ∧ ▷ ∀ σ mb,
        ⌜mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        ▷ P σ ={⊤ ∖ ↑inodeN}=∗ ▷ P σ ∗ (Φc ∧ ∀ s,
          match mb with Some b => is_block s 1 b | None => ⌜s = Slice.nil⌝ end -∗ Φ (slice_val s))) -∗
    WPC Inode__Read #l #off @ NotStuck; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  wpc_call.
  { by iLeft in "Hfupd". }
  iCache with "Hfupd".
  { by iLeft in "Hfupd". }
  wpc_bind_seq.
  wpc_frame.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); first by set_solver.
  iIntros "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iNamed 1.
  iCache with "Hfupd Hlockinv HP".
  { iSplitL "Hfupd"; first by iFromCache.
    iExists _; iFrame.
    iApply (inode_linv_to_cinv with "[$]"). }
  wpc_call.
  wpc_bind (_ ≥ _)%E.
  iNamed "Hlockinv".
  iCache with "Hfupd HP Hdurable".
  { iSplitL "Hfupd"; first by iFromCache.
    eauto 10 with iFrame. }
  iDestruct (is_inode_durable_size with "Hdurable") as %Hlen1.
  wpc_frame.
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen2.
  autorewrite with len in Hlen2.
  wp_apply wp_slice_len.
  wp_pures.
  iNamed 1.
  wpc_if_destruct.
  - iRight in "Hfupd".
    iMod ("Hfupd" $! σ None with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      rewrite lookup_ge_None_2 //.
      lia. }
    wpc_pures.
    { iLeft in "HQ". iFrame "HQ". eauto 10 with iFrame. }
    iSplitR "HP addrs Haddrs Hdurable"; last first.
    { eauto 10 with iFrame. }
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
  - destruct (list_lookup_lt _ addrs (int.nat off)) as [addr' Hlookup].
    { word. }
    iDestruct (is_slice_split with "Haddrs") as "[Haddrs_small Haddrs]".
    wpc_pures.
    wpc_frame_seq.
    wp_loadField.
    wp_apply (wp_SliceGet _ _ _ _ _ addrs with "[$Haddrs_small //]").
    iIntros "Haddrs_small"; iNamed 1.
    wpc_pures.
    iDestruct (is_inode_durable_read with "Hdurable") as "H"; iNamed "H".
    iDestruct (big_sepL2_lookup_1_some with "Hdata") as "%Hblock_lookup"; eauto.
    destruct Hblock_lookup as [b0 Hlookup2].
    iDestruct (is_slice_split with "[$Haddrs_small $Haddrs]") as "Haddrs".
    iDestruct (big_sepL2_lookup_acc with "Hdata") as "[Hb Hdata]"; eauto.
    iRight in "Hfupd".
    iMod ("Hfupd" $! σ with "[$HP]") as "[HP HQ]".
    { iPureIntro; eauto. }
    wpc_apply (wpc_Read with "Hb").
    iSplit.
    { iIntros "Hda".
      iSpecialize ("Hdata" with "Hda").
      iSpecialize ("Hdurable" with "Hhdr Hdata").
      iSplitL "HQ"; first by iLeft in "HQ".
      iNext. eauto 10 with iFrame. }
    iIntros "!>" (s) "[Hda Hb]".
    iSpecialize ("Hdata" with "Hda").
    iSpecialize ("Hdurable" with "Hhdr Hdata").
    iSplitR "Hdurable addrs Haddrs HP"; last first.
    { eauto 10 with iFrame. }
    iIntros "His_locked".
    iSplit; first by iLeft in "HQ". (* TODO(Ralf): can we avoid this double-proof? *)
    iCache with "HQ"; first by iLeft in "HQ".
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    wp_pures.
    iNamed 1.
    iApply "HQ".
    iFrame.
    rewrite Hlookup2.
    iDestruct (slice.is_slice_to_small with "Hb") as "Hb".
    iFrame.
Qed.

Theorem wpc_Inode__Read_triple {k E2} {l k' P addr} {off: u64} Q :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hfupd" ∷ (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        ▷ P σ ={⊤ ∖ ↑inodeN}=∗ ▷ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off @ NotStuck; LVL (S k); ⊤; E2
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => is_block s 1 b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}
  {{{ True }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iApply wpc_Inode__Read; first done.
  iFrame "Hinode".
  iSplit.
  { iApply "HΦ". done. }
  iNext. iIntros (σ mb) "[%Hσ HP]". iMod ("Hfupd" with "[$HP //]") as "[HP HQ]".
  iModIntro. iFrame "HP". iSplit.
  { iApply "HΦ". done. }
  iIntros (s) "Hblock". iApply "HΦ". iFrame. done.
Qed.

Theorem wpc_Inode__Size {k E2} {l k' P addr}:
  (S k < k')%nat →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hfupd" ∷ (Φc ∧ ▷ (∀ σ (sz: u64),
          ⌜int.nat sz = inode.size σ⌝ ∗
          ▷ P σ ={⊤ ∖ ↑inodeN}=∗ ▷ P σ ∗ (Φc ∧ Φ (#sz: val)))) -∗
    WPC Inode__Size #l @ NotStuck; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc }}.
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
  iNamed 1.
  iNamed "Hlockinv".
  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (is_inode_durable_size with "Hdurable") as %Hblocks_length.

  iRight in "Hfupd".
  iMod ("Hfupd" $! σ addr_s.(Slice.sz) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    rewrite /inode.size.
    autorewrite with len in Haddrs_sz.
    rewrite -Haddrs_sz //. }

  iCache with "HQ Hdurable HP".
  { iLeft in "HQ". eauto 10 with iFrame. }
  wpc_frame.
  wp_loadField.
  wp_apply wp_slice_len.
  iNamed 1.
  iSplitR "HP addrs Haddrs Hdurable"; last first.
  { eauto 10 with iFrame.  }
  iIntros "His_locked".
  iSplit; first by iLeft in "HQ".
  iCache with "HQ"; first by iLeft in "HQ".
  wpc_pures.
  wpc_frame.
  wp_loadField.
  wp_apply (crash_lock.release_spec with "His_locked"); auto.
  wp_pures.
  iNamed 1.
  by iRight in "HQ".
Qed.

Theorem wpc_Inode__Size_triple {k E2} {l k' P addr} (Q: u64 -> iProp Σ) (Qc: iProp Σ) :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "HQc" ∷ (∀ a, Q a -∗ Qc) ∗
      "Hfupd" ∷ (Qc ∧ (∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          ▷ P σ ={⊤ ∖ ↑inodeN}=∗ ▷ P σ' ∗ Q sz))
  }}}
    Inode__Size #l @ NotStuck; LVL (S k); ⊤; E2
  {{{ sz, RET #sz; Q sz }}}
  {{{ Qc }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iApply wpc_Inode__Size; first done.
  iFrame "Hinode".
  iSplit.
  { iApply "HΦ". by iLeft in "Hfupd". }
  iNext. iIntros (σ mb) "[%Hσ HP]". iMod ("Hfupd" with "[$HP //]") as "[HP HQ]".
  iModIntro. iFrame "HP". iSplit.
  { iApply "HΦ". by iApply "HQc". }
  iApply "HΦ". done.
Qed.

Theorem wp_Inode__mkHdr {stk E} l addr_s addrs :
  length addrs ≤ InodeMaxBlocks ->
  {{{ "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
      "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
  }}}
    Inode__mkHdr #l @ stk; E
  {{{ s b extra, RET (slice_val s);
      is_block s 1 b ∗
      ⌜Block_to_vals b = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (EncUInt64 <$> addrs)) ++ extra⌝ ∗
      "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
      "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
  }}}.
Proof.
  iIntros (Hbound Φ) "Hpre HΦ"; iNamed "Hpre".
  wp_call.
  wp_apply wp_new_enc; iIntros (enc) "[Henc %]".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen.
  autorewrite with len in Hlen.
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
  iIntros (s) "[Hs %]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  autorewrite with len in H0.
  iSplitL "Hs".
  - rewrite -list_to_block_to_vals; len.
    + iFrame.
    + rewrite H0.
      rewrite H; reflexivity.
  - iPureIntro.
    rewrite list_to_block_to_vals; len.
    + rewrite app_nil_l.
      repeat (f_equal; try word).
    + rewrite H0.
      rewrite H; reflexivity.
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

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.

Theorem wpc_Inode__Append {k E2}
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S k) < n)%nat →
  (S (S k) < k')%nat →
  nroot.@"readonly" ## allocN →
  nroot.@"readonly" ## inodeN →
  inodeN ## allocN →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (Φc ∧ ▷ (Φ #false ∧ ∀ σ σ' addr',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs ({[addr']} ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s ={⊤ ∖ ↑allocN ∖ ↑inodeN}=∗
         ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ (Φc ∧ Φ #true))) -∗
  WPC Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  wpc_call.
  { iLeft in "Hfupd"; auto. }
  iCache with "Hfupd".
  { iLeft in "Hfupd"; auto. }
  wpc_apply (wpc_Reserve _ _ _ (λ ma, emp)%I emp with "[$Halloc]"); auto.
  { (* Reserve fupd *)
    iSplit; auto.
    iIntros (σ σ' ma Htrans) "HP".
    iMod ("Halloc_fupd" with "[] HP"); eauto. }
  iSplit.
  { iIntros "_"; iFromCache. }
  iIntros "!>" (a ok) "Hblock".
  wpc_pures.
  wpc_if_destruct.
  - wpc_pures.
    iRight in "Hfupd".
    by iLeft in "Hfupd".
  - iDestruct "Hblock" as "[_ Hb]".
    wpc_pures.
    wpc_bind_seq.
    iApply (prepare_reserved_block_reuse with "Hb"); auto.
    iSplit; first by iFromCache.
    iIntros "Hb Hreserved".
    iDeexHyp "Hb".
    iAssert (□ ∀ b0 R, int.val a d↦ b0 ∗
                      (Φc ∧ R) -∗
                      Φc ∗ ▷ block_cinv Ψ γalloc a)%I as "#Hbc".
    { iIntros "!>" (b' R) "(Hb & Hfupd)".
      iLeft in "Hfupd".
      iSplitL "Hfupd"; first done.
      iApply block_cinv_free_pred.
      iExists _; iFrame. }

    iCache with "Hfupd Hb".
    {  iApply ("Hbc" with "[$]"). }
    wpc_apply (wpc_Write' with "[$Hb $Hbdata]").
    iSplit.
    { iIntros "[Hb|Hb]"; try iFromCache.
      iApply ("Hbc" with "[$]"). }
    iIntros "!> [Hda _]".
    iFrame "Hreserved".
    iSplitR "Hda"; last first.
    { instantiate (1:=λ _, _); simpl.
      iSplitL; [ iAccu | ].
      iAlways.
      iIntros "Hda".
      iApply block_cinv_free_pred. iExists _; iFrame. }
    iIntros "Hreserved".
    iSplit; first iFromCache.
    wpc_pures.
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros "His_locked". iNamed 1.
    wpc_pures.
    wpc_bind_seq.
    crash_lock_open "His_locked".
    iNamed 1.
    iNamed "Hlockinv".
    iCache with "Hfupd HP Hdurable".
    { iSplitL "Hfupd"; first by iFromCache.
      iExists _; iFrame.
      iExists _; iFrame. }
    iDestruct (is_slice_sz with "Haddrs") as %Hlen1.
    autorewrite with len in Hlen1.
    iDestruct (is_inode_durable_size with "Hdurable") as %Hlen2.
    wpc_call.
    wpc_bind (slice.len _ ≥ _)%E.
    wpc_frame.
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    iNamed 1.
    wpc_if_destruct.
    + wpc_pures.
      iSplitR "HP Hdurable addrs Haddrs"; last first.
      { iExists _; iFrame.
        iExists _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; first iFromCache.
      wpc_pures.
      wpc_frame_seq.
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      iNamed 1.
      wpc_pures.
      wpc_frame_seq.
      wp_apply (wp_Free _ _ _ emp with "[$Halloc Hreserved]").
      { auto. }
      { auto. }
      { iSplitL "Hreserved".
        { iApply (reserved_block_weaken with "[] [] Hreserved").
          { rewrite /Ψ. eauto. }
          { rewrite /Ψ/block_cinv. iNext. eauto. }
        }
        iIntros (σ' Hreserved) "HP".
        iMod ("Hfree_fupd" with "[//] HP") as "$".
        auto. }
      iIntros "_".
      wp_pures.
      iNamed 1.
      wpc_pures.
      iRight in "Hfupd".
      by iLeft in "Hfupd".
    + wpc_pures.
      wpc_frame_seq.
      wp_loadField.
      wp_apply (wp_SliceAppend (V:=u64) with "[$Haddrs]").
      { iPureIntro.
        word. }
      iIntros (addr_s') "Haddrs".
      Transparent slice.T.
      wp_storeField.
      Opaque slice.T.
      iNamed 1.
      wpc_pures.
      wpc_frame_seq.
      wp_apply (wp_Inode__mkHdr with "[$addrs $Haddrs]").
      { autorewrite with len; simpl.
        word. }
      iIntros (s b' extra') "(Hb&%Hencoded'&?&?)"; iNamed.
      iNamed 1.
      wpc_pures.
      wpc_bind (struct.loadF _ _ _).
      wpc_frame.
      wp_loadField.
      iNamed 1.

      iApply (prepare_reserved_block with "Hreserved"); auto; try lia.
      { solve_ndisj. }
      iSplit; first iFromCache.
      iIntros "Hda Hreserved".
      wpc_bind (Write _ _).
      (* hide this horrible postcondition for now *)
      match goal with
      | |- envs_entails _ (wpc _ _ _ _ _ ?Φ0 _) => set (Φ':=Φ0)
      end.
      wpc_apply (wpc_Write_fupd with "[$Hb]").
      iSplit.
      { iSplitR "Hda"; first iFromCache.
        iApply block_cinv_free_pred.
        iExists _; iFrame. }
      iNamed "Hdurable".
      iRight in "Hfupd".
      set (σ':=set inode.blocks (λ bs : list Block, bs ++ [b0])
                   (set inode.addrs (union {[a]}) σ)).
      iRight in "Hfupd".
      iSpecialize ("Hfupd" $! σ σ' a with "[% //] [% //]").

      iMod (mark_used _ _ _ _ _ _ (▷ P σ' ∗ (Φc ∧ Φ #true))%I with "Hreserved [HP Hfupd]") as "Hget_used".
      { solve_ndisj. }
      { clear.
        iIntros (s Hreserved) "HPalloc".
        iMod (fupd_intro_mask' _ (⊤ ∖ ↑allocN ∖ ↑inodeN)) as "HinnerN".
        { solve_ndisj. }
        iMod ("Hfupd" with "[% //] [$HP $HPalloc]") as "(HP&HPalloc&HQ)".
        iFrame. }

      iModIntro.
      iExists _; iFrame.
      iNext.
      iIntros "Hhdr".
      iMod "Hget_used" as "[ (HP&HQ) Hused]".
      iModIntro.
      iAssert (is_inode_durable addr
                 (set inode.blocks (λ bs : list Block, bs ++ [b0])
                      (set inode.addrs (union {[a]}) σ))
                 (addrs ++ [a]))
              with "[Hhdr Hdata Hda]" as "Hdurable".
      { iExists _, _; iFrame "∗ %".
        iSplitR.
        { iPureIntro.
          rewrite /inode.wf /=.
          autorewrite with len; simpl.
          word. }
        iSplitR.
        { iPureIntro.
          simpl.
          rewrite list_to_set_app_L.
          simpl.
          set_solver. }
        simpl; auto. }
      iDestruct (is_inode_durable_wf with "Hdurable") as %Hwf'.
      iCache Φc with "HQ".
      { by iLeft in "HQ". }
      match goal with
      | |- envs_entails _ ((?P ∗ _) ∧ _) =>
        iCache P with "HQ HP Hdurable"
      end.
      { iSplitL "HQ"; first iFromCache.
        iExists _; iFrame.
        iExists _; iFrame. }
      iCache (block_cinv Ψ γalloc a) with "Hused".
      { iApply block_cinv_from_used; iFrame. }
      iSplit.
      { iSplitR "Hused"; first iFromCache.
        iNext. iFromCache. }
      iIntros "Hb".
      subst Φ'; cbv beta.
      (* done applying wpc_Write_fupd *)

      wpc_pures.
      { iSplitR "Hused"; last (iNext; iFromCache).
        iSplitL "HQ"; first iFromCache.
        eauto 10 with iFrame. }
      iSplitR "Hused"; last iFromCache.
      iSplit.
      { iSplitL "HQ"; first iFromCache.
        eauto 10 with iFrame. }
      iSplitR "HP Haddrs addrs Hdurable"; last first.
      { iExists _; iFrame.
        iExists _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; first iFromCache.
      wpc_pures.
      wpc_frame_seq.
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      iNamed 1.
      wpc_pures.
      (* RALF: we are throwing away an [is_block] here. *)
      by iRight in "HQ".
Qed.

Theorem wpc_Inode__Append_triple {k E2}
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (Q: iProp Σ) (Qc: iProp Σ)
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S k) < n)%nat →
  (S (S k) < k')%nat →
  nroot.@"readonly" ## allocN →
  nroot.@"readonly" ## inodeN →
  inodeN ## allocN →
  {{{ "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "HQc" ∷ (Q -∗ Qc) ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (Qc ∧ (∀ σ σ' addr',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs ({[addr']} ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s ={⊤ ∖ ↑allocN ∖ ↑inodeN}=∗
         ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ Q))
  }}}
    Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
  {{{ Qc }}}.
Proof.
  iIntros (????? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iApply (wpc_Inode__Append (n:=n) (k':=k')); try assumption.
  iFrame "Hinode Hbdata Halloc_fupd Hfree_fupd Halloc".
  iSplit.
  { iApply "HΦ". by iLeft in "Hfupd". }
  iSplit.
  { iApply "HΦ". done. }
  iIntros "!>" (σ σ' addr' Hσ' Hσ s Hs) "HPs".
  iRight in "Hfupd".
  iMod ("Hfupd" $! _ _ _ Hσ' Hσ _ Hs with "HPs") as "($ & $ & HQ)".
  iIntros "!>". iSplit.
  { iApply "HΦ". iApply "HQc". done. }
  iApply "HΦ". done.
Qed.
End goose.
