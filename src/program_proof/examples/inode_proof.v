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
Context `{!lockG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Let inodeN := nroot.@"inode".

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

Definition inode_linv (l:loc) (addr:u64) σ : iProp Σ :=
  ∃ (addr_s: Slice.t) (addrs: list u64),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "Hdurable" ∷ is_inode_durable addr σ addrs ∗
    "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
    "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
.

Definition inode_cinv addr σ: iProp Σ :=
  ∃ addrs, is_inode_durable addr σ addrs.

Definition is_inode l k γ P (addr: u64) : iProp Σ :=
  ∃ (d:val) (lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr) ∗
                         "#Hlock" ∷ is_crash_lock inodeN inodeN k γ #lref
                                    (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ)
                                    (∃ σ, "Hlockcinv" ∷ inode_cinv addr σ ∗ "HP" ∷ P σ).

Definition pre_inode l γ P addr σ : iProp Σ :=
  ∃ (d:val) (lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr) ∗
                         "Hlock" ∷ is_free_lock γ lref ∗
                         "Hlockinv" ∷ inode_linv l addr σ ∗
                         "HP" ∷ P σ.

(* TODO: I don't think this is possible any more, since allocating the crash
lock requires a WPC - we need to follow the init_obligation pattern *)
Theorem pre_inode_init {E} l k γ P addr σ :
  pre_inode l γ P addr σ ={E}=∗ is_inode l k γ P addr.
Proof.
Abort.

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

Global Instance is_inode_Persistent l k γ P addr :
  Persistent (is_inode l k γ P addr).
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
  int.val addr d↦ block0 -∗ is_inode_durable addr (inode.mk ∅ []) [].
Proof.
  iIntros "Hhdr".
  iExists (replicate (int.nat (4096-8)) (U8 0)), block0.
  cbv [inode.blocks big_sepL2].
  iFrame "Hhdr".
  iPureIntro.
  split_and!.
  - rewrite /inode.wf /=.
    cbv; congruence.
  - reflexivity.
  - reflexivity.
Qed.

Theorem wpc_Open k E2 {d:loc} {addr addrs σ P} :
  {{{ is_inode_durable addr σ addrs ∗ P σ }}}
    inode.Open #d #addr @ NotStuck; k; ⊤; E2
  {{{ l γ, RET #l; pre_inode l γ P addr σ }}}
  {{{ is_inode_durable addr σ addrs ∗ P σ }}}.
Proof.
  iIntros (Φ Φc) "(Hinode&HP) HΦ"; iNamed "Hinode".
  iAssert (□ (int.val addr d↦ hdr ∗
              ([∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b) ∗ P σ -∗
              is_inode_durable addr σ addrs ∗ P σ))%I as "#Hinode".
  { iIntros "!> (?&?&?)".
    iFrame.
    iExists _, _; iFrame "% ∗". }
  iDestruct (big_sepL2_length with "Hdata") as %Hblocklen.
  rewrite /Open.
  wpc_pures.
  { iApply ("Hinode" with "[$]"). }
  iCache with "HΦ Hhdr Hdata HP".
  { crash_case. iApply ("Hinode" with "[$]"). }
  wpc_apply (wpc_Read with "Hhdr").
  iSplit; [ | iNext ].
  { iIntros "Hhdr"; iFromCache. }
  iIntros (s) "(Hhdr&Hs)".
  wpc_frame "HP Hdata Hhdr HΦ".
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
  iIntros (γ lref) "Hlock".
  wp_apply wp_allocStruct; auto.
  iIntros (l) "inode".
  iDestruct (struct_fields_split with "inode") as "(d&m&addr&addrs&_)".
  iMod (readonly_alloc_1 with "d") as "#d".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "addr") as "#addr".
  iModIntro.
  iNamed 1.
  iApply "HΦ".
  iExists _, _; iFrameNamed.
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

Theorem wp_Inode__UsedBlocks {l γ P addr σ} :
  {{{ pre_inode l γ P addr σ }}}
    Inode__UsedBlocks #l
  {{{ (s:Slice.t) (addrs: list u64), RET (slice_val s);
      is_slice s uint64T 1 addrs ∗
      ⌜list_to_set addrs = σ.(inode.addrs)⌝ ∗
      (is_slice s uint64T 1 addrs -∗ pre_inode l γ P addr σ) }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  iNamed "Hlockinv".
  wp_loadField.
  iApply "HΦ".
  iDestruct (is_inode_durable_addrs with "Hdurable") as %Haddrs.
  iFrame (Haddrs) "Haddrs".
  iIntros "Hs".
  iExists _, _; iFrame "# ∗".
  iExists _, _; iFrame; auto.
Qed.

Ltac crash_lock_open H :=
  lazymatch goal with
  | [ |- envs_entails _ (wpc _ _ _ _ _ _ _) ] =>
    (* TODO: check type of H and report mismatches in LVLs *)
    iApply (use_crash_locked with H);
    [ try lia (* LVL inequality *)
    | try solve_ndisj (* Ncrash namespace *)
    | first [ reflexivity | fail 1 "applied to a value?" ] (* to_val e = None *)
    | iSplit; [ try iFromCache | ]
    ]
  end.

Theorem wpc_Inode__Read {k E2} {l γ k' P addr} {off: u64} Q :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (LVL k') γ P addr ∗
      "Hfupd" ∷ (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        P σ ={⊤ ∖ ↑inodeN}=∗ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => ∃ s, is_block s 1 b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}
    {{{ True }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode".
  wpc_call; auto.
  iCache with "HΦ".
  { crash_case; auto. }
  wpc_bind_seq.
  wpc_frame "HΦ".
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); first by set_solver.
  iIntros (γlk) "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iNamed 1.
  iCache with "HΦ Hlockinv HP".
  { iSplitL "HΦ"; first by iFromCache.
    iExists _; iFrame.
    iApply (inode_linv_to_cinv with "[$]"). }
  wpc_call.
  wpc_bind (_ ≥ _)%E.
  iNamed "Hlockinv".
  iCache with "HΦ HP Hdurable".
  { iSplitL "HΦ"; first by iFromCache.
    iExists _; iFrame.
    iExists _; iFrame. }
  iDestruct (is_inode_durable_size with "Hdurable") as %Hlen1.
  wpc_frame "HΦ Hdurable HP".
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen2.
  autorewrite with len in Hlen2.
  wp_apply wp_slice_len.
  wp_pures.
  iNamed 1.
  wpc_if_destruct.
  - iMod ("Hfupd" $! σ σ None with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      split; auto.
      rewrite lookup_ge_None_2 //.
      lia. }
    wpc_pures.
    iSplitR "HP addrs Haddrs Hdurable"; last first.
    { iExists _; iFrame.
      iExists _, _; iFrame "∗ %". }
    iIntros "His_locked".
    iSplit; last iFromCache.
    wpc_pures.
    wpc_frame "HΦ".
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    wp_pures.
    iNamed 1.
    iRight in "HΦ".
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame.
    auto.
  - destruct (list_lookup_lt _ addrs (int.nat off)) as [addr' Hlookup].
    { word. }
    iDestruct (is_slice_split with "Haddrs") as "[Haddrs_small Haddrs]".
    wpc_pures.
    wpc_bind_seq.
    wpc_frame "HΦ HP Hdurable".
    wp_loadField.
    wp_apply (wp_SliceGet _ _ _ _ _ addrs with "[$Haddrs_small //]").
    iIntros "Haddrs_small"; iNamed 1.
    wpc_pures.

  (*
    iDestruct (big_sepL2_lookup_1_some with "Hdata") as "%Hblock_lookup"; eauto.
    destruct Hblock_lookup as [b0 Hlookup2].
    iDestruct (is_slice_split with "[$Haddrs_small $Haddrs]") as "Haddrs".
    iDestruct (big_sepL2_lookup_acc with "Hdata") as "[Hb Hdata]"; eauto.
    wp_apply (wp_Read with "Hb"); iIntros (s) "[Hb Hs]".
    iSpecialize ("Hdata" with "Hb").
    wp_loadField.
    iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
    { iPureIntro; eauto. }
    wp_apply (release_spec with "[$Hlock $His_locked Hhdr addr addrs Haddrs Hdata HP]").
    { iExists _; iFrame.
      iExists _, _; iFrame "∗ %".
      iExists _, _; iFrame "% ∗". }
    wp_pures.
    iApply "HΦ"; iFrame.
    rewrite Hlookup2.
    iDestruct (is_slice_split with "Hs") as "[Hs _]".
    iExists _; iFrame.
Qed.
*)
Admitted.

Theorem wp_Inode__Size {k E2} {l k' γ P addr} (Q: u64 -> iProp Σ) (Qc: iProp Σ) :
  (S k < k')%nat →
  {{{ "Hinode" ∷ is_inode l (LVL k') γ P addr ∗
      "HQc" ∷ (∀ a, Q a -∗ Qc) ∗
      "Hfupd" ∷ ((∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          P σ ={⊤ ∖ ↑inodeN}=∗ P σ' ∗ Q sz) ∧ Qc)
  }}}
    Inode__Size #l @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ sz, RET #sz; Q sz }}}
  {{{ True }}}.
Proof.
  iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode".
  rewrite /Inode__Size.
  wpc_pures; auto.
  iCache with "HΦ"; first crash_case.
  { auto. }
  wpc_bind_seq.
  wpc_frame "HΦ".
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros (γlk) "His_locked".
  iNamed 1.
  wpc_pures.
  wpc_bind_seq.
  crash_lock_open "His_locked".
  iNamed 1.
  iNamed "Hlockinv".
  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (is_inode_durable_size with "Hdurable") as %Hblocks_length.

  iLeft in "Hfupd".
  iMod ("Hfupd" $! σ σ addr_s.(Slice.sz) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
    rewrite /inode.size.
    autorewrite with len in Haddrs_sz.
    rewrite -Haddrs_sz //. }

  iCache with "HΦ HQ HQc Hdurable HP".
  { iSplitL "HΦ"; first by iFromCache.
    iExists _; iFrame.
    iExists _; iFrame. }
  wpc_frame "HΦ HQ HQc Hdurable HP".
  wp_loadField.
  wp_apply wp_slice_len.
  iNamed 1.
  iSplitR "HP addrs Haddrs Hdurable"; last first.
  { iExists _; iFrame.
    iExists _, _; iFrame "∗ %". }
  iIntros "His_locked".
  iSplit; last iFromCache.
  wpc_pures.
  wpc_frame "HΦ".
  wp_loadField.
  wp_apply (crash_lock.release_spec with "His_locked"); auto.
  wp_pures.
  iNamed 1.
  iApply "HΦ"; iFrame.
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
  Palloc σ ={E}=∗ Palloc σ'.

(* free really means unreserve (we don't have a way to unallocate something
marked used) *)
Definition free_fupd E (Palloc: alloc.t → iProp Σ) (a:u64) : iProp Σ :=
  ∀ (σ: alloc.t),
    ⌜σ !! a = Some block_reserved⌝ -∗
  Palloc σ ={E}=∗ Palloc (<[a:=block_free]> σ).

Definition use_fupd E (Palloc: alloc.t → iProp Σ) (a: u64): iProp Σ :=
  (∀ σ : alloc.t,
      ⌜σ !! a = Some block_reserved⌝ -∗
      Palloc σ ={E}=∗ Palloc (<[a:=block_used]> σ)).

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.

Theorem wpc_Inode__Append {k E2}
        {l γ k' P addr}
        (* allocator stuff *)
        {Palloc allocN γalloc domain n}
        (Q: iProp Σ) (Qc: iProp Σ)
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S (S k)) < n)%nat →
  (S (S (S k)) < k')%nat →
  ↑nroot.@"readonly" ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  ↑inodeN ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  ↑nroot.@"allocator" ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  {{{ "Hinode" ∷ is_inode l (LVL k') γ P addr ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "HQc" ∷ (Q -∗ Qc) ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "#Huse_fupd" ∷ □ (∀ a, use_fupd (⊤ ∖ ↑inodeN ∖ ↑Ncrash allocN ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ ((∀ σ σ',
          ⌜∃ addrs', σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs (addrs' ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
         P σ ={⊤ ∖ ↑allocN}=∗ P σ' ∗ Q) ∧ Qc)
  }}}
    Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S (S (S k)))); ⊤; E2
  {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
  {{{ Qc }}}.
Proof.
  iIntros (????? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode".
  wpc_call.
  { iRight in "Hfupd"; auto. }
  iCache with "HΦ Hfupd".
  { crash_case.
    iRight in "Hfupd"; auto. }
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
    iRight in "HΦ".
    by iApply "HΦ".
  - iDestruct "Hblock" as "[_ Hb]".
    wpc_pures.
    wpc_bind_seq.
    iApply (prepare_reserved_block_reuse with "Hb"); auto.
    iSplit; first by iFromCache.
    iIntros "Hb Hreserved".
    iDeexHyp "Hb".
    iAssert (□ ∀ b0 R1 R2, int.val a d↦ b0 ∗
                       ((Qc -∗ Φc) ∧ R1) ∗
                       (R2 ∧ Qc) -∗
                      Φc ∗ block_cinv Ψ γalloc a)%I as "#Hbc".
    { iIntros "!>" (b' R1 R2) "(Hb&HΦ&Hfupd)".
      iRight in "Hfupd".
      iSplitL "HΦ Hfupd".
      {  crash_case; auto. }
      iApply block_cinv_free_pred.
      iExists _; iFrame. }

    iCache with "HΦ Hfupd Hb".
    { iApply ("Hbc" with "[$]"). }
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
    iSplit; last iFromCache.
    wpc_pures.
    wpc_bind_seq.
    wpc_frame "Hfupd HΦ".
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros (γlk) "His_locked". iNamed 1.
    wpc_pures.
    wpc_bind_seq.
    crash_lock_open "His_locked".
    iNamed 1.
    iNamed "Hlockinv".
    iCache with "HΦ Hfupd HP Hdurable".
    { iSplitL "HΦ Hfupd"; first by iFromCache.
      iExists _; iFrame.
      iExists _; iFrame. }
    iDestruct (is_slice_sz with "Haddrs") as %Hlen1.
    autorewrite with len in Hlen1.
    iDestruct (is_inode_durable_size with "Hdurable") as %Hlen2.
    wpc_call.
    wpc_bind (slice.len _ ≥ _)%E.
    wpc_frame "HΦ Hfupd HP Hdurable".
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    iNamed 1.
    wpc_if_destruct.
    + wpc_pures.
      iSplitR "HP Hdurable addrs Haddrs"; last first.
      { iExists _; iFrame.
        iExists _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; last by iFromCache.
      wpc_pures.
      wpc_bind_seq.
      wpc_frame "HΦ Hfupd".
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      iNamed 1.
      wpc_pures.
      wpc_bind (alloc.Allocator__Free _ _).
      wpc_frame "HΦ Hfupd".
      wp_apply (wp_Free _ _ _ emp with "[$Halloc Hreserved]").
      { auto. }
      { auto. }
      { auto. }
      { iSplitL "Hreserved".
        { iApply (reserved_block_weaken with "[] Hreserved").
          iIntros "!> Hda".
          iExists _; iFrame. }
        iIntros (σ' Hreserved) "HP".
        iMod ("Hfree_fupd" with "[//] HP") as "$".
        auto. }
      iIntros "_".
      iNamed 1.
      wpc_pures.
      iRight in "HΦ".
      iApply "HΦ"; auto.
    + wpc_pures.
      wpc_bind_seq.
      wpc_frame "HΦ Hfupd HP Hdurable".
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
      wpc_bind_seq.
      wpc_frame "HΦ Hfupd HP Hdurable".
      wp_apply (wp_Inode__mkHdr with "[$addrs $Haddrs]").
      { autorewrite with len; simpl.
        word. }
      iIntros (s b' extra') "(Hb&%Hencoded'&?&?)"; iNamed.
      iNamed 1.
      wpc_pures.

      wpc_bind (struct.loadF _ _ _).
      wpc_frame "HΦ Hfupd HP Hdurable".
      wp_loadField.
      iNamed 1.

      iApply (prepare_reserved_block with "Hreserved"); auto; try lia.
      { admit. (* TODO: add assumption *) }
      iSplit; first iFromCache.
      iIntros "Hda Hreserved".
      wpc_bind (Write _ _).
      iNamed "Hdurable".
      iAssert ((int.val addr d↦ hdr -∗
               ([∗ list] a0;b1 ∈ addrs;σ.(inode.blocks), int.val a0 d↦ b1) -∗
               is_inode_durable addr σ addrs))%I as "Hrestore_durable".
      { iIntros "Hhdr Hdata".
        iExists _, _; iFrame "% ∗". }
      wpc_apply (wpc_Write_fupd _
                              ("HP" ∷ P (set inode.blocks (λ bs, bs ++ [b0])
                                            (set inode.addrs ({[a]} ∪.) σ)) ∗
                              "Hhdr" ∷ int.val addr d↦ b' ∗
                              "Hused" ∷ used_block γalloc a ∗
                              "HQ" ∷ Q) with "[$Hb Hhdr Hfupd HP Hreserved]").
      { iSplit; [ iNamedAccu | ].


        iMod (mark_used _ _ _ _ _ _ (emp)%I with "Hreserved []") as "Hget_used".
        { admit. (* TODO: split up allocN and Ncrash allocN *) }
        { iIntros (σ' Hreserved) "HPalloc".
          iMod ("Huse_fupd" with "[% //] HPalloc") as "$".
          auto. }

        iModIntro.
        iExists _; iFrame.
        iNext.
        iIntros "Hhdr".
        iMod "Hget_used" as "[_ Hused]".
        iMod (fupd_intro_mask' _ (⊤ ∖ ↑allocN)) as "HinnerN".
        { admit. (* namespace issues *) }
        iMod ("Hfupd" with "[%] [% //] HP") as "[$ HQ]".
        { eexists; eauto. }
        iMod "HinnerN" as "_".

        by iFrame. }
      iSplit; [ | iNext ].
      { iIntros "[Hcrash|Hcrash]"; iNamed "Hcrash".
        - iDestruct ("Hrestore_durable" with "[$] [$]") as "Hdurable".
          iSplitR "Hda"; first iFromCache.
          iApply block_cinv_free_pred.
          iExists _; iFrame.
        - iSpecialize ("HQc" with "HQ").
          iSplitR "Hused".
          { iSplitL "HΦ HQc Hda"; first by crash_case.
            iExists _; iFrame.
            admit. (* TODO: need to prove inode_cinv (as in proof below) *) }
          iApply block_cinv_from_used; iFrame. }
      iIntros "(Hb&Hpost)"; iNamed "Hpost".
      iCache Φc with "HΦ HQ HQc".
      { iSpecialize ("HQc" with "HQ").
        by crash_case. }

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
      iCache (block_cinv Ψ γalloc a) with "Hused".
      { iApply block_cinv_from_used; iFrame. }
      iCache with "HΦ HQ HQc Hused HP Hdurable".
      { iSplitR "Hused"; last iFromCache.
        iSplitL "HΦ HQ HQc"; first iFromCache.
        iExists _; iFrame "HP".
        iExists _; iFrame. }

      wpc_pures.
      iSplitR "Hused"; last iFromCache.
      iSplit; last first.
      { iSplitL "HΦ HQ HQc"; first iFromCache.
        iExists _; iFrame.
        iExists _; iFrame. }
      iSplitR "HP Haddrs addrs Hdurable"; last first.
      { iExists _; iFrame "HP".
        iExists _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; last iFromCache.
      wpc_pures.
      wpc_bind_seq.
      wpc_frame "HΦ HQ HQc".
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      iNamed 1.
      wpc_pures.
      iApply "HΦ"; iFrame.
      Fail idtac.
Admitted.

End goose.
