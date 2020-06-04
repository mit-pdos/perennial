From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import inode.

(* TODO: alloc_crash_proof must be imported early since otherwise it messes up a
bunch of things, like Z_scope, encode, and val *)
From Perennial.program_proof.examples Require Import alloc_crash_proof.
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

Definition is_inode l γ P (addr: u64) : iProp Σ :=
  ∃ (d:val) (lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr) ∗
                         "#Hlock" ∷ is_lock inodeN γ #lref (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ).

Definition pre_inode l γ P addr σ : iProp Σ :=
  ∃ (d:val) (lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "#addr" ∷ readonly (l ↦[Inode.S :: "addr"] #addr) ∗
                         "Hlock" ∷ is_free_lock γ lref ∗
                         "Hlockinv" ∷ inode_linv l addr σ ∗
                         "HP" ∷ P σ.

Theorem pre_inode_init {E} l γ P addr σ :
  pre_inode l γ P addr σ ={E}=∗ is_inode l γ P addr.
Proof.
  iNamed 1.
  iExists _, _; iFrame "#".
  iMod (alloc_lock inodeN _ _ _
                   (∃ σ, "Hlockinv" ∷ inode_linv l addr σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [Hlockinv HP]") as "$".
  { iExists _; iFrame. }
  auto.
Qed.

Global Instance is_inode_crash l addr σ :
  IntoCrash (inode_linv l addr σ) (λ _, ∃ addrs, is_inode_durable addr σ addrs)%I.
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iExists addrs.
  iFrame.
  auto.
Qed.

Global Instance is_inode_Persistent l γ P addr :
  Persistent (is_inode l γ P addr).
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

Tactic Notation "wpc_apply" "new" open_constr(lem) :=
  wpc_apply lem; iSplit; [ | try iNext ].

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
  Ltac prove_crash1 :=
    crash_case; iApply ("Hinode" with "[$]").
  iDestruct (big_sepL2_length with "Hdata") as %Hblocklen.
  rewrite /Open.
  wpc_pures; first by prove_crash1.
  wpc_apply new (wpc_Read with "Hhdr").
  { iIntros "Hhdr"; prove_crash1. }
  iIntros (s) "(Hhdr&Hs)".
  wpc_frame "HP Hdata Hhdr HΦ"; first by prove_crash1.
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

Theorem wp_Inode__Read {l γ P addr} {off: u64} Q :
  {{{ is_inode l γ P addr ∗
      (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        P σ ={⊤}=∗ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => ∃ s, is_block s 1 b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}.
Proof.
  iIntros (Φ) "(Hinode&Hfupd) HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(His_locked&Hlk)"; iNamed "Hlk".
  iNamed "Hlockinv".
  iNamed "Hdurable".
  wp_loadField.
  iDestruct (big_sepL2_length with "Hdata") as %Hlen1.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen2.
  autorewrite with len in Hlen2.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  - wp_loadField.
    iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      eauto. }
    wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr addrs Haddrs Hdata]").
    { iExists _; iFrame.
      iExists _, _; iFrame "∗ %".
      iExists _, _; iFrame "∗ %". }
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame.
    rewrite lookup_ge_None_2 //.
    rewrite -Hlen1 Hlen2.
    word.
  - wp_loadField.
    destruct (list_lookup_lt _ addrs (int.nat off)) as [addr' Hlookup].
    { word. }
    iDestruct (is_slice_split with "Haddrs") as "[Haddrs_small Haddrs]".
    wp_apply (wp_SliceGet _ _ _ _ _ addrs with "[$Haddrs_small //]").
    iIntros "Haddrs_small".
    wp_pures.
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

Theorem wp_Inode__Size {l γ P addr} (Q: u64 -> iProp Σ) :
  {{{ is_inode l γ P addr ∗
      (∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          P σ ={⊤}=∗ P σ' ∗ Q sz)
  }}}
    Inode__Size #l
  {{{ sz, RET #sz; Q sz }}}.
Proof.
  iIntros (Φ) "(Hinv & Hfupd) HΦ"; iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(Hlocked & Hinner)". iNamed "Hinner".
  iNamed "Hlockinv".
  iNamed "Hdurable".
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Haddrs_sz.
  iDestruct (big_sepL2_length with "Hdata") as %Hblocks_length.
  wp_apply wp_slice_len.
  wp_loadField.
  iMod ("Hfupd" $! σ σ addr_s.(Slice.sz) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
    rewrite /inode.size.
    autorewrite with len in Haddrs_sz.
    rewrite -Haddrs_sz //. }
  wp_apply (release_spec with "[-HQ HΦ $Hlock]").
  { iFrame "Hlocked".
    iExists σ; iFrame.
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "% ∗". }
  wp_pures.
  iApply ("HΦ" with "[$]").
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
        {l γ P addr}
        (* allocator stuff *)
        {Palloc allocN γalloc domain n}
        (Q: iProp Σ) (Qc: iProp Σ) (* TODO: thread Qc through fupd and crash *)
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S k < n)%nat →
  ↑nroot.@"readonly" ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  ↑inodeN ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  ↑nroot.@"allocator" ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  {{{ "Hinode" ∷ is_inode l γ P addr ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑Ncrash allocN ∖ ↑allocN) Palloc a) ∗
      "#Huse_fupd" ∷ □ (∀ a, use_fupd (⊤ ∖ ↑Ncrash allocN ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (∀ σ σ',
          ⌜∃ addrs', σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs (addrs' ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
         P σ ={⊤ ∖ ↑allocN}=∗ P σ' ∗ Q)
  }}}
    Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
  {{{ True }}}.
Proof.
  iIntros (???? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode".
  wpc_call; first by auto.
  iCache with "HΦ".
  { crash_case; auto. }
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
    iApply (prepare_reserved_block with "Hb"); auto.
    iSplit; first by iFromCache.
    iIntros "Hb Hreserved".
    iDeexHyp "Hb".
    iAssert (□ ∀ b0 R, int.val a d↦ b0 ∗
                       ((True -∗ Φc) ∧ R) -∗
                      Φc ∗ block_cinv Ψ γalloc a)%I as "#Hbc".
    { iIntros "!>" (b' R) "(Hb&HΦ)".
      iSplitL "HΦ".
      { crash_case; auto. }
      iApply block_cinv_free_pred.
      iExists _; iFrame. }

    iCache with "HΦ Hb".
    { iApply ("Hbc" with "[$]"). }
    wpc_apply (wpc_Write' with "[$Hb $Hbdata]").
    iSplit.
    { iIntros "[Hb|Hb]"; try iFromCache.
      iApply ("Hbc" with "[$]"). }
    iIntros "!> [Hda _]".

    iCache with "HΦ Hda"; first by (iApply ("Hbc" with "[$]")).
    wpc_pures.
    wpc_bind_seq.
    wpc_frame "Hda HΦ".
    wp_loadField.
    wp_apply (acquire_spec' with "Hlock"); first by solve_ndisj.
    iIntros "(His_locked&Hlk)"; iNamed "Hlk".
    iNamed "Hlockinv".
    iNamed "Hdurable".
    iNamed 1.

    wpc_pures.
    wpc_bind (slice.len _ ≥ _)%E.
    wpc_frame "Hda HΦ".
    wp_loadField.
    iDestruct (is_slice_sz with "Haddrs") as %Hlen1.
    iDestruct (big_sepL2_length with "Hdata") as %Hlen2.
    autorewrite with len in Hlen1.
    wp_apply wp_slice_len; wp_pures.
    iNamed 1.
    wpc_if_destruct.
    + (* don't have space, need to return block *)
      wpc_pures.
      wpc_frame "Hda HΦ".
      wp_apply (wp_Free _ _ _ emp with "[$Halloc Hreserved]").
      { admit. (* TODO: not true, Ncrash should be independent of invariant namespace *) }
      { auto. }
      { auto. }
      { iSplitL "Hreserved".
        { admit. (* XXX: can I go back to being a reserved_block? *) }
        iIntros (σ' Hreserved) "HP".
        iMod ("Hfree_fupd" with "[//] HP") as "$".
        auto. }
      iIntros "_".
      wp_pures.
      wp_loadField.
      wp_apply (release_spec' with "[$Hlock $His_locked Hhdr addrs Haddrs Hdata HP]"); first by auto.
      { iExists _; iFrame.
        iExists _, _; iFrame "∗ %".
        iExists _, _; iFrame "∗ %". }
      wp_pures.
      iNamed 1.
      (* these goals are entirely in the wrong order (should go block_cinv, then
      Φc, then Φ) *)
      iSplitR "Hda".
      { iSplit; last iFromCache.
        iRight in "HΦ".
        iApply "HΦ"; auto. }
      iApply block_cinv_free_pred.
      iExists _; iFrame.
    + wpc_pures.
      wpc_bind_seq.
      wpc_frame "HΦ Hda".
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
      wpc_frame "HΦ Hda".
      wp_apply (wp_Inode__mkHdr with "[$addrs $Haddrs]").
      { autorewrite with len; simpl.
        word. }
      iIntros (s b' extra') "(Hb&%Hencoded'&?&?)"; iNamed.
      iNamed 1.
      wpc_pures.
      wpc_bind (struct.loadF _ _ _).
      wpc_frame "HΦ Hda".
      wp_loadField.
      iNamed 1.

      wpc_bind (Write _ _).
      wpc_apply (wpc_Write_fupd _
                              ("HP" ∷ P (set inode.blocks (λ bs, bs ++ [b0])
                                            (set inode.addrs ({[a]} ∪.) σ)) ∗
                              "Hhdr" ∷ int.val addr d↦ b' ∗
                              "Hused" ∷ used_block γalloc a ∗
                              "HQ" ∷ Q) with "[$Hb Hhdr Hfupd HP Hreserved]").
      { iSplit; [ iNamedAccu | ].


        iMod (mark_used _ _ (⊤ ∖ ↑Ncrash allocN) _ _ _ (emp)%I with "Hreserved []") as "Hget_used".
        { admit. (* TODO: split up allocN and Ncrash allocN *) }
        { iIntros (σ' Hreserved) "HPalloc".
          iMod ("Huse_fupd" with "[% //] HPalloc") as "$".
          auto. }

        iModIntro.
        iExists _; iFrame.
        iNext.
        iIntros "Hda".
        iMod "Hget_used" as "[_ Hused]".
        iMod (fupd_intro_mask' _ (⊤ ∖ ↑allocN)) as "HinnerN"; first by solve_ndisj.
        iMod ("Hfupd" with "[%] [% //] HP") as "[$ HQ]".
        { eexists; eauto. }
        iMod "HinnerN" as "_".

        by iFrame. }
      iSplit; [ | iNext ].
      { iIntros "[Hcrash|Hcrash]"; iNamed; iFromCache. }
      iIntros "(Hb&Hpost)"; iNamed "Hpost".
      wpc_pures.
      wpc_bind_seq.
      iCache with "HΦ Hused".
      { iSplitL "HΦ"; first by iFromCache.
        iApply block_cinv_from_used; iFrame. }
      wpc_frame "HΦ Hused".
      wp_loadField.
      wp_apply (release_spec' with "[$Hlock $His_locked addr addrs Haddrs HP Hhdr Hdata Hda]"); auto.
      { iExists _; iFrame.
        iExists _, _; iFrame "∗ %".
        iApply wlog_assume_l; [ | iIntros (?) ].
        { rewrite /inode.wf /=.
          autorewrite with len; simpl.
          rewrite -Hlen2 Hlen1; word. }
        iExists _, _; iFrame "% ∗".
        iSplit.
        - iPureIntro.
          simpl.
          rewrite list_to_set_app_L.
          simpl.
          set_solver.
        - simpl; auto. }

      iNamed 1.
      wpc_pures.
      iDestruct (block_cinv_from_used with "Hused") as "$".
      iSplit; try iFromCache.
      iApply "HΦ"; iFrame.
Admitted.

End goose.
