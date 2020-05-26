From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import lib.into_val.

From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof Require Import disk_lib.

Definition InodeMaxBlocks: Z := 511.
Definition maxDirect: Z := 500.
Definition maxIndirect: Z := 10.
Definition indirectNumBlocks: Z := 512.

Module inode.
  Record t :=
    mk { addr: u64;
         blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; blocks>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ InodeMaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.

Hint Unfold inode.wf InodeMaxBlocks : word.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Let inodeN := nroot.@"inode".

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_indirect (a: u64) indBlock (blocks : list Block) : iProp Σ :=
  ∃ (addrs: list u64),
  "diskAddr" ∷ int.val a d↦ indBlock ∗
  "%Hlen" ∷ ⌜length(addrs) <= indirectNumBlocks⌝ ∗
  (* TODO: this does not support reading lock-free; we could make it [∃ q,
  int.val a d↦{q} b], but that wouldn't support lock-free writes if we
  implemented those *)
  "Hdata" ∷ [∗ list] a;b ∈ addrs;blocks, int.val a d↦ b
  .

Definition inode_linv (l:loc) σ : iProp Σ :=
  ∃ (direct_s indirect_s: Slice.t) (dirAddrs indAddrs: list u64) (sz: u64) (numInd: u64) (hdr: Block),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 sz] ++ (EncUInt64 <$> dirAddrs) ++ [EncUInt64 numInd] ++ (EncUInt64 <$> indAddrs))⌝ ∗
    "%Hlen" ∷ ⌜length(dirAddrs) = int.nat maxDirect ∧ length(indAddrs) = int.nat maxIndirect ∧ int.val sz < InodeMaxBlocks ∧ int.val numInd <= maxIndirect⌝ ∗
    "Hhdr" ∷ int.val σ.(inode.addr) d↦ hdr ∗
    "addr" ∷ l ↦[Inode.S :: "addr"] #σ.(inode.addr) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #sz ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 (take (int.nat sz) dirAddrs) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (int.nat numInd) indAddrs) ∗
    (* TODO: this does not support reading lock-free; we could make it [∃ q,
    int.val a d↦{q} b], but that wouldn't support lock-free writes if we
    implemented those *)
    "HdataDirect" ∷ ([∗ list] a;b ∈ dirAddrs;(take (int.nat maxDirect) σ.(inode.blocks)), int.val a d↦ b) ∗
    "HdataIndirect" ∷ [∗ list] a ∈ indAddrs, ∃ index indBlock blocks,
    ⌜a = nth index indAddrs 0⌝ ∗
    ⌜blocks = take (int.nat maxIndirect) (drop (int.nat maxDirect + (index * (int.nat indirectNumBlocks))) σ.(inode.blocks))⌝ ∗
    is_indirect a indBlock blocks
.

Definition is_inode l γ P : iProp Σ :=
  ∃ (d:val) (lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "#Hlock" ∷ is_lock inodeN γ #lref (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ).

Definition is_inode_durable σ : iProp Σ :=
  ∃ (addrs: list u64) (extra: list u8) (hdr: Block),
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (EncUInt64 <$> addrs)) ++ extra⌝ ∗
    "Hhdr" ∷ int.val σ.(inode.addr) d↦ hdr ∗
    "Hdata" ∷ [∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b.
(*
Instance is_inode_crash l σ :
  IntoCrash (inode_linv l σ) (λ _, is_inode_durable σ).
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iExists dirAddrs, indAddrs, listIndBlocks, sz, numInd. extra, hdr.
  iFrame "% ∗".
  auto.
Qed.

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

Theorem init_inode addr :
  int.val addr d↦ block0 -∗ is_inode_durable (inode.mk addr []).
Proof.
  iIntros "Hhdr".
  iExists [], (replicate (int.nat (4096-8)) (U8 0)), block0.
  cbv [inode.addr inode.blocks big_sepL2].
  iFrame "Hhdr".
  iPureIntro.
  split.
  - rewrite /inode.wf /=.
    cbv; congruence.
  - reflexivity.
Qed.

Theorem wp_Open {d:loc} {addr σ P} :
  addr = σ.(inode.addr) ->
  {{{ is_inode_durable σ ∗ P σ }}}
    inode.Open #d #addr
  {{{ l γ, RET #l; is_inode l γ P }}}.
Proof.
  intros ->.
  iIntros (Φ) "(Hinode&HP) HΦ"; iNamed "Hinode".
  iDestruct (big_sepL2_length with "Hdata") as %Hblocklen.
  wp_call.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
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
  iIntros (l) "Hinode".
  iDestruct (struct_fields_split with "Hinode") as "(d&m&addr&addrs&_)".
  iMod (readonly_alloc_1 with "d") as "#d".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (alloc_lock inodeN ⊤ _ _
                   (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [-HΦ]") as "#Hlock".
  { iExists _; iFrame.
    iExists _, _, _, _; iFrame "% ∗". }
  iModIntro.
  iApply "HΦ".
  iExists _, _; iFrame "#".
Qed.

Theorem wp_Inode__UsedBlocks {l γ P} :
  (* TODO: it would be cool to run this before allocating the lock invariant for
  the inode; we could recover a "pre-inode" and then in a purely logical step
  allocate all the lock invariants in the caller; otherwise this code can't
  return the slice literally because it'll be protected by a lock. *)
  {{{ is_inode l γ P }}}
    Inode__UsedBlocks #l
  {{{ (s:Slice.t) (addrs: list u64), RET (slice_val s);
      (* TODO: what should the spec be? this seems to help discover the
      footprint of is_durable; how do we use that? *)
      is_slice s uint64T 1 addrs }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[His_locked Hlk]"; iNamed "Hlk".
  iNamed "Hlockinv".
  wp_loadField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr addrs Haddrs Hdata]").
  { iExists _; iFrame.
    iExists _, _, _, _; iFrame "∗ %". }
  wp_pures.
Abort.

Theorem wp_Inode__Read {l γ P} {off: u64} Q :
  {{{ is_inode l γ P ∗
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
      iExists _, _, _, _; iFrame "∗ %". }
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame.
    rewrite lookup_ge_None_2 //.
    rewrite -Hlen1 Hlen2.
    word.
  - wp_loadField.
    destruct (list_lookup_lt _ addrs (int.nat off)) as [addr Hlookup].
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
      iExists _, _, _, _; iFrame "∗ %". }
    wp_pures.
    iApply "HΦ"; iFrame.
    rewrite Hlookup2.
    iDestruct (is_slice_split with "Hs") as "[Hs _]".
    iExists _; iFrame.
Qed.

Theorem wp_Inode__Size {l γ P} (Q: u64 -> iProp Σ) :
  {{{ is_inode l γ P ∗
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
    iExists _, _, _, _; iFrame "∗ %". }
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_Inode__mkHdr l addr_s addrs :
  length addrs ≤ InodeMaxBlocks ->
  {{{ "addrs" ∷ l ↦[Inode.S :: "addrs"] (slice_val addr_s) ∗
      "Haddrs" ∷ is_slice addr_s uint64T 1 addrs
  }}}
    Inode__mkHdr #l
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

Inductive AppendStatus :=
| AppendOk
| AppendFull
| AppendAgain.

Instance AppendStatus_witness : Inhabited AppendStatus := populate!.

Instance AppendStatus_eq_dec : EqDecision AppendStatus.
Proof. solve_decision. Qed.

Instance AppendStatus_val : IntoVal AppendStatus.
Proof.
  refine {| to_val := λ v, match v with
                           | AppendOk => #(U8 0)
                           | AppendAgain => #(U8 1)
                           | AppendFull => #(U8 2)
                           end;
            IntoVal_def := AppendOk;
         |}.
  abstract (intros [] []; auto; inversion 1).
Defined.

Theorem wp_Inode__Append {l γ P} (Q: AppendStatus -> iProp Σ) (a: u64) (b0: Block) :
  {{{ is_inode l γ P ∗ int.val a d↦ b0 ∗
      (∀ σ σ' (status: AppendStatus),
          ⌜(match status with
            | AppendOk => σ' = set inode.blocks (λ bs, bs ++ [b0]) σ
            (* TODO: if status is AppendAgain, still need to take ownership of a
               even if blocks don't change *)
            | _ => σ' = σ
            end) ∧
          (status = AppendFull ↔ 1 + inode.size σ > InodeMaxBlocks)⌝ -∗
        ⌜inode.wf σ⌝ -∗
         P σ ={⊤}=∗ P σ' ∗ Q status)
  }}}
    Inode__Append #l #a
  {{{ (status: AppendStatus), RET (to_val status); Q status ∗ if bool_decide (status = AppendOk) then emp else int.val a d↦ b0 }}}.
Proof.
  iIntros (Φ) "(Hinode&Ha&Hfupd) HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(His_locked&Hlk)"; iNamed "Hlk".
  iNamed "Hlockinv".
  wp_loadField.
  iDestruct (is_slice_sz with "Haddrs") as %Hlen1.
  iDestruct (big_sepL2_length with "Hdata") as %Hlen2.
  autorewrite with len in Hlen1.
  wp_apply wp_slice_len; wp_pures.
  wp_if_destruct.
  - wp_loadField.
    iMod ("Hfupd" $! σ σ AppendFull with "[%] [% //] HP") as "[HP HQ]".
    { split; auto.
      split; auto.
      intros.
      rewrite /inode.size.
      rewrite -Hlen2 Hlen1.
      word. }
    wp_apply (release_spec with "[$Hlock $His_locked Hhdr addr addrs Haddrs Hdata HP]").
    { iExists _; iFrame.
      iExists _, _, _, _; iFrame "∗ %". }
    wp_pures.
    change #(U8 2) with (to_val AppendFull).
    iApply "HΦ"; iFrame.
    rewrite bool_decide_eq_false_2; auto.
  - wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Haddrs]").
    { iPureIntro.
      word. }
    iIntros (addr_s') "Haddrs".
    Transparent slice.T.
    wp_storeField.
    Opaque slice.T.
    wp_apply (wp_Inode__mkHdr with "[$addrs $Haddrs]").
    { autorewrite with len; simpl.
      word. }
    iIntros (s b extra') "(Hb&%Hencded&?&?)"; iNamed.
    wp_loadField.
    wp_apply (wp_Write_fupd ⊤
                            ("HP" ∷ P (set inode.blocks (λ bs, bs ++ [b0]) σ) ∗
                            "Hhdr" ∷ int.val σ.(inode.addr) d↦ b ∗
                            "HQ" ∷ Q AppendOk) with "[$Hb Hhdr Hfupd HP]").
    { iMod ("Hfupd" $! σ _ AppendOk with "[%] [% //] HP") as "[HP HQ]".
      { split; eauto.
        split; try congruence.
        rewrite /inode.size.
        rewrite -Hlen2 Hlen1; word. }
      iExists hdr; iFrame.
      iModIntro. iNext.
      by iIntros "$". }
    iIntros "(Hs&Hpost)"; iNamed "Hpost".
    wp_loadField.
    wp_apply (release_spec with "[$Hlock $His_locked addr addrs Haddrs HP Hhdr Hdata Ha]").
    { iExists _; iFrame.
      iExists _, _, _, _; iFrame "∗ %".
      iSplitR.
      - iPureIntro.
        rewrite /inode.wf /=.
        autorewrite with len; simpl.
        rewrite -Hlen2 Hlen1; word.
      - simpl.
        iApply (big_sepL2_app with "[$Hdata] [Ha]").
        simpl; iFrame. }
    wp_pures.
    change #(U8 0) with (to_val AppendOk).
    iApply "HΦ"; iFrame.
    rewrite bool_decide_eq_true_2; auto.
Qed.
*)
End goose.
