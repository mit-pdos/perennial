From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import kvs.
From Perennial.program_proof Require Import txn.specs buftxn.specs.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof.

Module kvpair.
  Record t :=
    mk { key: specs.addr;
         val: defs.bufDataT defs.KindBlock
       }.
  Global Instance _eta: Settable _ := settable! mk <key; val>.
End kvpair.

Class kvsG Σ :=
  {
    kvs_bufs_pre :> gen_heapPreG specs.addr (defs.bufDataT defs.KindBlock) Σ;
    kvs_bufs :> gen_heapG specs.addr (defs.bufDataT defs.KindBlock) Σ;
  }.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!lockG Σ}.
Context `{!buftxnG Σ}.
Context `{!kvsG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Notation "l k↦ v" := (mapsto (L:=specs.addr) (V:=defs.bufDataT defs.KindBlock) l 1 v%V)
                            (at level 20, format "l k↦ v") : bi_scope.
Notation "l k↦{ q } v" := (mapsto (L:=specs.addr) (V:=defs.bufDataT defs.KindBlock) l q v%V)
                            (at level 20, q at level 50, format "l k↦{ q }  v") : bi_scope.

Fixpoint init_keys (keys: list specs.addr) (sz: nat) : list specs.addr :=
match sz with
| O => keys
| S n => init_keys ((specs.Build_addr n 0) :: keys) n
end.

Definition key2val (key: specs.addr) : val :=
  #key.(specs.addrBlock).

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : specs.addr*Slice.t): val :=
  ((key2val (fst pair)), (slice_val (snd pair), #()))%V.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_slice (slice_val: Slice.t) (ls_kvps: list kvpair.t): iProp Σ :=
  ∃ slice_kvps, is_slice slice_val (struct.t KVPair.S) 1 (kvpair_val <$> slice_kvps)
                         ∗ [∗ list] _ ↦ slice_kvp;ls_kvp ∈ slice_kvps;ls_kvps,
  let '(kvpair.mk key buf) := ls_kvp in ∃ blk,
      ⌜specs.is_bufData_at_off blk 0 buf⌝
      ∗ is_block (snd slice_kvp) blk
      ∗ ⌜fst slice_kvp = key⌝.

Definition kvpairs_match (pairs: list kvpair.t): iProp Σ :=
  [∗ list] kvp ∈ pairs, let '(kvpair.mk a b) := kvp in (a k↦ b)%I.

Definition LogSz := 513.

Definition valid_key (key: specs.addr) (sz: nat):=
  specs.valid_addr key ∧
  int.val key.(specs.addrBlock) >= int.val LogSz ∧
  int.val key.(specs.addrBlock) < int.val sz.

Definition is_kvs' (sz : nat) :=
  (∃ keys,
      ⌜keys = init_keys [] sz⌝
      ∗ [∗ list] k ∈ keys, (∃ v, k k↦ v)
  )%I.

Definition ptsto_kvs (kvsl: loc) (sz : nat): iProp Σ :=
  ( ∃ (l : loc) γ,
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γ ∗
      is_kvs' sz)%I.

Definition crashed_kvs sz kvp_ls : iProp Σ :=
  is_kvs' sz ∗ kvpairs_match kvp_ls.

Definition ptsto_kvpair (l: loc) (pair: kvpair.t) : iProp Σ :=
      ∃ bs blk, (l↦[KVPair.S :: "Key"] (key2val(pair.(kvpair.key))) ∗
                  l ↦[KVPair.S :: "Val"] (slice_val bs) ∗ is_block bs blk
                  ∗ ⌜specs.is_bufData_at_off blk 0 pair.(kvpair.val)⌝)%I.

Theorem wpc_MkKVS d (sz: nat) k E1 E2:
  {{{ True }}}
    MkKVS #d #(U64(Z.of_nat sz)) @ NotStuck; k; E1; E2
  {{{ kvsl, RET #kvsl; ptsto_kvs kvsl sz}}}
  {{{ True }}}.
Proof.
  iIntros (ϕ ϕc) "_ Hϕ".
  rewrite /MkKVS.
  wpc_pures; eauto.
  wpc_bind (super.MkFsSuper _).
Admitted.

Theorem wpc_KVS__Get kvsl sz key v:
  {{{
       ptsto_kvs kvsl sz
       ∗ ⌜valid_key key sz⌝
  }}}
    KVS__Get #kvsl (key2val(key))
  {{{(pairl: loc), RET #pairl;
     ptsto_kvs kvsl sz ∗ ptsto_kvpair pairl (kvpair.mk key v)
  }}}.
Proof.
  iIntros (ϕ) "[Hkvs %Hkey] Hϕ".
  iDestruct "Hkvs" as (l txn) "[Htxnl [Hsz [Htxn Hkvs]]]".
  destruct Hkey as [Hkaddr [Hklgsz Hsz]].
  wp_call.
  wp_loadField.
  wp_pures.
  unfold specs.valid_addr in *; unfold specs.addr2flat_z in *.
  remember(bool_decide (int.val sz < int.val key.(specs.addrBlock))) as Hszcomp.
  destruct Hszcomp; wp_pures.
  - wp_apply wp_panic.
    destruct (decide_rel Z.lt (int.val sz) (int.val key.(specs.addrBlock))); try discriminate. omega.
  - change (u64_instance.u64.(@word.add 64) (u64_instance.u64.(@word.divu 64) (u64_instance.u64.(@word.sub 64) 4096 8) 8) 2)
      with (U64 LogSz).
    remember(bool_decide (int.val _ < int.val LogSz)) as Hlgszcomp.
    destruct Hlgszcomp; wp_pures.
    * wp_apply wp_panic.
      destruct (decide_rel Z.lt _ (int.val LogSz)); try discriminate. omega.
    * wp_loadField.
      wp_apply (wp_buftxn_Begin l txn _ with "[Htxn]"); auto.
      iIntros (buftx γt) "Hbtxn".
      (*iDestruct "Hbtxn" as (l0 mT bufmap gBufmap txid) "[Htxnl0 [Hbml [Htxidl [Htxn [Hbm [Hgh [HmT [Hvalid Hmapsto]]]]]]]]".*)
      wp_let.
      wp_call.
      change (u64_instance.u64.(@word.mul 64) 4096 8) with (U64 32768).
      change (key2val key, (#0, #()))%V with (specs.addr2val (specs.Build_addr key.(specs.addrBlock) 0)).
      wp_apply (wp_BufTxn__ReadBuf buftx γt txn (specs.Build_addr key.(specs.addrBlock) 0) 32768 with "[Hbtxn Hkvs]").
      -- unfold is_kvs'. iSplitL "Hbtxn"; auto.
      unfold specs.valid_addr in *.

                  
  - iSplitL "Hbm"; auto.
    iPureIntro.
    destruct Hkey as [knat [Hknat Hkey]].
    rewrite Hknat.
    unfold abstraction.LogSz in *. simpl in *.
    admit.
    (*apply Hkey.
    Print specs.valid_addr.
    simpl. split; simpl; try word; auto.*)
  - iIntros (bptr).
    iDestruct "Hmapsto" as "[Hmaps0 Hmaps]".
    iApply "Hmapsto".
  specs.wp_BufMap__Lookup.
  wp_loadField.
  Searchabout "Begin".
  wp_pures; eauto.
  iPoseProof (wp_buftxn_Begin _ _ _ with "Htxn") as "WP_buftxn_Begin".
Admitted.

Theorem wpc_KVS__MultiPut kvsl s sz kvp_ls_before kvp_slice kvp_ls stk k E1 E2:
  {{{
       ptsto_kvs kvsl s sz
                 ∗ kvpairs_match s kvp_ls_before
                 ∗ kvpairs_slice kvp_slice kvp_ls
  }}}
    KVS__MultiPut #kvsl (slice_val kvp_slice) @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok;
      ptsto_kvs kvsl s sz ∗ kvpairs_match s kvp_ls
  }}}
  {{{ crashed_kvs s sz kvp_ls ∨ crashed_kvs s sz kvp_ls_before }}}.
Proof.
Admitted.
End heap.
