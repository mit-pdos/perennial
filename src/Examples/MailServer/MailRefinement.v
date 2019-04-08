From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Unset Implicit Arguments.

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Set Default Goal Selector "!".

Notation contents := (gmap string (Datatypes.list byte)).
Canonical Structure contentsC {m: GoModel} {wf: GoModelWf m} :=
  leibnizC contents.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ,
            ghost_mapG (discreteC contents) Σ}.

  Import Filesys.FS.
  Import GoLayer.Go.
  Import Mail.

  (* Every pointer in the abstract state should have a matching
     pointer with the same value in the concrete state. *)
  Definition MailHeapInv (σ : Mail.State) : iProp Σ :=
    ([∗ dmap] p↦v ∈ (Data.allocs σ.(heap)),
       Count_Typed_Heap.mapsto (hG := go_heap_inG) p O (fst v) (snd v))%I.

  Definition InboxLockInv (γ: gname) (n: nat) :=
    (∃ S, ghost_mapsto_auth γ (A := discreteC contents) S
      ∗ ghost_mapsto (A := discreteC contents) γ O S)%I.

  Definition MailboxStatusInterp (uid: uint64) (lk: LockRef) (γ: gname)
             (ls: MailboxStatus) (msgs: contents) :=
    (match ls with
     | MUnlocked => uint64_to_string uid ↦ Unlocked
     | MPickingUp => wlocked lk
        ∗ ∃ (S: contents), ghost_mapsto_auth γ (A := discreteC contents) S ∗ ⌜ S ⊆ msgs ⌝
     | MLocked => wlocked lk ∗ InboxLockInv γ O ∗ uint64_to_string uid ↦ Unlocked
     end)%I.

  Definition InboxInv (uid: uint64) (lk: LockRef) (γ: gname) (ls: MailboxStatus)
             (msgs: gmap.gmap string (Datatypes.list byte)) :=
    (∃ N, is_lock N lk (InboxLockInv γ) True
     ∗ MailboxStatusInterp uid lk γ ls msgs
     ∗ ([∗ map] mid ↦ msgData ∈ msgs,
        ∃ inode (n: nat), path.mk (uint64_to_string uid) mid ↦ inode
                ∗ inode ↦{n} msgData))%I.

  (* TODO: the global and lsptr should probably be partial read permissions *)
  Definition MailMsgsInv (Γ : gmap uint64 gname) (σ: Mail.State) : iProp Σ :=
    (∃ (lsptr: slice.t LockRef) ls, global ↦ Some lsptr ∗ lsptr ↦ ls ∗
     ([∗ map] uid↦lm ∈ σ.(messages),
      ∃ lk γ, ⌜ Γ !! uid = Some γ ⌝
      ∗ ⌜ List.nth_error ls uid = Some lk ⌝
      ∗ InboxInv uid lk γ (fst lm) (snd lm))%I)%I.

End refinement_triples.