From New.proof.sync_proof Require Import base mutex.
Local Existing Instances tokG wg_totalG rw_ghost_varG rw_ghost_wlG rw_ghost_rwmutexG  wg_auth_inG.

Unset Printing Projections.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m ∗
  (* TODO: not accurate to assume it never changes, there should be an unknown
  notifyList struct in an invariant *)
  "#?" ∷ c ↦s[sync.Cond :: "notify"]□ default_val sync.notifyList.t ∗
  "#?" ∷ c ↦s[sync.Cond :: "checker"]□ default_val sync.copyChecker.t
.
#[global] Opaque is_Cond.
#[local] Transparent is_Cond.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_pkg_init sync }}}
    @! sync.NewCond #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  rewrite -wp_fupd.
  wp_auto.
  wp_alloc c as "Hc".
  wp_pures.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  cbn [sync.Cond.L' sync.Cond.noCopy' sync.Cond.notify' sync.Cond.checker'].
  iNamed "Hl".
  iClear "HnoCopy". (* not used *)
  iPersist "HL Hchecker".
  iPersist "Hnotify".
  iFrame "#". done.
Qed.

Lemma wp_copyChecker__check c (c_v: sync.copyChecker.t) dq :
  {{{ is_pkg_init sync ∗ c ↦{dq} c_v }}}
    c @ (ptrT.id sync.copyChecker.id) @ "check" #()
  {{{ RET #(); c ↦{dq} c_v }}}.
Proof.
  wp_start as "c".
Admitted.

Lemma wp_runtime_notifyListAdd l (l_v: sync.notifyList.t) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListAdd #l
  {{{ (x: w32), RET #x; l ↦{dq} l_v }}}.
Proof.
  wp_start as "l".
  wp_apply wp_ArbitraryInt as "%".
  iApply "HΦ". by iFrame.
Qed.

Lemma wp_runtime_notifyListNotifyOne l (l_v: sync.notifyList.t) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListNotifyOne #l
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l".
  iApply "HΦ". by iFrame.
Qed.

Lemma wp_runtime_notifyListNotifyAll l (l_v: sync.notifyList.t) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListNotifyAll #l
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l".
  iApply "HΦ". by iFrame.
Qed.

Lemma wp_runtime_notifyListWait l (l_v: sync.notifyList.t) (t: w32) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListWait #l #t
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l".
  iApply "HΦ". by iFrame.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @ (ptrT.id sync.Cond.id) @ "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef @]".
  wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListNotifyOne with "[$]") as "_".
  iApply "HΦ". done.
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @ (ptrT.id sync.Cond.id) @ "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListNotifyAll with "[$]") as "_".
  iApply "HΦ". done.
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @ (ptrT.id sync.Cond.id) @ "Wait" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(@ & #Hlock & HR)". wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListAdd with "[$]") as "% _".
  iNamed "Hlock".
  wp_apply ("H_Unlock" with "[$HR]").
  wp_apply (wp_runtime_notifyListWait with "[$]") as "_".
  wp_apply ("H_Lock" with "[$]") as "HR".
  iApply "HΦ". by iFrame.
Qed.

End proof.
