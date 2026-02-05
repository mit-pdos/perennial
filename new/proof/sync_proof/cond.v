From New.proof.sync_proof Require Import base mutex.

Local Unset Printing Projections.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!allG Σ}.
Context {sem : go.Semantics} {package_sem : sync.Assumptions}.
Local Set Default Proof Using "All".

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t_ok) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c.[sync.Cond.t, "L"] ↦□ (interface.ok m) ∗
  (* FIXME: not accurate to assume it never changes, there should be an unknown
  notifyList struct in an invariant *)
  "#?" ∷ c.[sync.Cond.t, "notify"] ↦□ zero_val sync.notifyList.t ∗
  "#?" ∷ c.[sync.Cond.t, "checker"] ↦□ zero_val sync.copyChecker.t
.
#[global] Opaque is_Cond.
#[local] Transparent is_Cond.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond m :
  {{{ is_pkg_init sync }}}
    @! sync.NewCond #(interface.ok m)
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  rewrite -wp_fupd.
  wp_auto.
  wp_alloc c as "Hc".
  wp_pures.
  iApply "HΦ".
  iStructNamed "Hc". simpl.
  iClear "noCopy". (* not used *)
  iPersist "L checker notify".
  iFrame "#". done.
Qed.

Lemma wp_copyChecker__check c (c_v: sync.copyChecker.t) dq :
  {{{ is_pkg_init sync ∗ c ↦{dq} c_v }}}
    c @! (go.PointerType sync.copyChecker) @! "check" #()
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
  wp_apply wp_ArbitraryInt as "% _".
  wp_end.
Qed.

Lemma wp_runtime_notifyListNotifyOne l (l_v: sync.notifyList.t) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListNotifyOne #l
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l". wp_end.
Qed.

Lemma wp_runtime_notifyListNotifyAll l (l_v: sync.notifyList.t) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListNotifyAll #l
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l". wp_end.
Qed.

Lemma wp_runtime_notifyListWait l (l_v: sync.notifyList.t) (t: w32) dq :
  {{{ is_pkg_init sync ∗ l ↦{dq} l_v }}}
   @! sync.runtime_notifyListWait #l #t
  {{{ RET #(); l ↦{dq} l_v }}}.
Proof.
  wp_start as "l". wp_end.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @! (go.PointerType sync.Cond) @! "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef @]".
  wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListNotifyOne with "[$]") as "_".
  wp_end.
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @! (go.PointerType sync.Cond) @! "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H". wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListNotifyAll with "[$]") as "_".
  wp_end.
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @! (go.PointerType sync.Cond) @! "Wait" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(@ & #Hlock & HR)". wp_auto.
  wp_apply (wp_copyChecker__check with "[$]") as "?".
  wp_apply (wp_runtime_notifyListAdd with "[$]") as "% _".
  iNamed "Hlock".
  wp_apply ("H_Unlock" with "[$HR]").
  wp_apply (wp_runtime_notifyListWait with "[$]") as "_".
  wp_apply ("H_Lock" with "[$]") as "HR".
  wp_end.
Qed.

End wps.
