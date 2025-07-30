From New.proof.sync_proof Require Import base.


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

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @ (ptrT.id sync.Cond.id) @ "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef Hc]".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @ (ptrT.id sync.Cond.id) @ "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @ (ptrT.id sync.Cond.id) @ "Wait" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(#Hcond & #Hlock & HR)".
  iNamed "Hcond".
  wp_method_call. wp_call.
  iNamed "Hlock".
  wp_auto.
  wp_apply ("H_Unlock" with "[$]").
  wp_apply ("H_Lock" with "[$]") as "?".
  iApply "HΦ". done.
Qed.

End proof.
