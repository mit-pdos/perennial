From New.proof.sync_proof Require Import base mutex.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m.
#[global] Opaque is_Cond.
#[local] Transparent is_Cond.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_pkg_init sync }}}
    sync @ "NewCond" #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_auto.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  iNamed "Hl".
  iPersist "HL".
  iFrame "#". done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef Hc]".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @ sync @ "Cond'ptr" @ "Wait" #()
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
