From Perennial.goose_lang.lib Require Import proph.proph.
From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost mvcc_action.
From Perennial.program_proof.mvcc Require Import wrbuf_proof.
From Perennial.goose_lang.trusted.github_com.mit_pdos.go_mvcc Require Import trusted_proph.

Section proph.
Context `{!heapGS Σ}.

(* FIXME: define and prove these. *)
Local Definition decode_ev_read (v : val) : option action :=
  match v with
  | (#(LitInt tid), #(LitInt key))%V => Some (EvRead (int.nat tid) key)
  | _ => None
  end.
Local Definition decode_ev_abort (v : val) : option action :=
  match v with
  | #(LitInt tid) => Some (EvAbort (int.nat tid))
  | _ => None
  end.
Local Definition decode_ev_commit (v : val) : option action :=
  (* FIXME *) None.

Local Definition decode_action (v : val) : option action :=
  match v with
  | (#(LitInt id), data)%V =>
      if bool_decide (id = EvReadId) then
        decode_ev_read data
      else if bool_decide (id = EvAbortId) then
        decode_ev_abort data
      else if bool_decide (id = EvCommitId) then
        decode_ev_commit data
      else
        None
  | _ => None
  end.
Local Fixpoint decode_actions (pvs : list val) : list action :=
  match pvs with
  | [] => []
  | v :: pvs => option_list (decode_action v) ++ decode_actions pvs
  end.

Definition mvcc_proph (γ : mvcc_names) (p : proph_id) (acs : list action) : iProp Σ :=
  ∃ (pvs : list val), ⌜decode_actions pvs = acs⌝ ∗ proph p pvs.

Global Instance mvcc_proph_timeless γ p acs :
  Timeless (mvcc_proph γ p acs).
Proof. apply _. Qed.

Lemma wp_NewProphActions γ :
  {{{ True }}}
    NewProph #()
  {{{ (p : proph_id) acs, RET #p; mvcc_proph γ p acs }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply wp_new_proph. iIntros (pvs p) "Hp".
  iApply ("HΦ" $! p (decode_actions pvs)).
  iExists _. by iFrame.
Qed.

Lemma wp_ResolveRead γ p (tid key : u64) (ts : nat) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveRead #p #tid #key @ ∅
    <<< ∃ acs', ⌜acs = EvRead ts key :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Proof.
  iIntros "!> %Φ %Hts AU". wp_lam. wp_pures.
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
  iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
  wp_apply (wp_resolve_proph with "Hp").
  iIntros (pvs') "[-> Hp]". simpl in Hpvs.
  rewrite bool_decide_true in Hpvs; last done.
  simpl in Hpvs.
  iMod ("Hclose" with "[Hp]") as "HΦ".
  { iExists (decode_actions pvs').
    rewrite Hts in Hpvs. iSplit; first done.
    iExists _. by iFrame. }
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_ResolveAbort γ p (tid : u64) (ts : nat) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = EvAbort ts :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Admitted.

Lemma wp_ResolveCommit γ p (tid : u64) (ts : nat) (wrbuf : loc) (m : dbmap) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ ∗ own_wrbuf wrbuf m }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveCommit #p #tid #wrbuf @ ∅
    <<< ∃ acs', ⌜acs = EvCommit ts m :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); own_wrbuf wrbuf m }}}.
Admitted.

End proph.

Global Typeclasses Opaque mvcc_proph.
