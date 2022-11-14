From Perennial.goose_lang.lib Require Import proph.proph.
From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_action
     wrbuf_repr.
From Perennial.goose_lang.trusted.github_com.mit_pdos.go_mvcc Require Import trusted_proph.

Section proph.
Context `{!heapGS Σ}.


(** Computes a dbmap from its representation as a GooseLang value. *)
Local Definition decode_dbmap (v : val) : dbmap.
Admitted.

Local Definition decode_ev_read (v : val) : option action :=
  match v with
  | (#(LitInt tid), #(LitInt key))%V => Some (ActRead (int.nat tid) key)
  | _ => None
  end.
Local Definition decode_ev_abort (v : val) : option action :=
  match v with
  | #(LitInt tid) => Some (ActAbort (int.nat tid))
  | _ => None
  end.
Local Definition decode_ev_commit (v : val) : option action :=
  match v with
  | (#(LitInt tid), m)%V => Some (ActCommit (int.nat tid) (decode_dbmap m))
  | _ => None
  end.

Local Definition decode_action (v : val) : option action :=
  match v with
  | (#(LitInt id), data)%V =>
      if bool_decide (id = ActReadId) then
        decode_ev_read data
      else if bool_decide (id = ActAbortId) then
        decode_ev_abort data
      else if bool_decide (id = ActCommitId) then
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
    <<< ∃ acs', ⌜acs = ActRead ts key :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
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
    <<< ∃ acs', ⌜acs = ActAbort ts :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Proof.
  iIntros "!> %Φ %Hts AU". wp_lam. wp_pures.
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
  iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
  wp_apply (wp_resolve_proph with "Hp").
  iIntros (pvs') "[-> Hp]". simpl in Hpvs.
  rewrite bool_decide_false in Hpvs; last done.
  rewrite bool_decide_true in Hpvs; last done.
  simpl in Hpvs.
  iMod ("Hclose" with "[Hp]") as "HΦ".
  { iExists (decode_actions pvs').
    rewrite Hts in Hpvs. iSplit; first done.
    iExists _. by iFrame. }
  iModIntro. by iApply "HΦ".
Qed.

Local Lemma wp_WrbufToVal (wrbuf : loc) (m : dbmap) (tpls : gmap u64 loc) :
  {{{ own_wrbuf wrbuf m tpls }}}
    WrbufToVal #wrbuf
  {{{ v, RET v; ⌜decode_dbmap v = m⌝ ∗ own_wrbuf wrbuf m tpls }}}.
Proof.
Admitted.

(**
 * TO Ralf: Please just ignore [tpls].
 *)
Lemma wp_ResolveCommit
      γ p (tid : u64) (ts : nat) (wrbuf : loc)
      (m : dbmap) (tpls : gmap u64 loc) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ ∗ own_wrbuf wrbuf m tpls }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveCommit #p #tid #wrbuf @ ∅
    <<< ∃ acs', ⌜acs = ActCommit ts m :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); own_wrbuf wrbuf m tpls }}}.
Proof.
  iIntros "!> %Φ [%Hts Hm] AU". wp_lam. wp_pures.
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
  wp_apply (wp_WrbufToVal with "Hm").
  iIntros (mval) "[%Hmval Hm]".
  wp_pures.
  iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
  wp_apply (wp_resolve_proph with "Hp").
  iIntros (pvs') "[-> Hp]". simpl in Hpvs.
  rewrite bool_decide_false in Hpvs; last done.
  rewrite bool_decide_false in Hpvs; last done.
  rewrite bool_decide_true in Hpvs; last done.
  simpl in Hpvs.
  iMod ("Hclose" with "[Hp]") as "HΦ".
  { iExists (decode_actions pvs').
    rewrite Hts in Hpvs. iSplit; first naive_solver.
    iExists _. by iFrame. }
  iModIntro. by iApply "HΦ".
Qed.

End proph.

Global Typeclasses Opaque mvcc_proph.
