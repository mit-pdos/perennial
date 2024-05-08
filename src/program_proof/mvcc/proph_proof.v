From Perennial.goose_lang.lib Require Import proph.proph.
From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_action
     wrbuf_prelude wrbuf_repr.
From Perennial.goose_lang.trusted.github_com.mit_pdos.vmvcc Require Import trusted_proph.

Section proph.
Context `{!heapGS Σ}.

(** Computes a dbmap from its representation as a GooseLang value.
If decoding fails, returns some arbitrary nonsense value. *)
Local Fixpoint decode_dbmap (v : val) : dbmap :=
  match v with
  | (#(LitInt key), #(LitBool present), #(LitString str'), tail)%V => <[key:=to_dbval present str']> (decode_dbmap tail)
  | _ => ∅
  end.

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
  iIntros (Φ) "_ HΦ". wp_call.
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


Local Lemma nodup_take (l : list u64) n :
  NoDup l → NoDup (take n l).
Proof.
  rewrite -{1}(take_drop n l). intros Hl%NoDup_app. naive_solver.
Qed.

Local Lemma wrents_to_key_dbval (ents : list wrent) :
  ents.*1.*1.*1 = (wrent_to_key_dbval <$> ents).*1.
Proof.
  rewrite -!list_fmap_compose. apply list_fmap_ext. intros ? [[[??]?]?]. done.
Qed.

Local Lemma wp_WrbufToVal (wrbuf : loc) (m : dbmap) (tpls : gmap u64 loc) :
  {{{ own_wrbuf wrbuf m tpls }}}
    WrbufToVal #wrbuf
  {{{ v, RET v; ⌜decode_dbmap v = m⌝ ∗ own_wrbuf wrbuf m tpls }}}.
Proof.
  iIntros "%Φ Hwrbuf HΦ". wp_call.
  wp_apply wp_alloc_untyped. { done. }
  iIntros (l) "Hl". wp_apply (wp_store with "Hl"). iIntros "Hl". wp_pures.
  iNamed "Hwrbuf". wp_loadField. wp_pures.
  iDestruct (own_slice_split with "HentsS") as "[HentsS HentsC]".
  wp_apply (wp_forSlice (λ i, ∃ m' v,
    ⌜decode_dbmap v = m' ∧ m' = list_to_map (wrbuf_prelude.wrent_to_key_dbval <$> (take (int.nat i) ents))⌝ ∗ l ↦ v
  )%I with "[] [Hl $HentsS]").
  2:{ iExists ∅, _. iFrame. iPureIntro. split; done. }
  { clear Φ. iIntros (i ent Φ) "!# (I & %Hi & %Hent) HΦ".
    iDestruct "I" as (m' v) "([%Hdecode %Hm'] & Hl)".
    wp_pures. rewrite ->list_lookup_fmap in Hent.
    destruct (ents !! int.nat i) as [[[[key str'] present] tpl]|] eqn:Hent'.
    2:{ exfalso. done. }
    rewrite /= /wrent_to_val /= in Hent. inversion_clear Hent. wp_pures.
    wp_apply (wp_load with "Hl"). iIntros "Hl".
    wp_apply (wp_store with "Hl"). iIntros "Hl".
    iApply "HΦ". iExists (<[key:=to_dbval present str']> m'), _. iFrame "Hl". iPureIntro. split.
    - simpl. rewrite Hdecode. done.
    - replace (int.nat (i64_instance.i64.(word.add) i 1)) with (S (int.nat i)) by word.
      erewrite take_S_r; last done.
      rewrite fmap_app list_to_map_app -Hm' /=.
      rewrite [_ m']insert_union_singleton_r //.
      apply not_elem_of_dom. rewrite Hm'. rewrite dom_list_to_map_L.
      apply not_elem_of_list_to_set. apply NoDup_app_singleton.
      rewrite wrents_to_key_dbval in HNoDup.
      apply (nodup_take _ (S (int.nat i))) in HNoDup.
      erewrite take_S_r in HNoDup.
      2:{ rewrite !list_lookup_fmap Hent' //. }
      rewrite !fmap_take. exact HNoDup. }
  iIntros "(I & HentsS)".
  iDestruct "I" as (m' v) "([%Hdecode %Hm'] & Hl)".
  iDestruct (own_slice_small_sz with "HentsS") as %HentsLen.
  rewrite -HentsLen in Hm'. clear HentsLen.
  rewrite take_ge in Hm'.
  2:{ rewrite fmap_length. done. }
  rewrite -Hmods in Hm'. subst m'.
  wp_apply (wp_load with "Hl"). iIntros "Hl".
  iApply "HΦ".
  iSplitR; first done.
  rewrite /own_wrbuf. eauto with iFrame.
Qed.

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
