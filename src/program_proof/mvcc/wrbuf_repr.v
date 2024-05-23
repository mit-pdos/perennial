From Perennial.program_proof.mvcc Require Import wrbuf_prelude.

Section repr.
Context `{!heapGS Σ}.

Definition own_wrbuf_xtpls (wrbuf : loc) (mods : dbmap) : iProp Σ :=
  ∃ (entsS : Slice.t) (ents : list wrent),
    "Hents"   ∷ wrbuf ↦[WrBuf :: "ents"] (to_val entsS) ∗
    "HentsS"  ∷ slice.own_slice entsS (structTy WrEnt) (DfracOwn 1) (wrent_to_val <$> ents) ∗
    "%HNoDup" ∷ ⌜NoDup ents.*1.*1.*1⌝ ∗
    "%Hmods"  ∷ ⌜mods = (list_to_map (wrent_to_key_dbval <$> ents))⌝.

Definition own_wrbuf
           (wrbuf : loc) (mods : dbmap) (tpls : gmap u64 loc)
  : iProp Σ :=
  ∃ (entsS : Slice.t) (ents : list wrent),
    "Hents"   ∷ wrbuf ↦[WrBuf :: "ents"] (to_val entsS) ∗
    "HentsS"  ∷ slice.own_slice entsS (structTy WrEnt) (DfracOwn 1) (wrent_to_val <$> ents) ∗
    "%HNoDup" ∷ ⌜NoDup ents.*1.*1.*1⌝ ∗
    "%Hmods"  ∷ ⌜mods = (list_to_map (wrent_to_key_dbval <$> ents))⌝ ∗
    "%Htpls"  ∷ ⌜tpls = (list_to_map (wrent_to_key_tpl <$> ents))⌝.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_wrbuf_xtpls _ _)) => unfold own_wrbuf_xtpls : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_wrbuf _ _ _)) => unfold own_wrbuf : core.

Section lemma.
Context `{!heapGS Σ}.

Lemma own_wrbuf_mods_tpls_dom wrbuf mods tpls :
  own_wrbuf wrbuf mods tpls -∗
  ⌜dom mods = dom tpls⌝.
Proof.
  iIntros "Hwrbuf".
  iNamed "Hwrbuf".
  iPureIntro.
  rewrite Hmods Htpls.
  do 2 rewrite dom_list_to_map_L.
  unfold wrent_to_key_dbval, wrent_to_key_tpl.
  f_equal.
  by do 2 rewrite -list_fmap_compose.
Qed.

Lemma NoDup_wrent_to_key_dbval (ents : list wrent) :
  NoDup ents.*1.*1.*1 ->
  NoDup (wrent_to_key_dbval <$> ents).*1.
Proof.
  intros H.
  replace (wrent_to_key_dbval <$> _).*1 with ents.*1.*1.*1; last first.
  { do 3 rewrite -list_fmap_compose. f_equal. }
  done.
Qed.

Lemma wrent_to_key_dbval_key_fmap (ents : list wrent) :
  (wrent_to_key_dbval <$> ents).*1 = ents.*1.*1.*1.
Proof.
  do 3 rewrite -list_fmap_compose.
  by apply list_fmap_ext; last done.
Qed.

End lemma.
