From Perennial.program_proof Require Import grove_prelude marshal_stateless_proof.
From Goose.github_com.mit_pdos.gokv Require Import cachekv.
From Perennial.program_proof.vrsm Require Import renewable_lease.
From Perennial.program_proof.kv Require Import interface.
From iris.base_logic.lib Require Import ghost_map.

Module cacheValueC.
Record t :=
  mk {
      v : string ;
      l : u64 ;
    }.

#[global] Instance into_val : IntoVal t.
Proof.
  refine {| into_val.to_val := (λ (x:t),
                                 struct.mk_f cacheValue [
                                     "v" ::= #(LitString x.(v)) ;
                                     "l" ::= #x.(l)
                                   ])%V ;
           from_val := λ v, match v with (#(LitString v), (#(LitInt t), #()))%V => Some (mk v t) | _ => None end ;
           IntoVal_def := mk "" (W64 0) ;
         |}.
  intros. simpl. by destruct v0.
Defined.

#[global] Instance into_val_for_type : IntoValForType t (struct.t cacheValue).
Proof. constructor; auto. Qed.

End cacheValueC.

Section proof.
Context `{!heapGS Σ}.
Context `{!ghost_mapG Σ string string}.
Context `{!renewable_leaseG Σ}.

Definition encode_cacheValue (v:string) (lease:u64) : string :=
  (bytes_to_string $ u64_le lease) ++ v.

Lemma encode_cacheValue_inj v l v' l' :
  encode_cacheValue v l = encode_cacheValue v' l' →
  v = v' ∧
  l = l'.
Proof.
  intros H.
  rewrite /encode_cacheValue in H.
  apply (f_equal string_to_bytes) in H.
  repeat rewrite string_to_bytes_app bytes_to_string_inj in H.
  apply app_inj_1 in H.
  2:{ done. }
  destruct H as [H1 H2].
  split.
  {
    apply (f_equal bytes_to_string) in H2. repeat rewrite string_to_bytes_inj in H2. done.
  }
  apply (f_equal le_to_u64) in H1.
  repeat rewrite u64_le_to_word in H1.
  done.
Qed.

Definition cachekvN := nroot .@ "cachekv".
Definition leaseN := cachekvN .@ "lease".
Definition invN := cachekvN .@ "inv".

(* server/invariant-side key-value points-to *)
Definition s_kvptsto γ key value : iProp Σ :=
  key ↪[γ] {#1/2} value
.

Definition kvptsto γ key value : iProp Σ :=
  key ↪[γ] {#1/2} value
.

(* KV points-to for the internal kv service *)
Implicit Types kvptsto_int: string → string → iProp Σ.

Definition is_cachekv_inv kvptsto_int γ : iProp Σ :=
  inv invN (∃ kvs,
    (* This glues the two maps together *)
    "Hauth" ∷ ghost_map_auth γ 1 kvs ∗

    "Hmap" ∷ ([∗ map] k ↦ v ∈ kvs, ∃ leaseExpiration γl,
                             kvptsto_int k (encode_cacheValue v leaseExpiration) ∗
                             post_lease leaseN γl (s_kvptsto γ k v) ∗
                             own_lease_expiration γl leaseExpiration
             )
           )
.

Definition own_CacheKv (k:loc) γ : iProp Σ :=
  ∃ (cache_ptr:loc) (cache:gmap string cacheValueC.t),
  "Hcache_ptr" ∷ k ↦[CacheKv :: "cache"] #cache_ptr ∗
  "Hcache" ∷ own_map cache_ptr (DfracOwn 1) cache ∗
  "#Hleases" ∷ ([∗ map] k ↦ cv ∈ cache,
                  ∃ γl, is_lease leaseN γl (s_kvptsto γ k cv.(cacheValueC.v)) ∗
                        is_lease_valid_lb γl cv.(cacheValueC.l)
               )
.

(* TODO: allocation lemma *)

Context `{E:coPset}.
Definition is_CacheKv (k:loc) γ : iProp Σ :=
  ∃ mu kvptsto_int (kv:loc),
  "#Hinv" ∷ is_cachekv_inv kvptsto_int γ ∗
  "#Hmu" ∷ readonly (k ↦[CacheKv :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_CacheKv k γ) ∗
  "#Hkv" ∷ readonly (k ↦[CacheKv :: "kv"] #kv) ∗
  "#Hkv_is" ∷ is_Kv kv kvptsto_int E ∗
  "%Hdisj" ∷ ⌜ ↑cachekvN ## E ⌝
.

Lemma wp_DecodeValue v l :
  {{{ True }}}
  DecodeValue #(str encode_cacheValue v l)
  {{{ RET (to_val (cacheValueC.mk v l)); True }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (?) "Hptr".
  wp_pures.
  wp_load.
  rewrite /encode_cacheValue string_to_bytes_app bytes_to_string_inj.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_pures.
  wp_apply (wp_StringFromBytes with "[$]").
  iIntros "_". rewrite string_to_bytes_inj.
  wp_pures. iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_EncodeValue (v:string) (l:u64) :
  {{{ True }}}
  EncodeValue (to_val (cacheValueC.mk v l))
  {{{ RET #(str encode_cacheValue v l); True }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (?) "Hptr".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl".
  wp_store.
  wp_pures.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hv_sl".
  wp_load.
  iDestruct (own_slice_to_small with "Hv_sl") as "Hv_sl".
  wp_apply (wp_WriteBytes with "[$Hsl $Hv_sl]").
  iIntros (?) "[Hsl _]".
  wp_store.
  wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_StringFromBytes with "[$]").
  iIntros "_".
  Opaque u64_le.
  simpl. rewrite replicate_0 /=.
  rewrite bytes_to_string_app string_to_bytes_inj.
  by iApply "HΦ".
Qed.

Lemma wp_CacheKv__Get (k:loc) key γ :
  ⊢ {{{ is_CacheKv k γ }}}
    <<< ∀∀ v, kvptsto γ key v >>>
      CacheKv__Get #k #(LitString key) @ (↑cachekvN ∪ E)
    <<< kvptsto γ key v >>>
  {{{ RET #(LitString v); True }}}.
Proof.
  Opaque struct.get.
  iIntros (?) "!# #Hkv Hau".
  wp_lam.
  wp_pures.
  iNamed "Hkv".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "[$]").
  iIntros (??) "[%Hlookup Hcache]".
  wp_pures.
  wp_apply wp_GetTimeRange.
  iIntros "* %Hh %Hl Htime".
  destruct (decide (ok = true ∧ uint.nat h < uint.nat v.(cacheValueC.l))) as [Hvalid|Hnot].
  {
    (* case: cache is valid *)
    destruct Hvalid as [? Hvalid]. subst.
    apply map_get_true in Hlookup.
    iDestruct (big_sepM_lookup_acc with "Hleases") as "[#H _]".
    { done. }
    iDestruct "H" as (?) "[#Hlease #Hvalid]".
    iMod (lease_acc with "[$] [$] [$]") as "[>Hkey Hclose]".
    { done. }
    { word. }
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey2 Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_elem_agree with "[$] [$]") as %?.
    subst.
    iMod ("Hau" with "[$]") as "HΦ".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[$]") as "Htime".
    iModIntro.
    iFrame.
    wp_pures.
    Transparent struct.get. wp_pures.
    wp_if_destruct.
    2:{ exfalso. word. }
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { iFrame "HmuInv∗". iNext.
      repeat iExists _; eauto with iFrame.
    }
    wp_pures.
    by iApply "HΦ".
  }
  { (* case: cache is not valid, have to actually call Kv.Get() *)
    iFrame. iModIntro.
    wp_pures.
    wp_apply (wp_and).
    { iAccu. }
    { wp_pures. iPureIntro. instantiate (2:=(ok = true)). destruct ok.
      * by rewrite bool_decide_true.
      * by rewrite bool_decide_false.
    }
    { iIntros. Transparent struct.get. wp_pures. done. }
    iIntros "_".
    rewrite bool_decide_false.
    2:{ intros [H H2]. subst. apply Hnot. split; first done. word. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapDelete with "[$]").
    iIntros "Hcache".
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-Hau]").
    { iFrame "HmuInv∗". iNext.
      repeat iExists _.
      iFrame.
      iApply (big_sepM_subseteq with "Hleases").
      unfold map_del.
      apply delete_subseteq.
    }
    wp_pure1_credit "Hlc".
    wp_loadField.
    iNamed "Hkv_is".
    wp_loadField.
    wp_apply ("HgetSpec" with "[//]").
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iNamed "Hi".
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau".
    { solve_ndisj. }
    iModIntro.
    iDestruct "Hau" as (?) "[Hkey Hau]".
    clear Hlookup.
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "[HH Hmap]".
    1: done.
    iDestruct "HH" as (??) "(Hkvptsto & Hpost & Hexp)".
    iExists _.
    iFrame.
    iIntros "Hkvptsto".
    iSpecialize ("Hmap" with "[Hpost Hkvptsto Hexp]").
    { repeat iExists _. iFrame. }
    iMod ("Hau" with "[$]") as "HΦ".
    iMod "Hmask".
    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. repeat iExists _; iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    wp_apply wp_DecodeValue.
    wp_pures.
    iModIntro. by iApply "HΦ".
  }
  Unshelve.
  apply _.
Qed.

Lemma wp_max (a b : u64) :
  {{{ True }}}
  cachekv.max #a #b
  {{{ (v:u64), RET #v; ⌜uint.nat a <= uint.nat v⌝ ∗ ⌜uint.nat b ≤ uint.nat v⌝ }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_if_destruct; iApply "HΦ"; iPureIntro; word.
Qed.

Lemma wp_CacheKv__GetAndCache (k:loc) key (cachetime:u64) γ :
  ⊢ {{{ is_CacheKv k γ }}}
    <<< ∀∀ v, key ↪[γ] {#1/2} v >>>
      CacheKv__GetAndCache #k #(LitString key) #cachetime @ (↑cachekvN ∪ E)
    <<< key ↪[γ] {#1/2} v >>>
  {{{ RET #(LitString v); True }}}.
Proof.
  iIntros (?) "!# Hkv Hau".
  Opaque struct.get.
  wp_lam.
  wp_pures.
  iNamed "Hkv".
  wp_forBreak.
  wp_pure1_credit "Hlc".
  wp_loadField.
  iNamed "Hkv_is".
  wp_loadField.

  (* XXX: we could use the actual spec for Get() here, but that would require
     having kvptsto_int for `key` from is_inv, but we can't be sure it exists
     without seeing that (k ↪[γ] v) exists, but that would require calling
     Hau right now. We could have an "atomic_update" with the ability to
     peek at the resources, or we could actually linearize right here and use a
     prophecy variable to resolve the fact that this iteration of the loop might
     end up failing in CondPut.
   *)
  wp_apply ("HgetSpec" with "[//]").
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto_int is not available;
         this is a bit of a strange argument, but it works. *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM_lookup_acc with "Hmap") as "[HH Hmap]"; first done.
  iDestruct "HH" as (??) "(Hkvptsto & Hpost & Hexp)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  iSpecialize ("Hmap" with "[Hkvptsto Hpost Hexp]").
  { repeat iExists _. iFrame. }
  iMod ("Hclose" with "[Hmap Hauth]") as "_".
  { iNext. eauto with iFrame. }

  iModIntro. iIntros "_".
  wp_pures.
  wp_apply wp_DecodeValue.
  wp_pures.
  wp_apply wp_GetTimeRange.
  iIntros "* _ _ $".
  iModIntro.
  Transparent struct.get.
  wp_pures.
  wp_apply wp_max.
  iIntros (newLeaseExpiration) "[_ %Hineq]".
  wp_pure1_credit "Hlc".
  wp_apply wp_EncodeValue.
  wp_loadField.
  wp_loadField.

  wp_apply ("HcputSpec" with "[//]").
  clear kvs Hlookup.
  (* XXX copy/paste from above: *)
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto_int is not available;
         this is a bit of a strange argument, but it works. *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM_insert_acc with "Hmap") as "[HH Hmap]"; first done.
  iDestruct "HH" as (??) "(Hkvptsto & Hpost & Hexp)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  (* end paste *)

  destruct (bool_decide _) eqn:Hok.
  { (* case: cput succeeded *)
    apply bool_decide_eq_true in Hok.
    apply encode_cacheValue_inj in Hok as [? ?]; subst.

    (* extend/create lease *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod (lease_renew newLeaseExpiration with "[$] [$]") as "[Hpost Hexp]".
    { solve_ndisj. }
    { word. }
    iDestruct (lease_get_lb with "[$]") as "#Hvalid".
    iDestruct (post_get_lease with "[$]") as "#Hlease".
    iMod "Hmask" as "_".

    iSpecialize ("Hmap" with "[Hkvptsto Hpost Hexp]").
    { repeat iExists _. iFrame. }
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    rewrite Hlookup in Hlookup2.
    injection Hlookup2 as ?; subst.
    iMod ("Hau" with "[$]") as "HΦ".
    iMod "Hmask" as "_".
    rewrite insert_id; last done.
    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. repeat iExists _; iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    wp_loadField.
    wp_apply (acquire_spec with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapInsert with "[$]").
    { instantiate (1:=cacheValueC.mk _ _). done. }
    iIntros "Hcache".
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapGet with "[$]").
    clear Hlookup.
    iIntros (??) "[%Hlookup Hcache]".
    wp_pures.
    rewrite /map_get /typed_map.map_insert lookup_insert /= in Hlookup.
    injection Hlookup as ? ?. subst.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv ∗".
      iNext.
      repeat iExists _.
      iFrame.
      rewrite /typed_map.map_insert.
      iApply (big_sepM_insert_2 with "[Hlease] Hleases").
      { repeat iExists _; iFrame "#". }
    }
    wp_pures.
    by iApply "HΦ".
  }
  { (* case: cput failed, go back to beginning of loop *)
    apply bool_decide_eq_false in Hok.
    iSpecialize ("Hmap" with "[Hkvptsto Hexp Hpost]").
    { repeat iExists _; iFrame. }
    rewrite insert_id; last done.
    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. eauto with iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame.
  }
Qed.

Lemma wp_CacheKv__Put (k:loc) key value γ :
  ⊢ {{{ is_CacheKv k γ }}}
    <<< ∀∀ old_value, key ↪[γ] {#1/2} old_value >>>
      CacheKv__Put #k #(str key) #(str value) @ (↑cachekvN ∪ E)
    <<< key ↪[γ] {#1/2} value >>>
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "!# Hkv Hau".
  Opaque struct.get.
  wp_lam.
  wp_pures.
  iNamed "Hkv".
  wp_forBreak.
  wp_pure1_credit "Hlc".
  wp_loadField.
  iNamed "Hkv_is".
  wp_loadField.

  (* XXX: we could use the actual spec for Get() here, but that would require
     having kvptsto_int for `key` from is_inv, but we can't be sure it exists
     without seeing that (k ↪[γ] v) exists, but that would require calling
     Hau right now. We could have an "atomic_update" with the ability to
     peek at the resources, or we could actually linearize right here and use a
     prophecy variable to resolve the fact that this iteration of the loop might
     end up failing in CondPut.
   *)
  wp_apply ("HgetSpec" with "[//]").
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto_int is not available;
         this is a bit of a strange argument, but it works. *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM_lookup_acc with "Hmap") as "[HH Hmap]"; first done.
  iDestruct "HH" as (??) "(Hkvptsto & Hpost & Hexp)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  iSpecialize ("Hmap" with "[Hpost Hkvptsto Hexp]").
  { repeat iExists _; iFrame. }
  iMod ("Hclose" with "[Hmap Hauth]") as "_".
  { iNext. eauto with iFrame. }

  iModIntro. iIntros "_".
  wp_pures.
  wp_apply wp_DecodeValue.
  Transparent struct.get.
  wp_pures.
  wp_apply wp_GetTimeRange.
  iIntros "* _ %Hineq Htime".
  iDestruct (own_time_get_lb with "Htime") as "#Hlb".
  iFrame "Htime".
  iModIntro.
  Transparent struct.get.
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* case: lease is not expired, so loop *)
    iLeft.
    iSplitR; first done. iModIntro.
    iFrame.
  }

  (* case: lease is expired *)
  wp_apply wp_EncodeValue.
  wp_loadField.
  wp_loadField.

  wp_apply ("HcputSpec" with "[//]").
  clear kvs Hlookup.
  (* XXX copy/paste from above: *)

  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto_int is not available;
         this is a bit of a strange argument, but it works. *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM_insert_acc with "Hmap") as "[HH Hmap]"; first done.
  iDestruct "HH" as (??) "(Hkvptsto & Hpost & Hexp)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  (* end paste *)

  destruct (bool_decide _) eqn:Hok.
  { (* case: cput succeeded *)
    apply bool_decide_eq_true in Hok.
    apply encode_cacheValue_inj in Hok as [? ?]; subst.

    (* expire the existing lease, then make another one *)
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod (lease_expire with "[$] [$] []") as ">Hkey".
    { solve_ndisj. }
    { iApply (is_time_lb_mono with "[$]"). word. }
    iMod "Hmask" as "_".
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey2 Hau]".
    { solve_ndisj. }
    iCombine "Hkey Hkey2" as "Hkey".
    rewrite dfrac_op_own Qp.half_half.
    iMod (ghost_map_update with "[$] [$]") as "[Hauth Hkey]".
    iDestruct "Hkey" as "[Hkey Hkey2]".
    iMod ("Hau" with "[$] [//]") as "HΦ".
    iFrame.
    iMod "Hmask" as "_".
    iMod fupd_mask_subseteq as "Hmask".
    2: iMod (lease_alloc _ leaseN with "Hkey") as (?) "(#? & Hpost & Hexp)".
    { solve_ndisj. }
    iMod "Hmask".

    iSpecialize ("Hmap" with "[Hkvptsto Hpost Hexp]").
    { repeat iExists _. iFrame. }

    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. repeat iExists _; iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    iRight. iModIntro. iSplitR; first done.
    wp_pures.
    by iApply "HΦ".
  }
  {
    iSpecialize ("Hmap" with "[Hkvptsto Hpost Hexp]").
    { repeat iExists _; iFrame. }
    rewrite insert_id; last done.
    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. repeat iExists _; iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    iLeft. iModIntro.
    iSplitR; first done.
    iFrame.
  }
Qed.

End proof.
