From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_logic Require Import atomic.
From Goose.github_com.mit_pdos.gokv Require Import leasekv.
From Perennial.program_proof.simplepb Require Import renewable_lease.
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
           IntoVal_def := mk "" (U64 0) ;
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
Context {kvptsto: string → string → iProp Σ}.

(* Specification of Kv interface. *)
Definition is_Kv_Put (Put_fn:val) : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    Put_fn #(LitString key) #(LitString value) @ ∅
  <<< kvptsto key value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get (Get_fn:val) : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, kvptsto key value >>>
    Get_fn #(LitString key) @ ∅
  <<< kvptsto key value >>>
  {{{ RET #(LitString value); True }}}.

Definition is_Kv_ConditionalPut (CondPut_fn:val) : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    CondPut_fn #(LitString key) #(LitString expect) #(LitString value) @ ∅
  <<< kvptsto key (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(LitString (if bool_decide (expect = old_value) then "ok" else "")); True }}}.

Definition is_Kv (k:loc) : iProp Σ :=
  ∃ Put_fn Get_fn CondPut_fn,
  "#Hput" ∷ readonly (k ↦[Kv :: "Put"] Put_fn) ∗
  "#HputSpec" ∷ is_Kv_Put Put_fn ∗

  "#Hget" ∷ readonly (k ↦[Kv :: "Get"] Get_fn) ∗
  "#HgetSpec" ∷ is_Kv_Get Get_fn ∗

  "#Hcput" ∷ readonly (k ↦[Kv :: "ConditionalPut"] CondPut_fn) ∗
  "#HcputSpec" ∷ is_Kv_ConditionalPut CondPut_fn
.

(* FIXME: copies from tutorial proof *)
Fixpoint string_to_bytes (s:string): list u8 :=
  match s with
  | EmptyString => []
  | String x srest => [U8 (Ascii.nat_of_ascii x)] ++ (string_to_bytes srest)
  end
.

Definition bytes_to_string (l:list u8) : string :=
  foldl (λ s b, String (u8_to_ascii b) s) EmptyString l
.

Definition encode_cacheValue (v:string) (lease:u64) : string :=
  (bytes_to_string $ u64_le lease) ++ v.

Definition leasekvN := nroot .@ "leasekv".
Definition leaseN := leasekvN .@ "lease".
Definition invN := leasekvN .@ "inv".

Definition is_inv γ : iProp Σ :=
  inv invN (∃ kvs leases,
    "Hauth" ∷ ghost_map_auth γ 1 kvs ∗
    "Hmap" ∷ ([∗ map] k ↦ v; lease ∈ kvs ; leases,
                             kvptsto k (encode_cacheValue v lease) ∗
                             ((∃ γl, own_lease_expiration γl lease ∗
                                    is_lease leaseN γl (k ↪[γ] {#1/2} v) ∗
                                    post_lease leaseN γl (k ↪[γ] {#1/2} v)) ∨
                             (k ↪[γ] {#1/2} v)))
           )
.

Definition own_LeaseKv (k:loc) (γ:gname) : iProp Σ :=
  ∃ (cache_ptr:loc) (cache:gmap string cacheValueC.t),
  "Hcache_ptr" ∷ k ↦[LeaseKv :: "cache"] #cache_ptr ∗
  "Hcache" ∷ own_map cache_ptr 1 cache ∗
  "#Hleases" ∷ ([∗ map] k ↦ cv ∈ cache,
                  ∃ γl, is_lease leaseN γl (k ↪[γ] {#1/2} cv.(cacheValueC.v)) ∗
                        is_lease_valid_lb γl cv.(cacheValueC.l)
               )
.

Definition is_LeaseKv (k:loc) γ : iProp Σ :=
  ∃ mu (kv:loc),
  "#Hinv" ∷ is_inv γ ∗
  "#Hmu" ∷ readonly (k ↦[LeaseKv :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_LeaseKv k γ) ∗
  "#Hkv" ∷ readonly (k ↦[LeaseKv :: "kv"] #kv) ∗
  "#Hkv_is" ∷ is_Kv kv
.

Lemma wp_DecodeValue v l :
  {{{ True }}}
  DecodeValue #(str encode_cacheValue v l)
  {{{ RET (to_val (cacheValueC.mk v l)); True }}}.
Proof.
Admitted.

Lemma wp_LeaseKv__Get (k:loc) key γ :
  ⊢ {{{ is_LeaseKv k γ }}}
    <<< ∀∀ v, key ↪[γ] {#1/2} v >>>
      LeaseKv__Get #k #(LitString key) @ ↑leasekvN
    <<< key ↪[γ] {#1/2} v >>>
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
  destruct (decide (ok = true ∧ int.nat h < int.nat v.(cacheValueC.l))) as [Hvalid|Hnot].
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
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau".
    { solve_ndisj. }
    iModIntro.
    iDestruct "Hau" as (?) "[Hkey Hau]".
    clear Hlookup.
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup.
    iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
    { done. }
    iDestruct (big_sepM2_lookup_acc with "Hmap") as "[HH Hmap]".
    1-2: done.
    iDestruct "HH" as "[Hkvptsto Hrest]".
    iExists _.
    iFrame.
    iIntros "Hkvptsto".
    iSpecialize ("Hmap" with "[$]").
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
  leasekv.max #a #b
  {{{ (v:u64), RET #v; ⌜int.nat a <= int.nat v⌝ ∗ ⌜int.nat b ≤ int.nat v⌝ }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_if_destruct; iApply "HΦ"; iPureIntro; word.
Qed.

Lemma wp_EncodeValue (v:string) (l:u64) :
  {{{ True }}}
  EncodeValue (to_val (cacheValueC.mk v l))
  {{{ RET #(str encode_cacheValue v l); True }}}.
Proof.
Admitted.

Lemma wp_LeaseKv__GetAndCache (k:loc) key (cachetime:u64) γ :
  ⊢ {{{ is_LeaseKv k γ }}}
    <<< ∀∀ v, key ↪[γ] {#1/2} v >>>
      LeaseKv__GetAndCache #k #(LitString key) #cachetime @ ↑leasekvN
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
     having kvptsto for `key` from is_inv, but we can't be sure it exists
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
  2:{ (* XXX: Derive a contradiction in the case that kvptsto is not available;
         this is a bit of a strange argument, but it works. *)
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
  { done. }
  iDestruct (big_sepM2_lookup_acc with "Hmap") as "[HH Hmap]".
  1-2: done.
  iDestruct "HH" as "[Hkvptsto Hrest]".
  iApply ncfupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  iSpecialize ("Hmap" with "[$]").
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
  clear kvs Hlookup HleaseLookup.
  (* XXX copy/paste from above: *)
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto is not available;
         this is a bit of a strange argument, but it works. *)
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
  { done. }
  iDestruct (big_sepM2_insert_acc with "Hmap") as "[HH Hmap]".
  1-2: done.
  iDestruct "HH" as "[Hkvptsto Hrest]".
  iApply ncfupd_mask_intro.
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
    assert (s = s0 ∧ x = x0) as [? ?]; last subst.
    {
      unfold encode_cacheValue in Hok.
      admit. (* TODO: encoding injectivity. *)
    }

    iAssert (|={↑leaseN}=> _ ∗ _)%I with "[Hrest]" as "Hrest".
    1: shelve. (* XXX: shelving this so unification can fill in the goal when
                  specializing Hmap. *)
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hrest" as "[Hrest Hlease]".
    { solve_ndisj. }
    iMod "Hmask" as "_".

    iSpecialize ("Hmap" with "[Hkvptsto Hrest]").
    {
      iFrame "Hkvptsto". iLeft. iExact "Hrest".
    }
    Unshelve.
    3:{
      iDestruct "Hrest" as "[Hlease|Hkey]".
      { (* in this case, renew the existing lease *)
        iDestruct "Hlease" as (?) "(Hexp & #Hlease & Hpost)".
        iMod (lease_renew newLeaseExpiration with "[$] [$]") as "[Hpost Hexp]".
        { word. }
        iModIntro.
        iDestruct (lease_get_lb with "[$]") as "#Hvalid".
        iSplitL.
        { iExists _; iFrame "∗#". }
        shelve. (* XXX: shelving for later unification. *)
      }
      {
        iMod (lease_alloc with "Hkey") as (?) "(#Hlease & Hpost & Hexp)".
        iModIntro.
        iDestruct (lease_get_lb with "[$]") as "#Hvalid".
        iSplitL.
        { iExists _; iFrame "∗#". }
        shelve. (* XXX: shelving for later unification. *)
      }
    }
    2: shelve.
    iMod ncfupd_mask_subseteq as "Hmask".
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
      { iExact "Hlease". }
    }
    Unshelve.
    2:{ iExists _; iFrame "#". }
    2:{ iExists _; iFrame "#". }
    wp_pures.
    by iApply "HΦ".
  }
  { (* case: cput failed, go back to beginning of loop *)
    apply bool_decide_eq_false in Hok.
    iSpecialize ("Hmap" with "[$]").
    do 2 (rewrite insert_id; last done).
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
Admitted.

Lemma wp_LeaseKv__Put (k:loc) key value γ :
  ⊢ {{{ is_LeaseKv k γ }}}
    <<< ∀∀ old_value, key ↪[γ] {#1/2} old_value >>>
      LeaseKv__Put #k #(str key) #(str value) @ ↑leasekvN
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
     having kvptsto for `key` from is_inv, but we can't be sure it exists
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
  2:{ (* XXX: Derive a contradiction in the case that kvptsto is not available;
         this is a bit of a strange argument, but it works. *)
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
  { done. }
  iDestruct (big_sepM2_lookup_acc with "Hmap") as "[HH Hmap]".
  1-2: done.
  iDestruct "HH" as "[Hkvptsto Hrest]".
  iApply ncfupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _.
  iFrame.
  iIntros "Hkvptsto".
  iMod "Hmask" as "_".
  iSpecialize ("Hmap" with "[$]").
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
  clear kvs Hlookup HleaseLookup.
  (* XXX copy/paste from above: *)

  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  destruct (kvs !! key) eqn:Hlookup.
  2:{ (* XXX: Derive a contradiction in the case that kvptsto is not available;
         this is a bit of a strange argument, but it works. *)
    iMod ncfupd_mask_subseteq as "Hmask".
    2: iMod "Hau" as (?) "[Hkey Hau]".
    { solve_ndisj. }
    iDestruct (ghost_map_lookup with "[$] [$]") as %Hlookup2.
    exfalso. rewrite Hlookup in Hlookup2. done.
  }
  iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
  { done. }
  iDestruct (big_sepM2_insert_acc with "Hmap") as "[HH Hmap]".
  1-2: done.
  iDestruct "HH" as "[Hkvptsto Hrest]".
  iApply ncfupd_mask_intro.
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
    assert (s = s0 ∧ x = x0) as [? ?]; last subst.
    {
      unfold encode_cacheValue in Hok.
      admit. (* TODO: encoding injectivity. *)
    }

    iAssert (|NC={⊤∖∅∖↑invN}=> (_ ∗ ghost_map_auth γ 1 _ ∗ Φ #()))%I with "[Hrest Hau Hauth]" as "Hrest".
    1: shelve. (* XXX: shelving this so unification can fill in the goal when
                  specializing Hmap. *)
    iMod "Hrest" as "(Hrest & Hauth & HΦ)".

    iSpecialize ("Hmap" with "[Hkvptsto Hrest]").
    { iFrame "Hkvptsto". iRight. iExact "Hrest". }
    (* FIXME: can iAssert just the ghost_map_elem *)
    Unshelve.
    3:{
      iDestruct "Hrest" as "[Hlease|Hkey]".
      { (* in this case, expire the existing lease *)
        iDestruct "Hlease" as (?) "(Hexp & #Hlease & Hpost)".
        iMod ncfupd_mask_subseteq as "Hmask".
        2: iMod (lease_expire with "[$] [$] []") as ">Hkey".
        { solve_ndisj. }
        { iApply (is_time_lb_mono with "[$]"). word. }
        iMod "Hmask" as "_".
        iMod ncfupd_mask_subseteq as "Hmask".
        2: iMod "Hau" as (?) "[Hkey2 Hau]".
        { solve_ndisj. }
        iCombine "Hkey Hkey2" as "Hkey".
        rewrite dfrac_op_own Qp.half_half.
        iMod (ghost_map_update with "[$] [$]") as "[Hauth Hkey]".
        iDestruct "Hkey" as "[$ Hkey]".
        iMod ("Hau" with "[$] [//]") as "$".
        iFrame.
      }
      {
        iMod ncfupd_mask_subseteq as "Hmask".
        2: iMod "Hau" as (?) "[Hkey2 Hau]".
        { solve_ndisj. }
        iCombine "Hkey Hkey2" as "Hkey".
        rewrite dfrac_op_own Qp.half_half.
        iMod (ghost_map_update with "[$] [$]") as "[Hauth Hkey]".
        iDestruct "Hkey" as "[$ Hkey]".
        iMod ("Hau" with "[$] [//]") as "$".
        iFrame.
      }
    }
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
    iSpecialize ("Hmap" with "[$Hkvptsto $Hrest]").
    do 2 (rewrite insert_id; last done).
    iMod ("Hclose" with "[Hmap Hauth]") as "_".
    { iNext. repeat iExists _; iFrame. }
    iModIntro.
    iIntros "_".
    wp_pures.
    iLeft. iModIntro.
    iSplitR; first done.
    iFrame.
  }
Admitted. (* same encoding injectivity *)

End proof.
