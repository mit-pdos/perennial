From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_logic Require Import atomic.
From Goose.github_com.mit_pdos.gokv Require Import leasekv.
From Perennial.program_proof.simplepb Require Import renewable_lease.
From Perennial.program_proof.fencing Require Import map.

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
Context `{!mapG Σ string string}.
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
Fixpoint string_le (s:string): list u8 :=
  match s with
  | EmptyString => []
  | String x srest => [U8 (Ascii.nat_of_ascii x)] ++ (string_le srest)
  end
.

Definition encode_cacheValue (v:string) (lease:u64) : string.
Admitted.

Definition leaseN := nroot .@ "lease".
Definition invN := nroot .@ "lease".

Definition is_inv γ : iProp Σ :=
  inv invN (∃ kvs leases,
    "Hmap" ∷ ([∗ map] k ↦ v; lease ∈ kvs ; leases,
                             kvptsto k (encode_cacheValue v lease) ∗
                             ((∃ γl, own_lease_expiration γl lease ∗
                                    is_lease leaseN γl (k ⤳[γ]{#1/2} v) ∗
                                    post_lease leaseN γl (k ⤳[γ]{#1/2} v)) ∨
                             (k ⤳[γ]{#1/2} v)))
           )
.

Definition own_LeaseKv (k:loc) (γ:gname) : iProp Σ :=
  ∃ (cache_ptr:loc) (cache:gmap string cacheValueC.t),
  "Hcache_ptr" ∷ k ↦[LeaseKv :: "cache"] #cache_ptr ∗
  "Hcache" ∷ own_map cache_ptr 1 cache ∗
  "#Hleases" ∷ ([∗ map] k ↦ cv ∈ cache,
                  ∃ γl, is_lease leaseN γl (k ⤳[γ]{#1/2} cv.(cacheValueC.v)) ∗
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
    <<< ∀∀ v, key ⤳[γ]{#1/2} v >>>
      LeaseKv__Get #k #(LitString key) @ ↑leaseN ∪ ↑invN
    <<< key ⤳[γ]{#1/2} v >>>
  {{{ RET #(LitString v); True }}}.
Proof.
  Opaque struct.get.
  iIntros (?) "!# Hkv Hau".
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
    iDestruct (ghost_map_points_to_agree with "[$] [$]") as %?.
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
    assert (∃ v, kvs !! key = Some v) as [? Hlookup].
    { admit. } (* FIXME: deal with infinite map domain *)
    iDestruct (big_sepM2_lookup_l_some with "Hmap") as %[? HleaseLookup].
    { done. }
    iDestruct (big_sepM2_lookup_acc with "Hmap") as "[HH Hmap]".
    1-2: done.
    iDestruct "HH" as "[Hkvptsto Hrest]".
    iAssert (⌜v0 = x⌝)%I with "[-]" as %?.
    {
      (* TODO: match up x in Hrest with v 0 from Hkey; naively, this requires
         destructing into two cases: either the lease is expired, or it isn't.
         This same annoyance showed up in the simplepb config service proof.
         Ideally, we shouldn't need to do destruct, and should be able to make
         use of the fact that---one way or another---we have access to `key ⤳ x`,
         and that's all we need.
         This will also require adjusting some masks, so we have access to the
         lease resource here.
       *)
      (* XXX: Here's a hacky solution:
         "Hrest" always directly maintains 1/4 ownership, and the other 1/4
         might be in a lease.
      *)
      admit.
    }
    subst.
    iExists _.
    iFrame.
    iIntros "Hkvptsto".
    iSpecialize ("Hmap" with "[$]").
    iMod ("Hau" with "[$]") as "HΦ".
    iMod "Hmask".
    iMod ("Hclose" with "[Hmap]") as "_".
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
Admitted.

End proof.
