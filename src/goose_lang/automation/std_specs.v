From Perennial.goose_lang.automation Require Import goose_lang_auto.
From diaframe.lib Require Import iris_hints.

From Perennial.goose_lang.lib Require Import
  struct typed_mem lock into_val slice typed_slice
  string
  control.impl control.
From Perennial.program_proof Require Import std_proof.

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  #[global] Instance lock_acquire_spec lk N R :
    SPEC {{ is_lock N lk R }} lock.acquire lk {{ RET #(); locked lk ∗ R }}.
  Proof.
    iStep.
    wp_apply (acquire_spec' with "[$]"); auto.
  Qed.

  #[global] Instance lock_release_spec lk N R :
    SPEC {{ is_lock N lk R ∗ locked lk ∗ R }} lock.release lk {{ RET #(); emp }}.
  Proof.
    iStep as "Hlock Hlocked HR".
    wp_apply (release_spec' with "[$Hlock $Hlocked $HR]"); auto.
  Qed.

  #[global] Instance NewSlice_spec `{!IntoVal V} `{!IntoValForType V t} E (sz: w64) :
    SPEC ⟨E⟩
        {{ emp }}
        NewSlice t #sz
        {{ s, RET (slice_val s); own_slice s t 1 (replicate (uint.nat sz) (IntoVal_def V)) }}.
  Proof.
    iSteps.
    wp_apply wp_NewSlice.
    iSteps.
  Qed.

  (* TODO: is this really a good idea? shouldn't we take the slice resource and
  not directly expose slice properties? *)
  #[global] Instance slice_len_spec (s: Slice.t) E :
    SPEC ⟨E⟩ {{ emp }} slice.len s {{ RET #s.(Slice.sz); emp }}.
  Proof. iStep. wp_apply wp_slice_len. iSteps. Qed.

  (* TODO: write hints for own_slice splitting/merging *)

  #[global] Instance StringToBytes_spec (s: string) :
   SPEC
     {{ emp }}
      impl.StringToBytes #(str s)
    {{ sl, RET (slice_val sl); own_slice sl byteT 1 (string_to_bytes s) }}.
  Proof.
    iStep. wp_apply wp_StringToBytes. iSteps.
  Qed.

  #[global] Instance SumAssumeNoOverflow_spec (x y : u64) :
    SPEC
      {{ emp }}
        std.SumAssumeNoOverflow #x #y
      {{ RET #(LitInt $ word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}.
  Proof.
    iStep. (* Careful not to call [iSteps], as this would unfold the function *)
    wp_apply wp_SumAssumeNoOverflow. iIntros (Hoverflow) "!% //".
  Qed.

  #[global] Instance Assume_spec E (cond: bool) :
    SPEC ⟨E⟩
      {{ emp }}
      Assume #cond
      {{ RET #(); ⌜cond = true⌝ }}.
  Proof. iSteps. wp_apply wp_Assume; auto. Qed.

  #[global] Instance Assert_spec E (cond: bool) :
    SPEC ⟨E⟩
      {{ ⌜cond = true⌝ }}
      Assert #cond
      {{ RET #(); emp }}.
  Proof. iSteps. wp_apply wp_Assert; auto. Qed.

  #[global] Instance Exit_spec E (v: val) :
    SPEC ⟨E⟩
        {{ emp }}
        Exit v
        {{ RET #(); False }}.
  Proof. iSteps. wp_apply wp_Exit; auto. Qed.

End goose_lang_instances.
