From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  ktcore safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import base.

Module server.

Module StartReply.
Record t :=
  mk' {
    PrevEpochLen: w64;
    PrevLink: list w8;
    ChainProof: list w8;
    LinkSig: list w8;
    VrfPk: list w8;
    VrfSig: list w8;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(PrevEpochLen) ++
  safemarshal.Slice1D.pure_enc obj.(PrevLink) ++
  safemarshal.Slice1D.pure_enc obj.(ChainProof) ++
  safemarshal.Slice1D.pure_enc obj.(LinkSig) ++
  safemarshal.Slice1D.pure_enc obj.(VrfPk) ++
  safemarshal.Slice1D.pure_enc obj.(VrfSig).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(PrevLink) ∧
  safemarshal.Slice1D.valid obj.(ChainProof) ∧
  safemarshal.Slice1D.valid obj.(LinkSig) ∧
  safemarshal.Slice1D.valid obj.(VrfPk) ∧
  safemarshal.Slice1D.valid obj.(VrfSig).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_PrevLink sl_ChainProof sl_LinkSig sl_VrfPk sl_VrfSig,
  "Hstruct" ∷ ptr ↦{d} (server.StartReply.mk obj.(PrevEpochLen) sl_PrevLink sl_ChainProof sl_LinkSig sl_VrfPk sl_VrfSig) ∗

  "Hsl_PrevLink" ∷ sl_PrevLink ↦*{d} obj.(PrevLink) ∗
  "Hsl_ChainProof" ∷ sl_ChainProof ↦*{d} obj.(ChainProof) ∗
  "Hsl_LinkSig" ∷ sl_LinkSig ↦*{d} obj.(LinkSig) ∗
  "Hsl_VrfPk" ∷ sl_VrfPk ↦*{d} obj.(VrfPk) ∗
  "Hsl_VrfSig" ∷ sl_VrfSig ↦*{d} obj.(VrfSig).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.StartReplyEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.StartReplyDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End StartReply.

Module PutArg.
Record t :=
  mk' {
    Uid: w64;
    Pk: list w8;
    Ver: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(Uid) ++
  safemarshal.Slice1D.pure_enc obj.(Pk) ++
  safemarshal.w64.pure_enc obj.(Ver).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(Pk).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_Pk,
  "Hstruct" ∷ ptr ↦{d} (server.PutArg.mk obj.(Uid) sl_Pk obj.(Ver)) ∗

  "Hsl_Pk" ∷ sl_Pk ↦*{d} obj.(Pk).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.PutArgEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.PutArgDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End PutArg.

Module HistoryArg.
Record t :=
  mk' {
    Uid: w64;
    PrevEpoch: w64;
    PrevVerLen: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(Uid) ++
  safemarshal.w64.pure_enc obj.(PrevEpoch) ++
  safemarshal.w64.pure_enc obj.(PrevVerLen).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (server.HistoryArg.mk obj.(Uid) obj.(PrevEpoch) obj.(PrevVerLen)).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.HistoryArgEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.HistoryArgDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End HistoryArg.

Module MembSlice1D.
Definition t := list ktcore.Memb.t.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc (length obj) ++ mjoin (ktcore.Memb.pure_enc <$> obj).

Definition valid (obj : t) :=
  sint.Z (W64 (length obj)) = length obj ∧
  Forall (λ x, ktcore.Memb.valid x) obj.

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr0,
  ptr ↦*{d} ptr0 ∗
  ([∗ list] ptr;obj ∈ ptr0;obj,
    ktcore.Memb.own ptr obj d).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.MembSlice1DEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.MembSlice1DDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End MembSlice1D.

Module HistoryReply.
Record t :=
  mk' {
    ChainProof: list w8;
    LinkSig: list w8;
    Hist: list ktcore.Memb.t;
    Bound: ktcore.NonMemb.t;
    Err: w64;
  }.

Definition pure_enc obj :=
  safemarshal.Slice1D.pure_enc obj.(ChainProof) ++
  safemarshal.Slice1D.pure_enc obj.(LinkSig) ++
  MembSlice1D.pure_enc obj.(Hist) ++
  ktcore.NonMemb.pure_enc obj.(Bound) ++
  safemarshal.w64.pure_enc obj.(Err).

Definition valid obj :=
  safemarshal.Slice1D.valid obj.(ChainProof) ∧
  safemarshal.Slice1D.valid obj.(LinkSig) ∧
  MembSlice1D.valid obj.(Hist) ∧
  ktcore.NonMemb.valid obj.(Bound).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_ChainProof sl_LinkSig ptr_Hist ptr_Bound,
  "Hstruct" ∷ ptr ↦{d} (server.HistoryReply.mk sl_ChainProof sl_LinkSig ptr_Hist ptr_Bound obj.(Err)) ∗

  "Hsl_ChainProof" ∷ sl_ChainProof ↦*{d} obj.(ChainProof) ∗
  "Hsl_LinkSig" ∷ sl_LinkSig ↦*{d} obj.(LinkSig) ∗
  "Hown_Hist" ∷ MembSlice1D.own ptr_Hist obj.(Hist) d ∗
  "Hown_Bound" ∷ ktcore.NonMemb.own ptr_Bound obj.(Bound) d.

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.HistoryReplyEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.HistoryReplyDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End HistoryReply.

Module AuditArg.
Record t :=
  mk' {
    PrevEpochLen: w64;
  }.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc obj.(PrevEpochLen).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  "Hstruct" ∷ ptr ↦{d} (server.AuditArg.mk obj.(PrevEpochLen)).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.AuditArgEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.AuditArgDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End AuditArg.

Module AuditProofSlice1D.
Definition t := list ktcore.AuditProof.t.

Definition pure_enc obj :=
  safemarshal.w64.pure_enc (length obj) ++ mjoin (ktcore.AuditProof.pure_enc <$> obj).

Definition valid (obj : t) :=
  sint.Z (W64 (length obj)) = length obj ∧
  Forall (λ x, ktcore.AuditProof.valid x) obj.

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr0,
  ptr ↦*{d} ptr0 ∗
  ([∗ list] ptr;obj ∈ ptr0;obj,
    ktcore.AuditProof.own ptr obj d).

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! ktcore.AuditProofSlice1DEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! ktcore.AuditProofSlice1DDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End AuditProofSlice1D.

Module AuditReply.
Record t :=
  mk' {
    P: list ktcore.AuditProof.t;
    Err: w64;
  }.

Definition pure_enc obj :=
  AuditProofSlice1D.pure_enc obj.(P) ++
  safemarshal.w64.pure_enc obj.(Err).

Definition valid obj :=
  AuditProofSlice1D.valid obj.(P).

Definition wish b obj tail :=
  b = pure_enc obj ++ tail ∧
  valid obj.

Lemma wish_det tail0 tail1 obj0 obj1 {b} :
  wish b obj0 tail0 →
  wish b obj1 tail1 →
  obj0 = obj1 ∧ tail0 = tail1.
Proof. Admitted.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr_P,
  "Hstruct" ∷ ptr ↦{d} (server.AuditReply.mk ptr_P obj.(Err)) ∗

  "Hown_P" ∷ AuditProofSlice1D.own ptr_P obj.(P) d.

Lemma wp_enc obj sl_b b ptr_obj d :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦* b ∗
    "Hcap_b" ∷ own_slice_cap w8 sl_b 1 ∗
    "Hown_obj" ∷ own ptr_obj obj d
  }}}
  @! server.AuditReplyEncode #sl_b #ptr_obj
  {{{
    sl_b', RET #sl_b';
    let b' := b ++ pure_enc obj in
    sl_b' ↦* b' ∗
    own_slice_cap w8 sl_b' 1 ∗
    own ptr_obj obj d ∗
    ⌜wish b' obj b⌝
  }}}.
Proof. Admitted.

Lemma wp_dec sl_b d b :
  {{{
    is_pkg_init server ∗
    "Hsl_b" ∷ sl_b ↦*{d} b
  }}}
  @! server.AuditReplyDecode #sl_b
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, #sl_tail, #err);
    match err with
    | true => ¬ ∃ obj tail, ⌜wish b obj tail⌝
    | false =>
      ∃ obj tail,
      own ptr_obj obj d ∗
      sl_tail ↦*{d} tail ∗
      ⌜wish b obj tail⌝
    end
  }}}.
Proof. Admitted.

End proof.
End AuditReply.

End server.
