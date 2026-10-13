/-
A prototype of the Go-level layer over the byte memory (`ByteMem`, `Lang.lean`;
program logic in `GooseLang/ByteLifting.lean`; layouts in `Golang/Defn/ByteRepr.lean`).

* A. Typed points-to over bytes (`typedBytes`): agreement, padding-free types,
  and the field split of a struct, which makes a field reference a concrete
  byte offset.
* B. Strings as heap objects: a string is its header `(ptr, len)` and its
  frozen bytes (`isString`); literals, contents, `==`, `+`, indexing.
* (Interfaces: see `Golang/Defn/StaticImage.lean` and
  `Golang/Theory/StaticIface.lean`, over the program image's static descriptors.)
* D. Funcs as code pointers (`isFunc`): calling through a func pointer.
* E. `unsafe.Add`: computing a field address within an allocation block.
-/
module

public import Perennial.Golang.Theory.Pre
public import Perennial.GooseLang.ByteLifting
public import Perennial.Golang.Defn.ByteRepr

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

set_option linter.unusedSectionVars false

/-! ## Byte addresses -/

theorem byteAddr_add (a : w64) (n m : Nat) : byteAddr (byteAddr a n) m = byteAddr a (n + m) := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## A. Typed points-to over bytes -/

/- The byte-memory lemmas (`ByteLifting.lean`) are stated under the GooseLang
ghost state, so this file works under `HeapGS` throughout. -/
section typed
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

open ProofMode

/-- The bytes at `a` decode to `v` (padding bytes may be anything). -/
def typedBytes (a : w64) (dq : DFrac) {V : Type} [ByteRepr V] (v : V) : IProp GF :=
  iprop(∃ bs, ⌜ByteRepr.decode bs = some v⌝ ∗ a ↦∗{dq} bs)

variable {V : Type} [ByteRepr V]

theorem typedBytes_agree (a : w64) (dq1 dq2 : DFrac) (v1 v2 : V) :
    typedBytes (GF := GF) a dq1 v1 ∗ typedBytes a dq2 v2 ⊢ ⌜v1 = v2⌝ := by
  unfold typedBytes
  iintro ⟨⟨%bs1, %h1, H1⟩, ⟨%bs2, %h2, H2⟩⟩
  have hl : bs1.length = bs2.length := by
    rw [ByteRepr.length_of_decode _ _ h1, ByteRepr.length_of_decode _ _ h2]
  ihave %heq := bytesPointsto_agree a dq1 dq2 bs1 bs2 hl $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  subst heq
  ipureintro
  exact ByteRepr.decode_inj_of_eq h1 h2

theorem typedBytes_of_bytes (a : w64) (dq : DFrac) (v : V) :
    a ↦∗{dq} ByteRepr.encode v ⊢ typedBytes (GF := GF) a dq v := by
  unfold typedBytes
  iintro H
  iexists ByteRepr.encode v
  iframe H
  ipureintro
  exact ByteRepr.decode_encode v

/-- For a type whose only encoding of `v` is `encode v` (no padding, no
non-canonical bytes), typed ownership is ownership of `encode v`. -/
theorem typedBytes_eq_encode (a : w64) (dq : DFrac) (v : V)
    (hcanon : ∀ bs, ByteRepr.decode bs = some v → bs = ByteRepr.encode v) :
    typedBytes (GF := GF) a dq v ⊣⊢ a ↦∗{dq} ByteRepr.encode v := by
  constructor
  · unfold typedBytes
    iintro ⟨%bs, %h, H⟩
    rw [hcanon bs h] at *
    iexact H
  · exact typedBytes_of_bytes a dq v

theorem typedBytes_w64 (a : w64) (dq : DFrac) (v : w64) :
    typedBytes (GF := GF) a dq v ⊣⊢ a ↦∗{dq} ByteRepr.encode v :=
  typedBytes_eq_encode a dq v fun bs => (ByteRepr.w64_decode_iff_eq_encode bs v).mp

theorem typedBytes_goStrHdr (a : w64) (dq : DFrac) (v : GoStrHdr) :
    typedBytes (GF := GF) a dq v ⊣⊢ a ↦∗{dq} ByteRepr.encode v :=
  typedBytes_eq_encode a dq v fun bs => (ByteRepr.goStrHdr_decode_iff_eq_encode bs v).mp

/-- Ownership of `n` bytes with arbitrary contents (padding). -/
def anyBytes (a : w64) (dq : DFrac) (n : Nat) : IProp GF :=
  iprop(∃ bs, ⌜bs.length = n⌝ ∗ a ↦∗{dq} bs)

theorem bytesPointsto_app4 (a : w64) (dq : DFrac) (l1 l2 l3 l4 : List w8) :
    bytesPointsto (GF := GF) a dq (l1 ++ l2 ++ l3 ++ l4) ⊣⊢
      a ↦∗{dq} l1 ∗ byteAddr a l1.length ↦∗{dq} l2 ∗
        byteAddr a (l1.length + l2.length) ↦∗{dq} l3 ∗
        byteAddr a (l1.length + l2.length + l3.length) ↦∗{dq} l4 := by
  rw [(bytesPointsto_app (GF := GF) a dq (l1 ++ l2 ++ l3) l4).to_eq,
    (bytesPointsto_app (GF := GF) a dq (l1 ++ l2) l3).to_eq,
    (bytesPointsto_app (GF := GF) a dq l1 l2).to_eq,
    List.length_append, List.length_append, List.length_append]
  constructor
  · iintro ⟨⟨⟨H1, H2⟩, H3⟩, H4⟩
    iframe
  · iintro ⟨H1, H2, H3, H4⟩
    iframe

/-- The `n`-th byte of a range. -/
theorem bytesPointsto_lookup (a : w64) (dq : DFrac) (bs : List w8) (n : Nat) (hn : n < bs.length) :
    bytesPointsto (GF := GF) a dq bs ⊢ byteAddr a n ↦∗{dq} [bs[n]] := by
  have hsplit : bs = bs.take n ++ ([bs[n]] ++ bs.drop (n + 1)) := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hn, List.take_append_drop]
  have hl : (bs.take n).length = n := by simp only [List.length_take]; omega
  conv => lhs; rw [hsplit]
  rw [(bytesPointsto_app (GF := GF) _ _ _ _).to_eq, (bytesPointsto_app (GF := GF) _ _ _ _).to_eq, hl]
  iintro ⟨-, H, -⟩
  iexact H

section prod
variable {A B : Type} [ByteRepr A] [ByteRepr B]

/-- The field split of a struct of an `A` and a `B`: its first field at offset
0, its second at `fieldOffset2 A B`, and the padding after each. This is how a
struct field reference (`structFieldRef`) becomes a concrete byte offset. -/
theorem typedBytes_prod (a : w64) (dq : DFrac) (x : A) (y : B) :
    typedBytes (GF := GF) a dq (x, y) ⊣⊢
      typedBytes a dq x ∗
      anyBytes (byteAddr a (ByteRepr.size A)) dq
        (ByteRepr.fieldOffset2 A B - ByteRepr.size A) ∗
      typedBytes (byteAddr a (ByteRepr.fieldOffset2 A B)) dq y ∗
      anyBytes (byteAddr a (ByteRepr.fieldOffset2 A B + ByteRepr.size B)) dq
        (ByteRepr.size (A × B) - (ByteRepr.fieldOffset2 A B + ByteRepr.size B)) := by
  have h1 := ByteRepr.prod_fieldOffset2_ge (A := A) (B := B)
  have h2 := ByteRepr.prod_fieldOffset2_add_le (A := A) (B := B)
  unfold typedBytes anyBytes
  constructor
  · iintro ⟨%bs, %h, H⟩
    obtain ⟨hlen, hx, hy⟩ := (ByteRepr.prod_decode_iff bs x y).mp h
    have hsplit : bs = bs.take (ByteRepr.size A) ++
        (bs.drop (ByteRepr.size A)).take (ByteRepr.fieldOffset2 A B - ByteRepr.size A) ++
        (bs.drop (ByteRepr.fieldOffset2 A B)).take (ByteRepr.size B) ++
        bs.drop (ByteRepr.fieldOffset2 A B + ByteRepr.size B) := by
      have hd1 : (bs.drop (ByteRepr.size A)).drop
          (ByteRepr.fieldOffset2 A B - ByteRepr.size A) = bs.drop (ByteRepr.fieldOffset2 A B) := by
        rw [List.drop_drop]; congr 1; omega
      have hd2 : (bs.drop (ByteRepr.fieldOffset2 A B)).drop (ByteRepr.size B) =
          bs.drop (ByteRepr.fieldOffset2 A B + ByteRepr.size B) := by
        rw [List.drop_drop]
      conv => lhs; rw [← List.take_append_drop (ByteRepr.size A) bs,
        ← List.take_append_drop (ByteRepr.fieldOffset2 A B - ByteRepr.size A)
          (bs.drop (ByteRepr.size A)), hd1,
        ← List.take_append_drop (ByteRepr.size B) (bs.drop (ByteRepr.fieldOffset2 A B)), hd2]
      simp only [List.append_assoc]
    rw [hsplit, (bytesPointsto_app4 _ _ _ _ _ _).to_eq]
    icases H with ⟨H1, H2, H3, H4⟩
    have e1 : (bs.take (ByteRepr.size A)).length = ByteRepr.size A := by
      simp only [List.length_take]; omega
    have e2 : ((bs.drop (ByteRepr.size A)).take
        (ByteRepr.fieldOffset2 A B - ByteRepr.size A)).length =
        ByteRepr.fieldOffset2 A B - ByteRepr.size A := by
      simp only [List.length_take, List.length_drop]; omega
    have e3 : ((bs.drop (ByteRepr.fieldOffset2 A B)).take (ByteRepr.size B)).length =
        ByteRepr.size B := by
      simp only [List.length_take, List.length_drop]; omega
    rw [e1, e2, e3, show ByteRepr.size A + (ByteRepr.fieldOffset2 A B - ByteRepr.size A) =
      ByteRepr.fieldOffset2 A B by omega]
    isplitl [H1]
    · iexists _; iframe H1; ipureintro; exact hx
    isplitl [H2]
    · iexists _; iframe H2; ipureintro; exact e2
    isplitl [H3]
    · iexists _; iframe H3; ipureintro; exact hy
    · iexists _; iframe H4; ipureintro
      simp only [List.length_drop]; rw [hlen]
  · iintro ⟨⟨%l1, %hx, H1⟩, ⟨%l2, %hl2, H2⟩, ⟨%l3, %hy, H3⟩, ⟨%l4, %hl4, H4⟩⟩
    have e1 : l1.length = ByteRepr.size A := ByteRepr.length_of_decode _ _ hx
    have e3 : l3.length = ByteRepr.size B := ByteRepr.length_of_decode _ _ hy
    iexists l1 ++ l2 ++ l3 ++ l4
    rw [(bytesPointsto_app4 _ _ _ _ _ _).to_eq, e1, hl2, e3, show ByteRepr.size A +
      (ByteRepr.fieldOffset2 A B - ByteRepr.size A) = ByteRepr.fieldOffset2 A B by omega]
    iframe
    ipureintro
    rw [ByteRepr.prod_decode_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · rw [List.append_assoc, List.append_assoc, List.take_left' e1]; exact hx
    · have hl : (l1 ++ l2).length = ByteRepr.fieldOffset2 A B := by
        simp only [List.length_append]; omega
      rw [List.append_assoc _ l3, List.drop_left' hl, List.take_left' e3]; exact hy

end prod

end typed

/-! ## B. Strings as heap objects

A string value is its header `(ptr, len)`; its bytes are frozen at `ptr`. The
old string values `#(s : GoString)` are exactly the byte blobs `blobV s`
(`blobV_eq_intoVal`), so the existing string instructions `==` and `+`
(`GoOp _ go.string`) serve as operations on the contents. -/

section str_code
variable [FfiSyntax] [GoGlobalContext]

/-- A string value: its header. -/
abbrev strV (s : GoStrHdr) : val := PairV #s.ptr #s.len

/-- A string literal: its bytes, frozen (possibly shared with an equal literal). -/
def strLit (bs : List w8) : Expr :=
  gl(let: "p" := BAllocFrozen (Val (blobV bs)) in ("p", #(BitVec.ofNat 64 bs.length)))

/-- The contents of a string. -/
def strBytes : val := λ: "s", BLoad "s"

/-- `s1 == s2`: compare the contents. -/
def strEq : val := λ: "s1" "s2", (BLoad "s1") =⟨go.string⟩ (BLoad "s2")

/-- `s1 + s2`: a fresh string with the concatenated contents. -/
def strConcat : val :=
  λ: "s1" "s2",
    let: "c" := (BLoad "s1") +⟨go.string⟩ (BLoad "s2") in
    let: "p" := BAllocFrozen "c" in
    ("p", (Snd "s1") +⟨go.uint64⟩ (Snd "s2"))

/-- `s[i]`, with Go's bounds check (`i` unsigned). -/
def strIndex : val :=
  λ: "s" "i",
    if: "i" <⟨go.uint64⟩ (Snd "s") then BLoad ((Fst "s") +⟨go.uint64⟩ "i", #(W64 1))
    else Panic "index out of range"

end str_code

section blob
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- The old string values are the byte blobs. -/
theorem blobV_eq_intoVal (bs : List w8) : blobV bs = #(bs : GoString) := by
  rw [go.intoVal_unfold GoString]

end blob

section str_proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

open ProofMode


/-- `s` is a string with contents `bs`. -/
def isString (s : GoStrHdr) (bs : List w8) : IProp GF :=
  iprop(⌜s.len.toNat = bs.length⌝ ∗ s.ptr ↦∗□ bs)

instance isString_persistent (s : GoStrHdr) (bs : List w8) : Persistent (isString (GF := GF) s bs) := by
  unfold isString; infer_instance

theorem wp_strLit (bs : List w8) :
    {{ (⌜bs.length < 2 ^ 64⌝ : IProp GF) }} (strLit bs)
    {{ (s : GoStrHdr), RET strV s; isString s bs }} := by
  iintro %Φ %hlen HΦ
  unfold strLit
  wp_apply wp_balloc_frozen bs as %p #Hp
  iapply HΦ $$ %(⟨p, BitVec.ofNat 64 bs.length⟩ : GoStrHdr)
  unfold isString
  isplitl []
  · ipureintro; simp [Nat.mod_eq_of_lt hlen]
  · iexact Hp

theorem wp_strBytes (s : GoStrHdr) (bs : List w8) :
    {{ isString (GF := GF) s bs }} (App (Val strBytes) (Val (strV s)))
    {{ RET blobV bs; True }} := by
  unfold isString
  wp_start as ⟨%hlen, #Hs⟩
  wp_apply wp_bload s.ptr s.len DFrac.discard bs hlen.symm $$ [$Hs] as -
  iapply HΦ
  itrivial

theorem wp_strEq (s1 s2 : GoStrHdr) (bs1 bs2 : List w8) :
    {{ isString (GF := GF) s1 bs1 ∗ isString s2 bs2 }}
      (App (App (Val strEq) (Val (strV s1))) (Val (strV s2)))
    {{ RET #(decide (bs1 = bs2)); True }} := by
  unfold isString
  wp_start as ⟨⟨%hlen1, #Hs1⟩, ⟨%hlen2, #Hs2⟩⟩
  wp_apply wp_bload s1.ptr s1.len DFrac.discard bs1 hlen1.symm $$ [$Hs1] as -
  wp_apply wp_bload s2.ptr s2.len DFrac.discard bs2 hlen2.symm $$ [$Hs2] as -
  rw [blobV_eq_intoVal, blobV_eq_intoVal]
  wp_pures
  iapply HΦ
  itrivial

theorem wp_strConcat (s1 s2 : GoStrHdr) (bs1 bs2 : List w8)
    (hlt : bs1.length + bs2.length < 2 ^ 64) :
    {{ isString (GF := GF) s1 bs1 ∗ isString s2 bs2 }}
      (App (App (Val strConcat) (Val (strV s1))) (Val (strV s2)))
    {{ (s : GoStrHdr), RET strV s; isString s (bs1 ++ bs2) }} := by
  unfold isString
  wp_start as ⟨⟨%hlen1, #Hs1⟩, ⟨%hlen2, #Hs2⟩⟩
  wp_apply wp_bload s1.ptr s1.len DFrac.discard bs1 hlen1.symm $$ [$Hs1] as -
  wp_apply wp_bload s2.ptr s2.len DFrac.discard bs2 hlen2.symm $$ [$Hs2] as -
  rw [blobV_eq_intoVal, blobV_eq_intoVal]
  wp_pures
  rw [← blobV_eq_intoVal]
  wp_apply wp_balloc_frozen (bs1 ++ bs2) as %p #Hp
  iapply HΦ $$ %(⟨p, s1.len + s2.len⟩ : GoStrHdr)
  isplitl []
  · ipureintro
    simp only [BitVec.toNat_add, List.length_append]
    omega
  · iexact Hp

theorem wp_strIndex (s : GoStrHdr) (bs : List w8) (i : w64) (hi : i.toNat < bs.length) :
    {{ isString (GF := GF) s bs }}
      (App (App (Val strIndex) (Val (strV s))) (Val #i))
    {{ (b : w8), RET blobV [b]; ⌜bs[i.toNat]? = some b⌝ }} := by
  unfold isString
  wp_start as ⟨%hlen, #Hs⟩
  wp_if_destruct
  · ihave Hb := bytesPointsto_lookup s.ptr DFrac.discard bs i.toNat hi $$ Hs
    rw [show byteAddr s.ptr i.toNat = s.ptr + i by simp [byteAddr]]
    wp_apply wp_bload (s.ptr + i) (W64 1) DFrac.discard [bs[i.toNat]] rfl $$ [$Hb] as -
    iapply HΦ $$ %bs[i.toNat]
    ipureintro
    simp
  · exfalso
    simp only [uint.Z] at *
    omega

end str_proofs

/-! ## D. Funcs as code pointers

A func value is the address of its closure (`FuncAlloc`); a call loads the
closure (`FuncLoad`) and applies it. -/

section func_code
variable [FfiSyntax] [GoGlobalContext]

/-- A func literal: a fresh code pointer to the closure `v`. -/
abbrev funcLit (v : val) : Expr := FuncAlloc (Val v)

/-- Calling the func value `p` with the argument `e`. -/
def funcCall (p e : Expr) : Expr := App (FuncLoad p) e

end func_code

section func_proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

open ProofMode

theorem wp_funcLit (v : val) (hv : v.isPanic = false) :
    {{ (True : IProp GF) }} (funcLit v) {{ (p : w64), RET #p; isFunc p v ∗ ⌜p ≠ 0⌝ }} :=
  wp_func_alloc v hv

/-- A call through a func pointer is a call of its closure. -/
theorem wp_funcCall (p : w64) (f x : Binder) (e : Expr) (w : val) (hw : w.isPanic = false)
    (Φ : val → IProp GF) :
    isFunc p (RecV f x e) ∗ ▷ WP (subst' x w (subst' f (RecV f x e) e)) {{ Φ }} ⊢
      WP (funcCall (Val #p) (Val w)) {{ Φ }} := by
  unfold funcCall
  refine tac_wp_bind (K := [EctxItem.AppLCtx w hw]) (e' := FuncLoad (Val #p)) ?_
  iintro ⟨#Hf, Hwp⟩
  iapply wp_func_load p (RecV f x e) $$ Hf
  inext
  iintro _
  iapply (wp_pure_step_later (Hexec := pure_beta f x e w) hw :
    _ ⊢ WP (fill [EctxItem.AppLCtx w hw] (Val (RecV f x e))) {{ Φ }})
  inext
  iintro _
  iexact Hwp

end func_proofs

/-! ## E. `unsafe.Add`

`p := &struct{x, y uint64}{x, y}; q := unsafe.Add(p, 8); *q` reads `y`: the
field address is computed by pointer arithmetic within the allocation block
(`wp_balloc` says that the block does not wrap around the end of memory). -/

section unsafe_code
variable [FfiSyntax] [GoGlobalContext]

def unsafeAddExample (x y : w64) : Expr :=
  gl(let: "p" := BAlloc (#(W64 8), Val (blobV (ByteRepr.encode (x, y)))) in
    let: "q" := UnsafeAdd "p" #(W64 8) in
    BLoad ("q", #(W64 8)))

end unsafe_code

section unsafe_proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

open ProofMode

theorem encode_w64_pair (x y : w64) :
    ByteRepr.encode (x, y) = ByteRepr.encode x ++ ByteRepr.encode y := by
  rw [ByteRepr.prod_encode]
  have h1 : ByteRepr.fieldOffset2 w64 w64 = 8 := rfl
  have h2 : ByteRepr.size (w64 × w64) = 16 := rfl
  rw [h1, h2]
  simp [ByteRepr.size]

theorem wp_unsafeAddExample (x y : w64) :
    {{ (True : IProp GF) }} (unsafeAddExample x y) {{ RET blobV (ByteRepr.encode y); True }} := by
  iintro %Φ _ HΦ
  unfold unsafeAddExample
  wp_apply wp_balloc (W64 8) (ByteRepr.encode (x, y)) as %p ⟨H, %hp, Hb⟩
  have hlen : (ByteRepr.encode (x, y)).length = 16 := ByteRepr.length_encode _
  have hend := hp.2.2
  rw [hlen] at hend
  icases Hb with (%hnil | #Hb)
  · exfalso; rw [hnil] at hlen; exact absurd hlen (by decide)
  have hin1 : InBlock p (ByteRepr.encode (x, y)).length p := by
    unfold InBlock; rw [hlen]; omega
  have hin2 : InBlock p (ByteRepr.encode (x, y)).length (p + W64 8) := by
    have h8 : (W64 8).toNat = 8 := rfl
    unfold InBlock; rw [hlen, BitVec.toNat_add, h8]
    omega
  wp_pures
  wp_apply wp_unsafe_add p (W64 8) p _ hin1 hin2 $$ [$Hb]
  wp_pures
  ihave H2 := (bytesPointsto_app (GF := GF) p (DFrac.own 1) (ByteRepr.encode x)
    (ByteRepr.encode y)).1 $$ [H]
  · rw [← encode_w64_pair]; iexact H
  icases H2 with ⟨-, Hy⟩
  have hb : byteAddr p (ByteRepr.encode x).length = p + W64 8 := by
    rw [ByteRepr.length_encode]; rfl
  rw [hb]
  wp_apply wp_bload (p + W64 8) (W64 8) (DFrac.own 1) (ByteRepr.encode y)
    (by rw [ByteRepr.length_encode]; rfl) $$ [$Hy] as -
  iapply HΦ; itrivial

end unsafe_proofs

end Perennial
