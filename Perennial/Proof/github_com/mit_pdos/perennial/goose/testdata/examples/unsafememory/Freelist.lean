/-
The freelist pages of the `unsafememory` example (`freelist.go`): `writeIds` lays the ids as a
`[]Pgid` over the page after its 16-byte header, with the count in the header or, for `0xFFFF` or
more ids, in the first id; `readIds` reads them back through `unsafe.Slice` and copies them.

The page is the byte points-to of its bytes; its ids are a slice of `Pgid` over those bytes
(`ownSlice_of_bytes`), made when the program makes one with `unsafe.Slice`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Layout

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-! ## Freelist pages as bytes -/

section pure
variable [GooseExts]

/-- The ids a freelist page stores after its header: `vs`, preceded by their count when there
are `0xFFFF` or more. -/
def freelistIds (vs : List w64) : List w64 :=
  if vs.length < 65535 then vs else W64 vs.length :: vs

/-- The `count` of a freelist page of the ids `vs`. -/
def freelistCount (vs : List w64) : w16 :=
  if vs.length < 65535 then W16 vs.length else W16 65535

/-- The header `writeIds` leaves, from the header `h` there was. -/
def freelistHeader (h : Page) (vs : List w64) : Page :=
  { h with flags' := W16 16, count' := freelistCount vs }

/-- The bytes `writeIds` leaves in the page bytes `bs`. -/
def freelistBytes (bs : List w8) (vs : List w64) : List w8 :=
  encode (freelistHeader (decode (bs.take 16)) vs) ++ (freelistIds vs).flatMap encode ++
    bs.drop (16 + 8 * (freelistIds vs).length)

theorem freelistIds_length (vs : List w64) :
    (freelistIds vs).length = if vs.length < 65535 then vs.length else vs.length + 1 := by
  unfold freelistIds; split <;> simp

/-- `k` values of `n` bytes each, decoded from the bytes `bs`. -/
def decodeChunks {V : Type} {n : Nat} [ByteEncoding V n] : Nat → List w8 → List V
  | 0, _ => []
  | k + 1, bs => decode (bs.take n) :: decodeChunks k (bs.drop n)

theorem decodeChunks_length {V : Type} {n : Nat} [ByteEncoding V n] (k : Nat) (bs : List w8) :
    (decodeChunks (V := V) k bs).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [decodeChunks, ih]

/-- Bytes of the length of `k` values are the encoding of the values they decode to. -/
theorem decodeChunks_flatMap {V : Type} {n : Nat} [ByteEncoding V n] (k : Nat) (bs : List w8)
    (h : bs.length = k * n) : (decodeChunks (V := V) k bs).flatMap encode = bs := by
  induction k generalizing bs with
  | zero => simp [decodeChunks] at h ⊢; simp [h]
  | succ k ih =>
    simp only [decodeChunks, List.flatMap_cons]
    rw [ByteEncoding.encode_decode _ (by simp; rw [Nat.succ_mul] at h; omega),
      ih _ (by simp; rw [Nat.succ_mul] at h; omega), List.take_append_drop]

end pure

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
open ProofMode

/-- A byte points-to of at least one byte lies in `(0, maxAddr]`. -/
theorem bytesPointsto_bounds (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  iintro Hb
  icases bytesPointsto_pos l dq bs h $$ Hb with %Hl
  icases (arrayElems_bytes l bs dq Hl).2 $$ Hb with Hb
  iapply arrayElems_bytes_bounds l bs dq h $$ Hb

/-- The bytes of the elements of `vs`, from a positive address, are a slice of the plain `e` with
those elements. -/
theorem ownSlice_of_bytes {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr)
    (hlen : sint.Z s.len = vs.length) (hcap : sint.Z s.len ≤ sint.Z s.cap) :
    bytesPointsto (GF := GF) s.ptr dq (vs.flatMap encode) ⊢ s ↦*{dq} vs := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro Hb
  iright
  isplitl [Hb]
  · iapply (typedPointsto_array_bytes e hlay s.ptr (sint.Z s.len) (array.mk _ vs) dq hl).2
    iframe Hb
    ipureintro; exact hlen.symm
  · ipureintro; exact hcap

/-- A slice of plain `e` at a positive address is the bytes of its elements. -/
theorem ownSlice_to_bytes {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr) :
    (s ↦*{dq} vs : IProp GF) ⊢ bytesPointsto s.ptr dq (vs.flatMap encode) := by
  iintro Hs
  icases ownSlice_bytes_acc e hlay s vs dq hl $$ Hs with ⟨Hb, _⟩
  iexact Hb

/-- `pageAt(buf, 0)`: the page at the start of a non-empty buffer. -/
theorem wp_pageAt_zero (buf : GoSlice) (hlen : 0 < sint.Z buf.len) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! pageAt)) (Val #buf)) (Val #(W64 0)))
    {{ RET #buf.ptr; True }} := by
  wp_start
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z buf.len from ⟨by decide, hlen⟩)]
  wp_auto
  rw [show sliceIndexRef w8 (sint.Z (W64 0)) buf = buf.ptr from go.arrayIndexRef_0 _ _]
  iapply HΦ; itrivial

/-- `unsafeAdd(base, offset)`, for a result in `[0, maxAddr]`. -/
theorem wp_unsafeAdd_direct (l : Loc) (x : w64)
    (h : 0 ≤ (l +ₗ sint.Z x).addr ∧ (l +ₗ sint.Z x).addr ≤ maxAddr) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! unsafeAdd)) (Val #l)) (Val #x))
    {{ RET #(l +ₗ sint.Z x); True }} := by
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus _ _ _ h
  iapply HΦ; itrivial

/-- `copy(dst, ids)` into a `[]Pgid` over bytes: the bytes become those of the ids. -/
theorem wp_copy_into_bytes (d : GoSlice) (bs : List w8) (ids : GoSlice) (vs : List w64)
    (dq : DFrac) (hl : 0 < d.ptr.addr) (hlen : sint.Z d.len = vs.length)
    (hcap : sint.Z d.len ≤ sint.Z d.cap) (hbs : bs.length = vs.length * 8) :
    {{ bytesPointsto (GF := GF) d.ptr (DFrac.own 1) bs ∗ ids ↦*{dq} vs }}
      (App (App (Val #(functions go.copy [go.SliceType Pgid.ty])) (Val #d)) (Val #ids))
    {{ (n : w64), RET #n; bytesPointsto d.ptr (DFrac.own 1) (vs.flatMap encode) ∗ ids ↦*{dq} vs }} := by
  iintro %Φ ⟨Hb, Hids⟩ HΦ
  ihave Hb := bytesPointsto_congr _ _ _ _ (decodeChunks_flatMap (V := w64) vs.length bs hbs).symm
    $$ Hb
  ihave Hd := ownSlice_of_bytes Pgid.ty Pgid.layout d _ _ hl
    (by rw [decodeChunks_length]; exact hlen) hcap $$ Hb
  wp_apply wp_slice_copy d _ ids vs dq $$ [Hd Hids] as %n ⟨%Hn, Hd, Hids⟩
  · iframe
  rw [decodeChunks_length, List.take_length, List.drop_of_length_le (by rw [decodeChunks_length]; exact Nat.le_refl _),
    List.append_nil]
  iapply HΦ
  iframe Hids
  iapply ownSlice_to_bytes Pgid.ty Pgid.layout d _ _ hl $$ Hd

/-- A page header and the bytes after it are the page's bytes. -/
theorem page_bytes_close (p : Loc) (h : Page) (rest : List w8) (hl : 0 < p.addr) :
    typedPointsto (GF := GF) p h (DFrac.own 1) ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) rest ⊢
      bytesPointsto p (DFrac.own 1) (encode h ++ rest) := by
  iintro ⟨Hh, Hr⟩
  icases (typedPointsto_bytes p h _ hl).1 $$ Hh with Hh
  iapply (bytesPointsto_app p _ (encode h) rest).2
  rw [ByteEncoding.encode_length]
  iframe

/-- The bytes `writeIds` leaves, from its stores to the header and the ids. -/
theorem writeIds_close (p : Loc) (bs : List w8) (vs : List w64) (c : w16)
    (hc : c = freelistCount vs) (hl : 0 < p.addr) :
    typedPointsto (GF := GF) p (Page.mk (Page.id' (decode (bs.take 16))) (W16 16) c
      (Page.overflow' (decode (bs.take 16)))) (DFrac.own 1) ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        ((freelistIds vs).flatMap encode ++ bs.drop (16 + 8 * (freelistIds vs).length)) ⊢
      bytesPointsto p (DFrac.own 1) (freelistBytes bs vs) := by
  subst hc
  unfold freelistBytes
  rw [List.append_assoc]
  exact page_bytes_close p _ _ hl

/-- `unsafe.Slice((*Pgid)(l), n)` for a non-null `l` and a slice that ends in the address space. -/
theorem wp_unsafe_slice_Pgid (l : Loc) (n : w64) (hn : 0 ≤ sint.Z n) (hl : 0 < l.addr)
    (hb : l.addr + sint.Z n * 8 ≤ 2 ^ 64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions «unsafe».Slice [Pgid.ty, go.int])) (Val #l)) (Val #n))
    {{ RET #(slice.mk l n n); True }} := by
  iintro %Φ _ HΦ
  wp_func_call
  wp_call
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  rw [ite_eq_right (by omega), ite_eq_right hnn, ite_eq_right (by push_cast; omega)]
  wp_auto
  iapply HΦ; itrivial

/-- `writeIds(p, ids)` on a page of bytes `bs` with room for the ids. -/
theorem wp_writeIds (p : Loc) (bs : List w8) (ids : GoSlice) (vs : List w64) (dq : DFrac)
    (hlen : 16 + 8 * (freelistIds vs).length ≤ bs.length) (hvs : vs.length < 2 ^ 40) :
    {{ bytesPointsto (GF := GF) p (DFrac.own 1) bs ∗ ids ↦*{dq} vs }}
      (App (App (Val (@! writeIds)) (Val #p)) (Val #ids))
    {{ RET #(); bytesPointsto p (DFrac.own 1) (freelistBytes bs vs) ∗ ids ↦*{dq} vs }} := by
  wp_start as ⟨Hb, Hids⟩
  icases bytesPointsto_bounds p _ bs (by intro h; subst h; simp at hlen) $$ Hb with %Hbnd
  ihave %Hlen := ownSlice_len _ _ _ $$ Hids
  ihave Hb := bytesPointsto_congr p _ bs _ (List.take_append_drop 16 bs).symm $$ Hb
  icases (bytesPointsto_app p _ (bs.take 16) (bs.drop 16)).1 $$ Hb with ⟨Hh, Hr⟩
  icases (bytesPointsto_typed (V := Page) p _ (bs.take 16) (by simp; omega) Hbnd.1).1 $$ Hh with Hh
  wp_auto
  have h16 : (List.take 16 bs).length = 16 := by simp; omega
  rw [h16]
  wp_if_destruct
  · have hv : vs = [] := by
      rw [Hif] at Hlen; exact List.eq_nil_of_length_eq_zero Hlen.1
    subst hv
    iapply HΦ
    iframe Hids
    iapply writeIds_close p bs [] (W16 (sint.Z ids.len)) (by rw [Hif]; rfl) Hbnd.1
    iframe Hh
    simp [freelistIds]
    iexact Hr
  rw [show ((16 : Nat) : Int) = 16 from rfl]
  have h16' : sint.Z (W64 16) = 16 := rfl
  have hn : sint.Z ids.len = vs.length := by
    rw [Hlen.1]; show sint.Z ids.len = ((sint.Z ids.len).toNat : Int); omega
  have hadd : 0 ≤ (p +ₗ sint.Z (W64 16)).addr ∧ (p +ₗ sint.Z (W64 16)).addr ≤ maxAddr := by
    simp only [h16', Loc.add]; omega
  wp_if_destruct
  · wp_apply wp_unsafeAdd_direct p (W64 16) hadd
    rw [h16']
    have hsmall : vs.length < 65535 := by rw [show sint.Z (W64 65535) = 65535 from rfl] at Hif; omega
    have hfi : freelistIds vs = vs := by simp [freelistIds, hsmall]
    rw [hfi] at hlen
    wp_apply wp_unsafe_slice_Pgid (p +ₗ 16) ids.len Hlen.2 (by simp [Loc.add]; omega)
      (by simp only [Loc.add]; simp [maxAddr] at Hbnd; omega)
    ihave Hr := bytesPointsto_congr _ _ _ _
      (List.take_append_drop (vs.length * 8) (bs.drop 16)).symm $$ Hr
    icases (bytesPointsto_app _ _ _ _).1 $$ Hr with ⟨Hr1, Hr2⟩
    wp_apply wp_copy_into_bytes (slice.mk (p +ₗ 16) ids.len ids.len)
      ((bs.drop 16).take (vs.length * 8)) ids vs dq
      (by simp [Loc.add]; omega) hn (Int.le_refl _) (by simp; omega) $$ [Hr1 Hids] as %n ⟨Hr1, Hids⟩
    · iframe
    iapply HΦ
    iframe Hids
    iapply writeIds_close p bs vs (W16 (sint.Z ids.len))
      (by simp only [freelistCount, hsmall, ↓reduceIte, hn]) Hbnd.1
    iframe Hh
    rw [hfi]
    iapply (bytesPointsto_app _ _ _ _).2
    rw [flatMap_encode_length,
      show List.drop (vs.length * 8) (List.drop 16 bs) = List.drop (16 + 8 * vs.length) bs by
        rw [List.drop_drop]; congr 1; omega,
      show (List.take (vs.length * 8) (List.drop 16 bs)).length = vs.length * 8 by simp; omega]
    iframe
  · wp_apply wp_unsafeAdd_direct p (W64 16) hadd
    rw [h16']
    have hbig : 65535 ≤ vs.length := by rw [show sint.Z (W64 65535) = 65535 from rfl] at Hif; omega
    have hfi : freelistIds vs = W64 vs.length :: vs := by simp [freelistIds]; omega
    rw [hfi] at hlen
    simp only [List.length_cons] at hlen
    have hl1 : sint.Z (ids.len + W64 1) = vs.length + 1 := by rw [← hn]; word
    have hlw : ids.len = W64 vs.length := by rw [← hn]; word
    wp_apply wp_unsafe_slice_Pgid (p +ₗ 16) (ids.len + W64 1) (by omega) (by simp [Loc.add]; omega)
      (by simp only [Loc.add]; simp [maxAddr] at Hbnd; omega)
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (ids.len + W64 1) from
      ⟨by decide, by rw [hl1]; show (0 : Int) < _; omega⟩),
      show sliceIndexRef w64 (sint.Z (W64 0)) (slice.mk (p +ₗ 16) (ids.len + W64 1)
        (ids.len + W64 1)) = p +ₗ 16 from go.arrayIndexRef_0 _ _]
    ihave Hr := bytesPointsto_congr _ _ _ _ (List.take_append_drop 8 (bs.drop 16)).symm $$ Hr
    icases (bytesPointsto_app _ _ _ _).1 $$ Hr with ⟨Hc, Hr⟩
    icases (bytesPointsto_typed (V := w64) (p +ₗ 16) _ _ (by simp; omega)
      (by simp [Loc.add]; omega)).1 $$ Hc with Hc
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (ids.len + W64 1) ∧
      sint.Z (ids.len + W64 1) ≤ sint.Z (ids.len + W64 1) from
      ⟨by decide, by rw [hl1]; show (1 : Int) ≤ _; omega, Int.le_refl _⟩)]
    have hsl : slice.slice (slice.mk (p +ₗ 16) (ids.len + W64 1) (ids.len + W64 1)) w64 (W64 1)
        (ids.len + W64 1) = slice.mk (p +ₗ 16 +ₗ 8) ids.len ids.len := by
      have := sliceIndexRef_plain_W64 (V := w64) Pgid.ty Pgid.layout
        (slice.mk (p +ₗ 16) (ids.len + W64 1) (ids.len + W64 1)) 1 (by simp [Loc.add]; omega)
        (by decide)
      simp only [slice.slice]
      rw [show sint.Z (W64 1) = sint.Z (W64 ((1 : Nat) : Int)) from rfl, this]
      have e : ids.len + W64 1 - W64 1 = ids.len := by word
      rw [e]; rfl
    rw [hsl]
    wp_auto
    rw [show (List.take 8 (List.drop 16 bs)).length = 8 by simp; omega]
    ihave Hr := bytesPointsto_congr _ _ _ _
      (List.take_append_drop (vs.length * 8) ((bs.drop 16).drop 8)).symm $$ Hr
    icases (bytesPointsto_app _ _ _ _).1 $$ Hr with ⟨Hr1, Hr2⟩
    wp_apply wp_copy_into_bytes (slice.mk (p +ₗ 16 +ₗ 8) ids.len ids.len)
      (((bs.drop 16).drop 8).take (vs.length * 8)) ids vs dq
      (by simp [Loc.add]; omega) hn (Int.le_refl _) (by simp; omega) $$ [Hr1 Hids] as %n ⟨Hr1, Hids⟩
    · iframe
    iapply HΦ
    iframe Hids
    iapply writeIds_close p bs vs (W16 65535)
      (by simp only [freelistCount]; rw [ite_eq_right (by omega)]) Hbnd.1
    iframe Hh
    rw [hfi, List.flatMap_cons, List.append_assoc, List.length_cons]
    iapply (bytesPointsto_app _ _ _ _).2
    rw [ByteEncoding.encode_length]
    isplitl [Hc]
    · rw [← hlw]
      iapply (typedPointsto_bytes _ _ _ (by simp [Loc.add]; omega)).1 $$ Hc
    iapply (bytesPointsto_app _ _ _ _).2
    rw [flatMap_encode_length,
      show List.drop (vs.length * 8) (List.drop 8 (List.drop 16 bs)) =
        List.drop (16 + 8 * (vs.length + 1)) bs by
        rw [List.drop_drop, List.drop_drop]; congr 1; omega,
      show (List.take (vs.length * 8) (List.drop 8 (List.drop 16 bs))).length = vs.length * 8 by
        simp; omega,
      show ((8 : Nat) : Int) = 8 from rfl]
    iframe

/-- `unsafeIndex(base, offset, elemsz, n)`, for a result in `[0, maxAddr]`. -/
theorem wp_unsafeIndex_direct (l : Loc) (off sz n : w64)
    (h : 0 ≤ (l +ₗ sint.Z (off + n * sz)).addr ∧ (l +ₗ sint.Z (off + n * sz)).addr ≤ maxAddr) :
    {{ (True : IProp GF) }}
      (App (App (App (App (Val (@! unsafeIndex)) (Val #l)) (Val #off)) (Val #sz)) (Val #n))
    {{ RET #(l +ₗ sint.Z (off + n * sz)); True }} := by
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus _ _ _ h
  iapply HΦ; itrivial

/-- `copy(out, ids)` from a `[]Pgid` over bytes into a slice of as many elements. -/
theorem wp_copy_from_bytes (out : GoSlice) (ws : List w64) (d : GoSlice) (vs : List w64)
    (hl : 0 < d.ptr.addr) (hlen : sint.Z d.len = vs.length) (hcap : sint.Z d.len ≤ sint.Z d.cap)
    (hws : ws.length = vs.length) :
    {{ (out ↦* ws ∗ bytesPointsto d.ptr (DFrac.own 1) (vs.flatMap encode) : IProp GF) }}
      (App (App (Val #(functions go.copy [go.SliceType Pgid.ty])) (Val #out)) (Val #d))
    {{ (n : w64), RET #n; out ↦* vs ∗ bytesPointsto d.ptr (DFrac.own 1) (vs.flatMap encode) }} := by
  iintro %Φ ⟨Hout, Hb⟩ HΦ
  ihave Hd := ownSlice_of_bytes Pgid.ty Pgid.layout d _ _ hl hlen hcap $$ Hb
  wp_apply wp_slice_copy out ws d vs (DFrac.own 1) $$ [Hout Hd] as %n ⟨%Hn, Hout, Hd⟩
  · iframe
  rw [hws, List.take_length, List.drop_of_length_le (by rw [hws]; exact Nat.le_refl _),
    List.append_nil]
  iapply HΦ
  iframe Hout
  iapply ownSlice_to_bytes Pgid.ty Pgid.layout d _ _ hl $$ Hd

/-- `readIds(p)` on a freelist page with the ids `vs`: a new slice of them (`nil` for none). -/
theorem wp_readIds (p : Loc) (h : Page) (vs : List w64) (rest : List w8)
    (hc : h.count' = freelistCount vs) (hvs : vs.length < 2 ^ 40) :
    {{ bytesPointsto (GF := GF) p (DFrac.own 1) (encode h ++ (freelistIds vs).flatMap encode ++ rest) }}
      (App (Val (@! readIds)) (Val #p))
    {{ (s : GoSlice), RET #s; bytesPointsto p (DFrac.own 1) (encode h ++ (freelistIds vs).flatMap encode ++ rest) ∗
        ⌜vs = [] → s = slice.nil⌝ ∗ s ↦* vs }} := by
  wp_start as Hb
  icases bytesPointsto_bounds p _ _ (by simp [List.append_eq_nil_iff, ByteEncoding.encode_ne_nil h (by decide)]) $$ Hb with %Hbnd
  ihave Hb := bytesPointsto_congr _ _ _ _ (List.append_assoc _ _ _) $$ Hb
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hx⟩
  icases (typedPointsto_bytes p h _ Hbnd.1).2 $$ Hh with Hh
  rw [ByteEncoding.encode_length]
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  have h16' : sint.Z (W64 16) = 16 := rfl
  rw [show ((16 : Nat) : Int) = 16 from rfl]
  have hlen : (encode h ++ List.flatMap encode (freelistIds vs) ++ rest).length =
      16 + 8 * (freelistIds vs).length + rest.length := by
    rw [List.length_append, List.length_append, ByteEncoding.encode_length, flatMap_encode_length]
    omega
  rw [hlen] at Hbnd
  wp_if_destruct
  · have hbig : 65535 ≤ vs.length := by
      rw [hc] at Hif; simp only [freelistCount] at Hif
      by_cases hn : vs.length < 65535
      · exfalso
        simp only [hn, ↓reduceIte, W16] at Hif
        have := congrArg BitVec.toNat Hif
        simp only [BitVec.toNat_ofInt] at this
        omega
      · omega
    have hfi : freelistIds vs = W64 vs.length :: vs := by simp [freelistIds]; omega
    rw [hfi] at Hbnd
    simp only [List.length_cons] at Hbnd
    ihave Hx := bytesPointsto_congr _ _ _ (encode (W64 (vs.length : Int)) ++ (vs.flatMap encode ++ rest))
      (by rw [hfi, List.flatMap_cons, List.append_assoc]) $$ Hx
    icases (bytesPointsto_app _ _ _ _).1 $$ Hx with ⟨Hc, Hx⟩
    rw [ByteEncoding.encode_length, show ((8 : Nat) : Int) = 8 from rfl]
    icases (typedPointsto_bytes (p +ₗ 16) (W64 (vs.length : Int)) _ (by simp [Loc.add]; omega)).2
      $$ Hc with Hc
    wp_apply wp_unsafeAdd_direct p (W64 16) (by simp only [h16', Loc.add]; omega)
    rw [h16']
    wp_auto
    have hn : sint.Z (W64 (vs.length : Int)) = vs.length := sint_Z_W64_nat _ (by omega)
    wp_if_destruct
    · exfalso
      have := congrArg (fun x : w64 => sint.Z x) Hif
      simp only [hn, show sint.Z (W64 0) = 0 from rfl] at this; omega
    have h24 : sint.Z (W64 16 + W64 1 * W64 8) = 24 := by rfl
    wp_apply wp_unsafeIndex_direct p (W64 16) (W64 8) (W64 1) (by rw [h24]; simp only [Loc.add]; omega)
    rw [h24, show p +ₗ 24 = p +ₗ 16 +ₗ 8 by rw [loc_add_assoc]; rfl]
    wp_apply wp_unsafe_slice_Pgid (p +ₗ 16 +ₗ 8) (W64 vs.length) (by omega)
      (by simp [Loc.add]; omega) (by simp only [Loc.add]; simp [maxAddr] at Hbnd; omega)
    wp_apply wp_slice_make2 (V := w64) (W64 vs.length) $$ [] as %out ⟨Hout, _⟩
    · ipureintro; omega
    icases (bytesPointsto_app _ _ _ _).1 $$ Hx with ⟨Hx1, Hx2⟩
    wp_apply wp_copy_from_bytes out (List.replicate (sint.nat (W64 vs.length)) (zero_val w64))
      (slice.mk (p +ₗ 16 +ₗ 8) (W64 vs.length) (W64 vs.length)) vs
      (by simp [Loc.add]; omega) hn (Int.le_refl _)
      (by rw [List.length_replicate]; simp only [sint.nat, hn]; omega) $$ [Hout Hx1]
      as %n ⟨Hout, Hx1⟩
    · iframe
    iapply HΦ
    isplitl [Hh Hc Hx1 Hx2]
    · iapply bytesPointsto_congr _ _ _ _ (List.append_assoc _ _ _).symm
      iapply page_bytes_close p h _ Hbnd.1
      iframe Hh
      iapply bytesPointsto_congr _ _ (encode (W64 (vs.length : Int)) ++ (vs.flatMap encode ++ rest))
        _ (by rw [hfi, List.flatMap_cons, List.append_assoc])
      iapply (bytesPointsto_app _ _ _ _).2
      rw [ByteEncoding.encode_length, show ((8 : Nat) : Int) = 8 from rfl]
      isplitl [Hc]
      · iapply (typedPointsto_bytes _ _ _ (by simp [Loc.add]; omega)).1 $$ Hc
      iapply (bytesPointsto_app _ _ _ _).2
      iframe
    isplitr
    · ipureintro; intro hv; subst hv; simp at hbig
    iexact Hout
  · have hsmall : vs.length < 65535 := by
      rw [hc] at Hif; simp only [freelistCount] at Hif
      by_cases hn : vs.length < 65535
      · exact hn
      · exfalso; apply Hif; simp [hn]
    have hfi : freelistIds vs = vs := by simp [freelistIds, hsmall]
    rw [hfi] at Hbnd
    rw [hfi]
    have hcount : W64 (uint.Z h.count') = W64 vs.length := by
      rw [hc]; simp only [freelistCount, hsmall, ↓reduceIte]
      congr 1; simp only [uint.Z, W16, BitVec.toNat_ofInt]; omega
    rw [hcount]
    wp_if_destruct
    · have hv : vs = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := congrArg (fun x : w64 => sint.Z x) Hif
        simp only [sint_Z_W64_nat _ (by omega : vs.length < 2 ^ 63)] at this
        rw [show sint.Z (W64 0) = 0 from rfl] at this; omega
      subst hv
      iapply HΦ
      isplitl [Hh Hx]
      · iapply bytesPointsto_congr _ _ _ _ (List.append_assoc _ _ _).symm
        iapply page_bytes_close p h _ Hbnd.1
        iframe
      isplitr
      · ipureintro; intro _; rfl
      iapply ownSlice_nil
    have hn : sint.Z (W64 (vs.length : Int)) = vs.length := sint_Z_W64_nat _ (by omega)
    wp_apply wp_unsafeIndex_direct p (W64 16) (W64 8) (W64 0)
      (by rw [show W64 16 + W64 0 * W64 8 = W64 16 by rfl, h16']; simp only [Loc.add]; omega)
    rw [show W64 16 + W64 0 * W64 8 = W64 16 by rfl, h16']
    wp_apply wp_unsafe_slice_Pgid (p +ₗ 16) (W64 vs.length) (by omega) (by simp [Loc.add]; omega)
      (by simp only [Loc.add]; simp [maxAddr] at Hbnd; omega)
    wp_apply wp_slice_make2 (V := w64) (W64 vs.length) $$ [] as %out ⟨Hout, _⟩
    · ipureintro; omega
    icases (bytesPointsto_app _ _ _ _).1 $$ Hx with ⟨Hx1, Hx2⟩
    wp_apply wp_copy_from_bytes out (List.replicate (sint.nat (W64 vs.length)) (zero_val w64))
      (slice.mk (p +ₗ 16) (W64 vs.length) (W64 vs.length)) vs
      (by simp [Loc.add]; omega) hn (Int.le_refl _)
      (by rw [List.length_replicate]; simp only [sint.nat, hn]; omega) $$ [Hout Hx1]
      as %n ⟨Hout, Hx1⟩
    · iframe
    iapply HΦ
    isplitl [Hh Hx1 Hx2]
    · iapply bytesPointsto_congr _ _ _ _ (List.append_assoc _ _ _).symm
      iapply page_bytes_close p h _ Hbnd.1
      iframe Hh
      iapply (bytesPointsto_app _ _ _ _).2
      iframe
    isplitr
    · ipureintro; intro hv; subst hv; simp at Hif
    iexact Hout


end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

end Perennial
