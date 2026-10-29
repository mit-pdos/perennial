/-
The layouts of the `unsafememory` example's plain types (`Pgid`, `InBucket`, `Page`,
`leafPageElement`, `branchPageElement`, `Meta`, `words`), checked against gc's (`meta.go`,
`page.go`), their `IsPlain` instances (for `(*T)(unsafe.Pointer(p))`), and their byte views
(`Perennial/Golang/Theory/Unsafe.lean`): each struct is the bytes of its fields in order.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Base
public import Perennial.Golang.Theory.Unsafe

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-! ## Layout tactics (here rather than in `Golang/Theory/Unsafe.lean`, which would make that module
and its imports part of the precompiled `PerennialMeta` library) -/

/-- Prove `go.PlainFields fds off stop ?align` for a concrete field list, computing the alignment:
each field's layout is a scalar's or a hypothesis in the context (a named type's
`PlainLayout`). -/
macro "solve_plain_fields" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFields.nil _
    | (apply go.PlainFields.cons_ (hb := rfl)
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption
       · decide))))

/-- Prove `go.PlainLayout (go.StructType fds) size align` for a concrete field list (field layouts
as in `solve_plain_fields`). -/
macro "solve_plain_struct_layout" : tactic => `(tactic| (
  apply go.PlainLayout.struct'
  · simp
  · solve_plain_fields
  · decide
  · decide))

/-- Prove `go.PlainFieldOffset fds base f off` for a concrete field list (field layouts as in
`solve_plain_fields`). -/
macro "solve_plain_field_offset" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFieldOffset.here _ _ _
    | (apply go.PlainFieldOffset.there
       · dsimp only [go.fieldDeclName]; decide
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption))))

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-! ## Layouts -/

section layouts
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem Pgid.layout : go.PlainLayout Pgid.ty 8 8 :=
  .named _ go.uint64 8 8 go.is_underlying (by unfold Pgid.ty go.uint64; simp)
    (.scalar _ _ .isPlainScalar_uint64)

instance Pgid.isPlain : go.IsPlain Pgid.ty 8 := ⟨8, Pgid.layout⟩

/-- `InBucket` (`root Pgid; sequence uint64`): 16 bytes, `sequence` at 8. -/
theorem InBucket.fields_layout : go.PlainLayout (go.StructType InBucket.fields) 16 8 := by
  have := Pgid.layout
  simp only [InBucket.fields, InBucket.fieldsUnsealed]
  solve_plain_struct_layout

theorem InBucket.layout : go.PlainLayout InBucket.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold InBucket.ty; simp) InBucket.fields_layout

instance InBucket.isPlain : go.IsPlain InBucket.ty 16 := ⟨8, InBucket.layout⟩

/-- `Page` (`id Pgid; flags, count uint16; overflow uint32`): 16 bytes, `flags` at 8, `count` at
10, `overflow` at 12. -/
theorem Page.fields_layout : go.PlainLayout (go.StructType Page.fields) 16 8 := by
  have := Pgid.layout
  simp only [Page.fields, Page.fieldsUnsealed]
  solve_plain_struct_layout

theorem Page.layout : go.PlainLayout Page.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold Page.ty; simp) Page.fields_layout

instance Page.isPlain : go.IsPlain Page.ty 16 := ⟨8, Page.layout⟩

/-- `leafPageElement` (four `uint32`s): 16 bytes. -/
theorem leafPageElement.fields_layout :
    go.PlainLayout (go.StructType leafPageElement.fields) 16 4 := by
  simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]
  solve_plain_struct_layout

theorem leafPageElement.layout : go.PlainLayout leafPageElement.ty 16 4 :=
  .named _ _ 16 4 go.is_underlying (by unfold leafPageElement.ty; simp)
    leafPageElement.fields_layout

instance leafPageElement.isPlain : go.IsPlain leafPageElement.ty 16 := ⟨4, leafPageElement.layout⟩

/-- `branchPageElement` (`pos, ksize uint32; pgid Pgid`): 16 bytes, `pgid` at 8. -/
theorem branchPageElement.fields_layout :
    go.PlainLayout (go.StructType branchPageElement.fields) 16 8 := by
  have := Pgid.layout
  simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]
  solve_plain_struct_layout

theorem branchPageElement.layout : go.PlainLayout branchPageElement.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold branchPageElement.ty; simp)
    branchPageElement.fields_layout

instance branchPageElement.isPlain : go.IsPlain branchPageElement.ty 16 :=
  ⟨8, branchPageElement.layout⟩

/-- `Meta`: 64 bytes, no padding (`root` at 16, `txid` at 48, `checksum` at 56). -/
theorem Meta.fields_layout : go.PlainLayout (go.StructType Meta.fields) 64 8 := by
  have := Pgid.layout
  have := InBucket.layout
  simp only [Meta.fields, Meta.fieldsUnsealed]
  solve_plain_struct_layout

theorem Meta.layout : go.PlainLayout Meta.ty 64 8 :=
  .named _ _ 64 8 go.is_underlying (by unfold Meta.ty; simp) Meta.fields_layout

instance Meta.isPlain : go.IsPlain Meta.ty 64 := ⟨8, Meta.layout⟩

/-- `words` (eight `uint64`s): 64 bytes. -/
theorem words.fields_layout : go.PlainLayout (go.StructType words.fields) 64 8 := by
  simp only [words.fields, words.fieldsUnsealed]
  solve_plain_struct_layout

theorem words.layout : go.PlainLayout words.ty 64 8 :=
  .named _ _ 64 8 go.is_underlying (by unfold words.ty; simp) words.fields_layout

instance words.isPlain : go.IsPlain words.ty 64 := ⟨8, words.layout⟩

end layouts

/-! ## Byte encodings: a struct is its fields' bytes in order -/

section encodings
variable [GooseExts]

instance InBucket.byteEncoding : ByteEncoding InBucket 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w64) (fun v => (v.root', v.sequence'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl) (fun _ => rfl)

instance Page.byteEncoding : ByteEncoding Page 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w16 × w16 × w32)
    (fun v => (v.id', v.flags', v.count', v.overflow'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance leafPageElement.byteEncoding : ByteEncoding leafPageElement 16 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × w32 × w32)
    (fun v => (v.flags', v.pos', v.ksize', v.vsize'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance branchPageElement.byteEncoding : ByteEncoding branchPageElement 16 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × Pgid)
    (fun v => (v.pos', v.ksize', v.pgid'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance Meta.byteEncoding : ByteEncoding Meta 64 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × w32 × w32 × InBucket × Pgid × Pgid × w64 × w64)
    (fun v => (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance words.byteEncoding : ByteEncoding words 64 :=
  ByteEncoding.ofEquiv (W := w64 × w64 × w64 × w64 × w64 × w64 × w64 × w64)
    (fun v => (v.a', v.b', v.c', v.d', v.e', v.f', v.g', v.h'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

end encodings

/-! ## Byte views -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance InBucket.bytesView : BytesView (GF := GF) InBucket where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ InBucket InBucket.fields_layout
    have o1 : go.PlainFieldOffset InBucket.fields 0 go!"root" 0 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset InBucket.fields 0 go!"sequence" 8 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o1 l hl, off _ _ o2 l hl]
    exact bytesView_field l 0 _ dq _ _ _ hl (bytesView_last_field l 8 _ dq _ _ hl)

instance Page.bytesView : BytesView (GF := GF) Page where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ Page Page.fields_layout
    have o0 : go.PlainFieldOffset Page.fields 0 go!"id" 0 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset Page.fields 0 go!"flags" 8 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset Page.fields 0 go!"count" 10 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset Page.fields 0 go!"overflow" 12 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 10 _ dq _ _ _ hl
      (bytesView_last_field l 12 _ dq _ _ hl))))

instance leafPageElement.bytesView : BytesView (GF := GF) leafPageElement where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have off := structFieldRef_offset _ leafPageElement leafPageElement.fields_layout
    have o0 : go.PlainFieldOffset leafPageElement.fields 0 go!"flags" 0 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset leafPageElement.fields 0 go!"pos" 4 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset leafPageElement.fields 0 go!"ksize" 8 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset leafPageElement.fields 0 go!"vsize" 12 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_last_field l 12 _ dq _ _ hl))))

instance branchPageElement.bytesView : BytesView (GF := GF) branchPageElement where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ branchPageElement branchPageElement.fields_layout
    have o0 : go.PlainFieldOffset branchPageElement.fields 0 go!"pos" 0 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset branchPageElement.fields 0 go!"ksize" 4 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset branchPageElement.fields 0 go!"pgid" 8 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_last_field l 8 _ dq _ _ hl)))

instance Meta.bytesView : BytesView (GF := GF) Meta where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have := InBucket.layout
    have off := structFieldRef_offset _ Meta Meta.fields_layout
    have o0 : go.PlainFieldOffset Meta.fields 0 go!"magic" 0 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset Meta.fields 0 go!"version" 4 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset Meta.fields 0 go!"pageSize" 8 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset Meta.fields 0 go!"flags" 12 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o4 : go.PlainFieldOffset Meta.fields 0 go!"root" 16 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o5 : go.PlainFieldOffset Meta.fields 0 go!"freelist" 32 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o6 : go.PlainFieldOffset Meta.fields 0 go!"pgid" 40 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o7 : go.PlainFieldOffset Meta.fields 0 go!"txid" 48 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o8 : go.PlainFieldOffset Meta.fields 0 go!"checksum" 56 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl, off _ _ o4 l hl, off _ _ o5 l hl, off _ _ o6 l hl, off _ _ o7 l hl, off _ _ o8 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 12 _ dq _ _ _ hl
      (bytesView_field l 16 _ dq _ _ _ hl
      (bytesView_field l 32 _ dq _ _ _ hl
      (bytesView_field l 40 _ dq _ _ _ hl
      (bytesView_field l 48 _ dq _ _ _ hl
      (bytesView_last_field l 56 _ dq _ _ hl)))))))))

instance words.bytesView : BytesView (GF := GF) words where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have off := structFieldRef_offset _ words words.fields_layout
    have o0 : go.PlainFieldOffset words.fields 0 go!"a" 0 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset words.fields 0 go!"b" 8 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset words.fields 0 go!"c" 16 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset words.fields 0 go!"d" 24 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o4 : go.PlainFieldOffset words.fields 0 go!"e" 32 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o5 : go.PlainFieldOffset words.fields 0 go!"f" 40 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o6 : go.PlainFieldOffset words.fields 0 go!"g" 48 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    have o7 : go.PlainFieldOffset words.fields 0 go!"h" 56 := by
      simp only [words.fields, words.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl, off _ _ o4 l hl, off _ _ o5 l hl, off _ _ o6 l hl, off _ _ o7 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 16 _ dq _ _ _ hl
      (bytesView_field l 24 _ dq _ _ _ hl
      (bytesView_field l 32 _ dq _ _ _ hl
      (bytesView_field l 40 _ dq _ _ _ hl
      (bytesView_field l 48 _ dq _ _ _ hl
      (bytesView_last_field l 56 _ dq _ _ hl))))))))

end views

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory
end Perennial
