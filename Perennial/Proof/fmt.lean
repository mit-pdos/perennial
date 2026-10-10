/-
Package initialization of `fmt`, `fmt.Errorf`, `fmt.Sprintf` (with `SprintfOut`, the relation
its result satisfies) and `fmt.Printf`.
-/
module

public import Perennial.Proof.io
public import Perennial.Code.fmt
public import Perennial.GeneratedProof.fmt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

/-! ## The output of `Sprintf`

`SprintfOut format args out`: `out` is a possible result of the model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`) on `format` and the arguments `args`. Bytes are `w8`:
`W8 37` is `%`, `W8 115` is `s`. -/

/-- At `%` followed by `f`, with arguments `args` left: whether the model formats the directive
(`%%`, or `%s` of an interface holding a `string`); at any other directive the rest of the
output is arbitrary. -/
def SimpleDirective [FfiSyntax] : GoString → List GoInterface → Prop
  | c :: _, args =>
      c = W8 37 ∨ (c = W8 115 ∧ ∃ ii rest, args = interface.ok ii :: rest ∧ ii.ty = go.string)
  | [], _ => False

/-- `SprintfOut format args out`: `out` is a possible result of `fmt.Sprintf(format, args...)`,
as the model of `Sprintf` formats it. Bytes other than `%` are copied, `%%` gives `%`, `%s` with
an interface holding a `string` next gives that string; at any other directive, and after the
format if arguments remain unused, the rest of the output is arbitrary. -/
inductive SprintfOut [FfiSyntax] [GoGlobalContext] :
    GoString → List GoInterface → GoString → Prop
  /-- The end of the format, every argument used: nothing more. -/
  | done : SprintfOut [] [] []
  /-- The end of the format, arguments unused: an arbitrary suffix (Go's `%!(EXTRA ...)`). -/
  | extra (a : GoInterface) (args : List GoInterface) (junk : GoString) :
      SprintfOut [] (a :: args) junk
  /-- A byte other than `%` is copied. -/
  | byte (c : w8) (f : GoString) (args : List GoInterface) (out : GoString) :
      c ≠ W8 37 → SprintfOut f args out → SprintfOut (c :: f) args (c :: out)
  /-- `%%` gives `%`. -/
  | percent (f : GoString) (args : List GoInterface) (out : GoString) :
      SprintfOut f args out → SprintfOut (W8 37 :: W8 37 :: f) args (W8 37 :: out)
  /-- `%s` of an interface holding the string `x` gives `x`, and consumes the argument. -/
  | str (x : GoString) (f : GoString) (args : List GoInterface) (out : GoString) :
      SprintfOut f args out →
      SprintfOut (W8 37 :: W8 115 :: f) (interface.mkOk go.string #x :: args) (x ++ out)
  /-- Any other directive (or a trailing lone `%`): the rest of the output is arbitrary. -/
  | other (f : GoString) (args : List GoInterface) (junk : GoString) :
      ¬ SimpleDirective f args → SprintfOut (W8 37 :: f) args junk

/-- The arguments' dynamic types tell the truth about `string`s: an argument whose dynamic type
is `string` holds a string. (Go's typing guarantees it; a `GoInterface` does not.) -/
def StringArgsWf [FfiSyntax] [GoGlobalContext] (args : List GoInterface) : Prop :=
  ∀ ii, interface.ok ii ∈ args → ii.ty = go.string → ∃ x : GoString, ii.v = #x

section prefix_lemmas
variable [FfiSyntax] [GoGlobalContext]

theorem StringArgsWf.nil : StringArgsWf ([] : List GoInterface) := by
  intro ii h; simp at h

theorem StringArgsWf.cons_string (x : GoString) (args : List GoInterface)
    (h : StringArgsWf args) : StringArgsWf (interface.mkOk go.string #x :: args) := by
  intro ii hmem hty
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq; exact ⟨x, rfl⟩
  · exact h ii hmem hty

theorem StringArgsWf.cons_other (t : go.GoType) (v : val) (args : List GoInterface)
    (ht : t ≠ go.string) (h : StringArgsWf args) :
    StringArgsWf (interface.mkOk t v :: args) := by
  intro ii hmem hty
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq; exact absurd hty ht
  · exact h ii hmem hty

/-- `Sprintf("%s" + f, x, ...)` begins with `x`. -/
theorem SprintfOut.str_prefix [go.IntoValInj GoString] (x f : GoString)
    (args : List GoInterface) (out : GoString)
    (h : SprintfOut (go!"%s" ++ f) (interface.mkOk go.string #x :: args) out) : x <+: out := by
  have hfmt : go!"%s" ++ f = W8 37 :: W8 115 :: f := rfl
  rw [hfmt] at h
  generalize hF : (W8 37 :: W8 115 :: f) = F at h
  generalize hA : (interface.mkOk go.string #x :: args) = A at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte c _ _ _ hc _ =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.1.symm hc
  | percent =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.2.1 (by decide)
  | str y _ _ out' _ =>
    simp only [List.cons.injEq, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hA
    rw [go.intoVal_inj hA.1]
    exact ⟨out', rfl⟩
  | other _ _ _ hnot =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    subst hA
    exact absurd (Or.inr ⟨rfl, _, _, rfl, rfl⟩) hnot

/-- `Sprintf("%s%x", x, n)` begins with `x` (whatever the second argument). -/
theorem SprintfOut.str_x_prefix [go.IntoValInj GoString] (x : GoString)
    (args : List GoInterface) (out : GoString)
    (h : SprintfOut go!"%s%x" (interface.mkOk go.string #x :: args) out) : x <+: out :=
  SprintfOut.str_prefix x go!"%x" args out h

/-! Tests of `SprintfOut` and `StringArgsWf`. -/

example (pfx : GoString) (n : w64) :
    StringArgsWf [interface.mkOk go.string #pfx, interface.mkOk go.int64 #n] :=
  .cons_string _ _ (.cons_other _ _ _ (by simp [go.int64, go.string]) .nil)

example (x : GoString) :
    SprintfOut go!"a%sb%%" [interface.mkOk go.string #x] (go!"a" ++ x ++ go!"b%") := by
  have : go!"a%sb%%" = W8 97 :: W8 37 :: W8 115 :: W8 98 :: W8 37 :: W8 37 :: [] := rfl
  rw [this]
  refine .byte _ _ _ _ (by decide) ?_
  simpa using (SprintfOut.str x _ _ _ (.byte _ _ _ _ (by decide) (.percent _ _ _ .done)))

end prefix_lemmas

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.fmt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.fmt :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.fmt get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) ssFree sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoSlice) space _ as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) ppFree sync.Pool.ty as _
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_slice_literal (V := GoArray w16 2)
    [array.mk 2 [W16 9, W16 13], array.mk 2 [W16 32, W16 32], array.mk 2 [W16 133, W16 133], array.mk 2 [W16 160, W16 160], array.mk 2 [W16 5760, W16 5760], array.mk 2 [W16 8192, W16 8202], array.mk 2 [W16 8232, W16 8233], array.mk 2 [W16 8239, W16 8239], array.mk 2 [W16 8287, W16 8287], array.mk 2 [W16 12288, W16 12288]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  iframe Hown
  is_pkg_init_finish

/-- `fmt.Errorf(format, args...)` returns a non-nil error whose `Error()` returns some string.
The model of `Errorf` (`Perennial/TrustedCode/fmt.lean`) does not format: it is
`errors.New(format)`, ignoring the arguments, so this follows from `errors.wp_New`. (The
statement does not give back `args_sl ↦* args`, which the model never reads.) -/
theorem wp_Errorf (format : GoString) (args_sl : GoSlice) (args : List GoAny) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  wp_start as _
  wp_apply errors.wp_New as %err #Herr
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

/-- The helper `fmt.arbitraryString` of the model of `Sprintf` returns some string. -/
theorem wp_arbitraryString :
    {{ (True : IProp GF) }}
      (App (Val arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

/-- `fmt.Sprintf(format, args...)` returns a string `s` with `SprintfOut format args s`: `%s` of a
`string` and `%%` are formatted, the rest of the output is arbitrary from any other directive
on (see the model of `Sprintf`, `Perennial/TrustedCode/fmt.lean`). The arguments must hold
strings wherever their dynamic type is `string` (`StringArgsWf`). -/
theorem wp_Sprintf (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (Hxs : StringArgsWf xs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜SprintfOut format xs s⌝ }} := by
  wp_start as Hsl
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n k : w64) (acc : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "argNum" ∷ argNum_ptr ↦ k ∗
      "out" ∷ out_ptr ↦ acc ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (format.length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜∀ r, SprintfOut (format.drop (sint.nat n)) (xs.drop (sint.nat k)) r →
        SprintfOut format xs (acc ++ r)⌝) $$ [i argNum out]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl, show zero_val GoString = [] from rfl,
      show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => by simpa using h⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat n]? = some c ∧
        format.drop (sint.nat n) = c :: format.drop (sint.nat n + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    rw [Hc]
    wp_auto
    wp_if_destruct
    · -- `%`
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_if_destruct
      · -- `%` and a byte `d` after it
        have Hlt1 : sint.nat n + 1 < format.length := by word
        obtain ⟨d, Hd, Hdrop1⟩ : ∃ d, format[sint.nat n + 1]? = some d ∧
            format.drop (sint.nat n + 1) = d :: format.drop (sint.nat n + 2) :=
          ⟨_, List.getElem?_eq_getElem Hlt1, List.drop_eq_getElem_cons Hlt1⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, Hd]
        wp_auto
        wp_if_destruct
        · -- `%%`
          wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
          rw [show sint.nat (n + W64 2) = sint.nat n + 2 by word] at h
          have := Hacc (W8 37 :: r) (by rw [Hdrop, Hdrop1]; exact .percent _ _ _ h)
          simpa using this
        · -- `%` and a byte `d` other than `%`
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
          wp_if_destruct
          · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, Hd]
            wp_auto
            wp_if_destruct
            · -- `%s`
              wp_if_destruct
              · -- an argument is left
                simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z args_sl.len from ⟨Hk.1, Hif⟩,
                  and_self, ↓reduceIte]
                have Hklt : sint.nat k < xs.length := by word
                obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
                    xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
                  ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
                wp_apply wp_load_slice_index args_sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
                · iframe; ipureintro; exact Hx
                have Hxmem : x ∈ xs := List.mem_of_getElem? Hx
                cases x with
                | nil =>
                  wp_auto
                  wp_apply wp_arbitraryString as %junk -
                  wp_for_post
                  iapply HΦ
                  iframe
                  ipureintro
                  refine Hacc junk ?_
                  rw [Hdrop]
                  refine .other _ _ _ ?_
                  rw [Hdrop1, Hdropk]
                  simp [SimpleDirective]
                | ok ii =>
                  by_cases hty : ii.ty = go.string
                  · obtain ⟨sx, hv⟩ := Hxs ii Hxmem hty
                    obtain ⟨ty, v⟩ := ii
                    simp only at hty hv
                    subst hty hv
                    simp only [↓reduceIte, _root_.decide_true]
                    wp_auto
                    wp_for_post
                    iframe
                    iexists _, _, _
                    iframe
                    ipureintro
                    refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
                    rw [show sint.nat (n + W64 2) = sint.nat n + 2 by word,
                      show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
                    have := Hacc (sx ++ r) (by rw [Hdrop, Hdrop1, Hdropk]; exact .str sx _ _ _ h)
                    simpa using this
                  · simp only [hty, ↓reduceIte, decide_false]
                    wp_auto
                    wp_apply wp_arbitraryString as %junk -
                    wp_for_post
                    iapply HΦ
                    iframe
                    ipureintro
                    refine Hacc junk ?_
                    rw [Hdrop]
                    refine .other _ _ _ ?_
                    rw [Hdrop1, Hdropk]
                    simp [SimpleDirective, hty]
              · -- no argument left
                wp_apply wp_arbitraryString as %junk -
                wp_for_post
                iapply HΦ
                iframe
                ipureintro
                refine Hacc junk ?_
                rw [Hdrop]
                refine .other _ _ _ ?_
                have Hnil : xs.drop (sint.nat k) = [] := List.drop_eq_nil_of_le (by word)
                rw [Hdrop1, Hnil]
                simp [SimpleDirective]
            · -- another verb
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine Hacc junk ?_
              rw [Hdrop]
              refine .other _ _ _ ?_
              rw [Hdrop1]
              simp only [SimpleDirective]
              rintro (h | ⟨h, -⟩) <;> contradiction
          · exfalso; word
      · -- a trailing `%`
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        wp_if_destruct
        · exfalso; word
        · wp_apply wp_arbitraryString as %junk -
          wp_for_post
          iapply HΦ
          iframe
          ipureintro
          refine Hacc junk ?_
          rw [Hdrop]
          refine .other _ _ _ ?_
          rw [List.drop_eq_nil_of_le (by word)]
          simp [SimpleDirective]
    · -- a byte other than `%`
      rw [Hc]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [c]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #c)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hc_sl, -⟩
      wp_apply wp_bytes_to_string $$ Hc_sl as -
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at h
      have := Hacc (c :: r) (by rw [Hdrop]; exact .byte c _ _ _ Hif h)
      simpa using this
  · -- the end of the format
    have Hnot : ¬ sint.Z n < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    rw [show sint.nat n = format.length by word, List.drop_length] at Hacc
    wp_auto
    wp_if_destruct
    · -- arguments are left
      wp_apply wp_arbitraryString as %junk -
      iapply HΦ
      iframe
      ipureintro
      refine Hacc junk ?_
      rw [List.drop_eq_getElem_cons (show sint.nat k < xs.length by word)]
      exact .extra _ _ _
    · iapply HΦ
      iframe
      ipureintro
      have := Hacc [] (by rw [List.drop_eq_nil_of_le (by word)]; exact .done)
      simpa using this

/-- `fmt.Printf(format, args...)` returns; the output is not modelled, nor the results. -/
theorem wp_Printf (format : GoString) (args_sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (App (Val (@! Printf)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); True }} := by
  wp_start
  iapply HΦ
  itrivial

end wps

end fmt

end Perennial
end
