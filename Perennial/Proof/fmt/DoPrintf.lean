/-
The spec of the helper `doPrintf` of the model of `fmt` (`Perennial/TrustedCode/fmt.lean`), which
`Sprintf`, `Printf` and `Errorf` run: the formatted string (`SprintfOut`), the calls of the
arguments' methods Go makes (through `visitRest`), and the arguments of the `%w` directives.
-/
module

public import Perennial.Proof.fmt.VisitModel
public import Perennial.Proof.fmt.BytesModel

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section lemmas
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

theorem wrapArgsFrom_append_noW (j n : Nat) (pre ds : List Directive)
    (h : ∀ d ∈ pre, d.verb ≠ W8 119) :
    wrapArgsFrom j (pre ++ ds) n = wrapArgsFrom (j + pre.length) ds n := by
  induction pre generalizing j with
  | nil => simp
  | cons d pre ih =>
    rw [List.cons_append, wrapArgsFrom_cons_ne _ _ (h d (by simp)),
      ih _ (fun e he => h e (by simp [he]))]
    simp only [List.length_cons]
    rw [show j + 1 + pre.length = j + (pre.length + 1) by omega]

theorem not_hasFmtSig_of_noFmtMethods {t : go.GoType} (h : NoFmtMethods t) : ¬ HasFmtSig t := by
  rintro (h' | h' | h' | h')
  · rw [h.1] at h'; cases h'
  · rw [h.2.1] at h'; cases h'
  · rw [h.2.2.1] at h'; cases h'
  · rw [h.2.2.2] at h'; cases h'

theorem inertTy_of_isStrArgType {t : go.GoType} (h : IsStrArgType t) : InertTy t := by
  rcases h with rfl | ⟨-, hu, hm⟩
  · exact .inl (.inl rfl)
  · exact .inr ⟨not_hasFmtSig_of_noFmtMethods hm, .inl hu⟩

theorem inertTy_of_isIntArgType {t : go.GoType} (h : IsIntArgType t) : InertTy t := by
  rcases h with hi | ⟨hi, hm⟩
  · exact .inl (.inr (.inr (.inl hi)))
  · exact .inr ⟨not_hasFmtSig_of_noFmtMethods hm, .inr hi⟩

theorem wrapArgsFrom_bound {k n j : Nat} {ds : List Directive} (h : j ∈ wrapArgsFrom k ds n) :
    k ≤ j ∧ j < n := by
  induction ds generalizing k with
  | nil => simp [wrapArgsFrom] at h
  | cons d ds ih =>
    simp only [wrapArgsFrom, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hc; simp only [List.mem_singleton] at h; subst h; exact ⟨Nat.le_refl _, hc.2⟩
      · simp at h
    · have := ih h; omega

theorem doPrintf_exit_wrap {format : GoString} {n k : Nat} {xs : List GoInterface}
    {ws : List w64} {unk : Bool}
    (Hpre : ∀ ds, fmtDirectives format = some ds → ∃ pre ds', ds = pre ++ ds' ∧
      (∀ d ∈ pre, d.verb ≠ W8 119) ∧ pre.length = k ∧
      fmtDirectivesAux none (format.drop n) = some ds')
    (Hvr : (unk = true → ArgsWf xs ∧ fmtDirectivesAux none (format.drop n) = none) ∧
      (unk = false → ∃ ds, fmtDirectivesAux none (format.drop n) = some ds ∧
        ws = (wrapArgsFrom k ds xs.length).map (fun j : Nat => W64 (j : Int)))) :
    (unk = true → ArgsWf xs ∧ fmtDirectives format = none) ∧
    (unk = false → ∀ ds, fmtDirectives format = some ds →
      ws = (wrapArgs ds xs.length).map (fun j : Nat => W64 (j : Int))) ∧
    (unk = false → ∀ w ∈ ws, ∃ j : Nat, w = W64 (j : Int) ∧ j < xs.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hu
    obtain ⟨hwf, hnone⟩ := Hvr.1 hu
    refine ⟨hwf, ?_⟩
    cases hf : fmtDirectives format with
    | none => rfl
    | some ds =>
      obtain ⟨pre, ds', -, -, -, hds'⟩ := Hpre ds hf
      rw [hnone] at hds'; cases hds'
  · intro hu ds hds
    obtain ⟨dr, hdr, hws⟩ := Hvr.2 hu
    obtain ⟨pre, ds', rfl, hnw, hlen, hds'⟩ := Hpre ds hds
    rw [hdr] at hds'
    cases hds'
    rw [hws, wrapArgs, wrapArgsFrom_append_noW _ _ _ _ hnw, hlen, Nat.zero_add]
  · intro hu w hw
    obtain ⟨dr, -, hws⟩ := Hvr.2 hu
    rw [hws] at hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    exact ⟨j, rfl, (wrapArgsFrom_bound hj).2⟩

end lemmas

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

include sem package_sem hG in
theorem inertTy_no_sig {t : go.GoType} (hi : InertTy t) {m : GoString}
    (hm : m = go!"Error" ∨ m = go!"String") (h : methodSet t !! m = some noArgStringSig) : False := by
  rcases hi with hb | ⟨hn, -⟩
  · have := noFmtMethods_basic (hG := hG) t hb
    rcases hm with rfl | rfl
    · rw [this.2.2.1] at h; cases h
    · rw [this.2.2.2] at h; cases h
  · rcases hm with rfl | rfl
    · exact hn (.inr (.inr (.inl h)))
    · exact hn (.inr (.inr (.inr h)))

theorem isRefKind_named {n} {args : List go.GoType} :
    ¬ IsRefKind (go.GoType.Named n args) := by
  simp [IsRefKind]

include sem package_sem in
theorem underlying_basic {t : go.GoType} (h : IsBasicType t) : underlying t = t := by
  rcases h with rfl | rfl | h | rfl | rfl | rfl
  all_goals try exact go.is_underlying
  exact underlying_intType _ h

theorem isBasicType_named {t : go.GoType} (h : IsBasicType t) : ∃ n args, t = go.GoType.Named n args := by
  rcases h with rfl | rfl | h | rfl | rfl | rfl
  all_goals try exact ⟨_, _, rfl⟩
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

include sem package_sem in
theorem inertTy_not_ref {t : go.GoType} (hi : InertTy t) (h : IsRefKind (underlying t)) : False := by
  rcases hi with hb | ⟨-, hs | hi⟩
  · rw [underlying_basic hb] at h
    obtain ⟨n, args, rfl⟩ := isBasicType_named hb
    exact isRefKind_named h
  · rw [hs] at h; exact isRefKind_named h
  · obtain ⟨n, args, he⟩ := isBasicType_named (Or.inr (Or.inr (Or.inl hi)) : IsBasicType (underlying t))
    rw [he] at h; exact isRefKind_named h

/-- What `formatArg` needs of an inert argument (`ArgWf`, where it reads the argument), from its
directive's `argOkAt`. -/
theorem argWf_of_argOkAt_inert (mv : List w8) (d : Directive) (ii : GoInterfaceOk)
    (hi : InertTy ii.ty) (hT : d.verb ≠ W8 84) :
    argOkAt (GF := GF) mv d (.ok ii) ⊢ ⌜ArgWf ii⌝ := by
  unfold argOkAt
  iintro (%Hwf | %Hni | ⟨%Hm, Hok⟩ | %HT | %Hp)
  · ipureintro; exact Hwf
  · exfalso
    rcases Hni.2.2.2 with h | h
    · exact inertTy_no_sig hi (.inl rfl) h
    · exact inertTy_no_sig hi (.inr rfl) h
  · iunfold argOk at Hok
    icases Hok with (%Hwf | ⟨-, %hE⟩ | ⟨-, %hS⟩)
    · ipureintro; exact Hwf
    · exfalso; exact inertTy_no_sig hi (.inl rfl) hE.2
    · exfalso; exact inertTy_no_sig hi (.inr rfl) hS.2.2.1
  · exfalso; exact hT HT
  · exfalso; exact inertTy_not_ref hi Hp.2

/-- An argument `argOkAt` a directive `%c` of a `byteVerbs` verb is no slice (no `[]byte`, no
`[]string`): the specs admit a slice only under `%T` and `%p`. -/
theorem notBytes_of_argOkAt (mv : List w8) (c : w8) (hc : c ∈ byteVerbs) (ii : GoInterfaceOk)
    (t : go.GoType) :
    argOkAt (GF := GF) mv ⟨c, false⟩ (.ok ii) ⊢ ⌜ii.ty ≠ go.SliceType t⌝ := by
  unfold argOkAt
  iintro (%Hwf | %Hni | ⟨%Hm, Hok⟩ | %HT | %Hp)
  · ipureintro; exact ne_SliceType_of_argWf t Hwf
  · ipureintro; exact ne_SliceType_of_kind t (.inr Hni.2.1)
  · iunfold argOk at Hok
    icases Hok with (%Hwf | ⟨-, %hE⟩ | ⟨-, %hS⟩)
    · ipureintro; exact ne_SliceType_of_argWf t Hwf
    · ipureintro; exact ne_SliceType_of_method t hE.2
    · ipureintro; exact ne_SliceType_of_method t hS.2.2.1
  · exfalso
    simp only at HT
    subst HT
    simp [byteVerbs] at hc
  · exfalso
    obtain ⟨HP, -⟩ := Hp
    simp only at HP
    subst HP
    simp [byteVerbs] at hc

/-- An argument `argOkAtB` a directive `%c` of a `byteVerbs` verb that is a `[]byte` or a
`[]string` is lent. -/
theorem lent_of_argOkAtB (B : GoInterface → Option Lent) (mv : List w8) (c : w8)
    (hc : c ∈ byteVerbs) (ii : GoInterfaceOk) :
    argOkAtB (GF := GF) B mv ⟨c, false⟩ (.ok ii) ⊢
      ⌜(ii.ty = go.SliceType go.byte ∨ ii.ty = go.SliceType go.string) → (B (.ok ii)).isSome⌝ := by
  unfold argOkAtB
  iintro (Hd | %HB)
  · ihave %hn := notBytes_of_argOkAt _ c hc ii go.byte $$ Hd
    ihave %hn' := notBytes_of_argOkAt _ c hc ii go.string $$ Hd
    ipureintro; rintro (h | h)
    · exact absurd h hn
    · exact absurd h hn'
  · ipureintro; intro _; exact HB

/-- What `formatArg` needs of an inert argument (`ArgWf`), from its directive's `argOkAtB`: a lent
argument is a `[]byte` or a `[]string`, which is not inert. -/
theorem argWf_of_argOkAtB_inert (B : GoInterface → Option Lent) (mv : List w8) (d : Directive)
    (ii : GoInterfaceOk) (hi : InertTy ii.ty) (hT : d.verb ≠ W8 84)
    (hB : (B (.ok ii)).isSome → ∃ t, ii.ty = go.SliceType t) :
    argOkAtB (GF := GF) B mv d (.ok ii) ⊢ ⌜ArgWf ii⌝ := by
  unfold argOkAtB
  iintro (Hd | %HB)
  · iapply argWf_of_argOkAt_inert _ d ii hi hT; iexact Hd
  · exfalso
    obtain ⟨t, h⟩ := hB HB
    rw [h] at hi
    exact inertTy_not_ref hi (by rw [underlying_SliceType]; trivial)

/-- The helper `fmt.doPrintf`: for arguments `argsOk` the format under the verbs of its mode,
the formatted string (`SprintfOut`), after the calls Go makes of the arguments' methods; the
arguments' slice comes back; and the arguments of the `%w` directives, unless the model gave up
(`unknown`) at a directive `fmtDirectives` refuses, every argument being `ArgWf`. -/
theorem wp_doPrintfB (B : GoInterface → Option Lent) (dqb : DFrac) (format : GoString)
    (sl : GoSlice) (xs : List GoInterface) (dq : DFrac) (wrapErrs : Bool) :
    {{ sl ↦*{dq} xs ∗ bytesOwn dqb B xs ∗ argsOkB (GF := GF) B (modeVerbs wrapErrs) format xs }}
      (App (App (App (Val doPrintf) (Val #format)) (Val #sl)) (Val #wrapErrs))
    {{ (s : GoString) (wsl : GoSlice) (unknown : Bool), RET (PairV (PairV #s #wsl) #unknown);
        sl ↦*{dq} xs ∗ bytesOwn dqb B xs ∗ ⌜SprintfOutB B format xs s⌝ ∗
        ∃ ws : List w64, wsl ↦* ws ∗
        ⌜(unknown = true → ArgsWf xs ∧ fmtDirectives format = none) ∧
         (unknown = false → ∀ ds, fmtDirectives format = some ds →
            ws = (wrapArgs ds xs.length).map (fun j : Nat => W64 (j : Int))) ∧
         (unknown = false → ∀ w ∈ ws, ∃ j : Nat, w = W64 (j : Int) ∧ j < xs.length)⌝ }} := by
  iintro %Φ ⟨Hsl, Hown, Hok⟩ HΦ
  unfold doPrintf
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  icases bytesOwn_ty dqb B xs $$ Hown with ⟨Hown, %HBty⟩
  ihave IH : iprop(∃ (n k : w64) (acc : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "argNum" ∷ argNum_ptr ↦ k ∗
      "out" ∷ out_ptr ↦ acc ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (format.length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜∀ r, SprintfOutB B (format.drop (sint.nat n)) (xs.drop (sint.nat k)) r →
        SprintfOutB B format xs (acc ++ r)⌝ ∗
      "%Hpre" ∷ ⌜∀ ds, fmtDirectives format = some ds → ∃ pre ds', ds = pre ++ ds' ∧
        (∀ d ∈ pre, d.verb ≠ W8 119) ∧ pre.length = sint.nat k ∧
        fmtDirectivesAux none (format.drop (sint.nat n)) = some ds'⌝ ∗
      "#Hargs" ∷ (⌜ArgsWf xs⌝ ∨ ∃ ds, ⌜fmtDirectivesAux none (format.drop (sint.nat n)) = some ds⌝ ∗
          argsOkAtB (GF := GF) B (modeVerbs wrapErrs) ds (xs.drop (sint.nat k)))) $$ [i argNum out Hok]
  · ihave #Hargs0 : iprop(⌜ArgsWf xs⌝ ∨ ∃ ds, ⌜fmtDirectivesAux none (format.drop 0) = some ds⌝ ∗
        argsOkAtB (GF := GF) B (modeVerbs wrapErrs) ds (xs.drop 0)) $$ [Hok]
    · iunfold argsOkB at Hok
      icases Hok with (%Hwf | ⟨%ds, %Hds, #Hds⟩)
      · ileft; ipureintro; exact Hwf
      · iright; iexists ds; isplitr
        · ipureintro; simpa [fmtDirectives] using Hds
        · simp only [List.drop_zero]; iexact Hds
    iexists _, _, _
    rw [show zero_val w64 = W64 0 from rfl, show zero_val GoString = [] from rfl,
      show sint.nat (W64 0) = 0 from rfl]
    iframe
    iframe Hargs0
    ipureintro
    refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => by simpa using h,
      fun ds hds => ⟨[], ds, rfl, by simp, rfl, by simpa [fmtDirectives] using hds⟩⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  have Hflen' : (format.length : Int) < 2 ^ 63 := by word
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat n]? = some c ∧
        format.drop (sint.nat n) = c :: format.drop (sint.nat n + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    rw [if_pos (show 0 ≤ sint.Z n by word), Hc]
    wp_auto
    wp_if_destruct
    · -- `%`
      have hpct : fmtDirectivesAux none (format.drop (sint.nat n)) =
          fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat n + 1)) := by
        rw [Hdrop]; exact fmtDirectivesAux_pct _
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_if_destruct
      · -- `%` and a byte `d` after it
        have Hlt1 : sint.nat n + 1 < format.length := by word
        obtain ⟨d, Hd, Hdrop1⟩ : ∃ d, format[sint.nat n + 1]? = some d ∧
            format.drop (sint.nat n + 1) = d :: format.drop (sint.nat n + 2) :=
          ⟨_, List.getElem?_eq_getElem Hlt1, List.drop_eq_getElem_cons Hlt1⟩
        rw [if_pos (show 0 ≤ sint.Z (n + W64 1) by word),
          show sint.nat (n + W64 1) = sint.nat n + 1 by word, Hd]
        wp_auto
        wp_if_destruct
        · -- `%%`
          have hpp : fmtDirectivesAux none (format.drop (sint.nat n)) =
              fmtDirectivesAux none (format.drop (sint.nat (n + W64 2))) := by
            rw [Hdrop, Hdrop1, show sint.nat (n + W64 2) = sint.nat n + 2 by word]
            exact fmtDirectivesAux_pct_pct _
          wp_for_post
          iframe
          iexists _, _, _
          rw [← hpp]
          iframe
          iframe Hargs
          ipureintro
          refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_, Hpre⟩
          rw [show sint.nat (n + W64 2) = sint.nat n + 2 by word] at h
          have := Hacc (W8 37 :: r) (by rw [Hdrop, Hdrop1]; exact .percent _ _ _ h)
          simpa using this
        · -- `%` and a byte `d` other than `%`
          have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
            rw [Hdrop1]; simpa using Hif
          wp_if_destruct
          · -- an argument is left: is it inert?
            have Hklt : sint.nat k < xs.length := by word
            obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
                xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
              ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
              _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            -- `formatSlice`: a `[]byte` under its verbs is lent
            have HxBty : ∀ ii, x = interface.ok ii → (B x).isSome → ∃ t, ii.ty = go.SliceType t := by
              intro ii h hs
              obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hs
              obtain ⟨ii', h', hty⟩ := HBty x (List.mem_of_getElem? Hx) L hL
              rw [h] at h'; cases h'
              cases L with
              | bytes _ => exact ⟨_, hty⟩
              | strings _ => exact ⟨_, hty⟩
            have hpct' : fmtDirectivesAux none (W8 37 :: format.drop (sint.nat n + 1)) =
                fmtDirectivesAux none (format.drop (sint.nat n)) := by
              rw [Hdrop]
            ihave %HxB : iprop(⌜∀ c, (format.drop (sint.nat n + 1)).head? = some c → c ∈ byteVerbs →
                ∀ ii, x = interface.ok ii →
                  (ii.ty = go.SliceType go.byte ∨ ii.ty = go.SliceType go.string) → (B x).isSome⌝) $$ [Hargs]
            · icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
              · ipureintro; intro _ _ _ ii h hty
                rcases hty with hty | hty
                · exact absurd hty (ne_SliceType_of_argWf go.byte (Hwf ii (h ▸ List.mem_of_getElem? Hx)))
                · exact absurd hty (ne_SliceType_of_argWf go.string (Hwf ii (h ▸ List.mem_of_getElem? Hx)))
              · cases x with
                | nil => ipureintro; intro _ _ _ ii h; cases h
                | ok ii =>
                  by_cases hcond : ∃ c', (format.drop (sint.nat n + 1)).head? = some c' ∧
                      c' ∈ byteVerbs
                  · obtain ⟨c', hc1, hc2⟩ := hcond
                    have hcons : format.drop (sint.nat n + 1) =
                        c' :: (format.drop (sint.nat n + 1)).tail := by
                      cases h : format.drop (sint.nat n + 1) with
                      | nil => rw [h] at hc1; cases hc1
                      | cons a r => rw [h] at hc1; cases hc1; rfl
                    have hL := fmtDirectivesAux_byteVerb (format.drop (sint.nat n + 1)).tail hc2
                    rw [← hcons, ← Hdrop, Hds] at hL
                    cases hL' : fmtDirectivesAux none (format.drop (sint.nat n + 1)).tail with
                    | none => rw [hL'] at hL; cases hL
                    | some L' =>
                      rw [hL'] at hL
                      simp only [Functor.map, Option.map_some, Option.some.injEq] at hL
                      subst hL
                      rw [Hdropk]
                      simp only [argsOkAtB]
                      icases Hds with ⟨Hd, -⟩
                      ihave %hn := lent_of_argOkAtB B _ c' hc2 ii $$ Hd
                      ipureintro; intro _ _ _ ii' h; cases h; exact hn
                  · ipureintro; intro c'' h1 h2; exact absurd ⟨c'', h1, h2⟩ hcond
            icases (bytesOwn_lookup_acc (k := sint.nat k) Hx) $$ Hown with ⟨Hxb, Hclose⟩
            wp_apply (wp_formatSliceB B dqb format n x ⟨Hn.1, by word⟩ HxB) $$ [$Hxb]
              as %bs_s %bs_next %bs_ok ⟨Hxb, %Hb1, %Hb2⟩
            ihave Hown := Hclose $$ Hxb
            cases bs_ok
            rotate_left
            · -- formatted as a lent `[]byte`
              obtain ⟨-, Hn1, Hn2, Hout, Hstep⟩ := Hb1 rfl
              ihave #Hargs' : iprop(⌜ArgsWf xs⌝ ∨ ∃ ds,
                  ⌜fmtDirectivesAux none (format.drop (sint.nat bs_next)) = some ds⌝ ∗
                  argsOkAtB (GF := GF) B (modeVerbs wrapErrs) ds (xs.drop (sint.nat (k + W64 1)))) $$ [Hargs]
              · icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
                · ileft; ipureintro; exact Hwf
                · iright
                  obtain ⟨d', L', rfl, -, -, hL'⟩ := Hstep ds (by rw [hpct', Hds])
                  iexists L'
                  isplitr
                  · ipureintro; exact hL'
                  rw [Hdropk, show sint.nat (k + W64 1) = sint.nat k + 1 by word]
                  simp only [argsOkAtB]
                  icases Hds with ⟨-, Hds⟩
                  iexact Hds
              try wp_auto
              wp_for_post
              iframe
              iexists _, _, _
              iframe
              iframe Hargs'
              ipureintro
              refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_, fun ds hds => ?_⟩
              · rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
                have := Hacc (bs_s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
                simpa using this
              · obtain ⟨pre, ds', rfl, hnw, hlen, hds'⟩ := Hpre ds hds
                obtain ⟨d', L', rfl, hw, -, hL'⟩ := Hstep ds' (by rw [hpct', hds'])
                refine ⟨pre ++ [d'], L', by simp, fun e he => ?_, ?_, hL'⟩
                · rcases List.mem_append.mp he with he | he
                  · exact hnw e he
                  · rw [List.mem_singleton.mp he]; exact hw
                · rw [List.length_append, hlen]; simp only [List.length_singleton]; word
            have HnB := Hb2 rfl
            try wp_auto
            wp_if_destruct
            rotate_left
            · exfalso; word
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
              _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            wp_apply wp_inert as %bi %Hbi
            cases bi
            · -- not inert: from here on, `visitRest`
              have hns : ∀ ii, x = interface.ok ii → ¬ IsStrArgType ii.ty ∧ ¬ IsIntArgType ii.ty := by
                intro ii h
                refine ⟨fun hs => ?_, fun hi => ?_⟩
                · exact absurd (Hbi.2 (.inr ⟨ii, h, inertTy_of_isStrArgType hs⟩)) (by simp)
                · exact absurd (Hbi.2 (.inr ⟨ii, h, inertTy_of_isIntArgType hi⟩)) (by simp)
              wp_auto
              wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
                $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
              rw [Hdrop, Hdropk]
              exact .other _ _ _ (not_simpleDirective _ _ _ Hnp
                (.inr fun ii h => (hns ii h).1) (.inr fun ii h => (hns ii h).2)
                (.inr fun ii h => (hns ii h).2)) (HnB _).1 (HnB _).2
            -- inert: `formatArg`
            have HxIn : ∀ ii, x = interface.ok ii → InertTy ii.ty := by
              intro ii h
              rcases Hbi.1 rfl with hn | ⟨ii', h', hi⟩
              · rw [h] at hn; cases hn
              · rw [h] at h'; cases h'; exact hi
            ihave %HxWf : iprop(⌜((format.drop (sint.nat n + 1)).head? = some (W8 115) ∨
                (format.drop (sint.nat n + 1)).head? = some (W8 118) ∨
                (format.drop (sint.nat n + 1)).head? = some (W8 120) ∨
                (parseIntVerb (format.drop (sint.nat n + 1))).isSome) →
                ∀ ii, x = interface.ok ii → ArgWf ii⌝) $$ [Hargs]
            · by_cases hcond : ((format.drop (sint.nat n + 1)).head? = some (W8 115) ∨
                  (format.drop (sint.nat n + 1)).head? = some (W8 118) ∨
                  (format.drop (sint.nat n + 1)).head? = some (W8 120) ∨
                  (parseIntVerb (format.drop (sint.nat n + 1))).isSome)
              · obtain ⟨rest, hstep⟩ := auxStepF_of_cond _ hcond
                icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
                · ipureintro; intro _ ii h; exact Hwf ii (h ▸ List.mem_of_getElem? Hx)
                · obtain ⟨d', L', rfl, -, hT, -⟩ := hstep ds (by rw [hpct', Hds])
                  rw [Hdropk]
                  simp only [argsOkAtB]
                  icases Hds with ⟨Hd, -⟩
                  cases x with
                  | nil => ipureintro; intro _ ii h; cases h
                  | ok ii =>
                    ihave %hw := argWf_of_argOkAtB_inert B _ d' ii (HxIn ii rfl) hT (fun hs => HxBty ii rfl hs) $$ Hd
                    ipureintro; intro _ ii' h; cases h; exact hw
              · ipureintro; intro h; exact absurd h hcond
            wp_auto
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
              _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            wp_apply wp_formatArg B format n x ⟨Hn.1, by word⟩ HxWf as %s %next %ok ⟨%Hf1, %Hf2⟩
            cases ok
            · -- not formatted: from here on, `visitRest`
              wp_auto
              wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
                $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
              rw [Hdrop, Hdropk]
              exact .other _ _ _ (Hf2 rfl Hnp _) (HnB _).1 (HnB _).2
            · obtain ⟨Hn1, Hn2, Hout, Hstep⟩ := Hf1 rfl
              ihave #Hargs' : iprop(⌜ArgsWf xs⌝ ∨ ∃ ds,
                  ⌜fmtDirectivesAux none (format.drop (sint.nat next)) = some ds⌝ ∗
                  argsOkAtB (GF := GF) B (modeVerbs wrapErrs) ds (xs.drop (sint.nat (k + W64 1)))) $$ [Hargs]
              · icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
                · ileft; ipureintro; exact Hwf
                · iright
                  obtain ⟨d', L', rfl, -, -, hL'⟩ := Hstep ds (by rw [hpct', Hds])
                  iexists L'
                  isplitr
                  · ipureintro; exact hL'
                  rw [Hdropk, show sint.nat (k + W64 1) = sint.nat k + 1 by word]
                  simp only [argsOkAtB]
                  icases Hds with ⟨-, Hds⟩
                  iexact Hds
              wp_auto
              wp_for_post
              iframe
              iexists _, _, _
              iframe
              iframe Hargs'
              ipureintro
              refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_, fun ds hds => ?_⟩
              · rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
                have := Hacc (s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
                simpa using this
              · obtain ⟨pre, ds', rfl, hnw, hlen, hds'⟩ := Hpre ds hds
                obtain ⟨d', L', rfl, hw, -, hL'⟩ := Hstep ds' (by rw [hpct', hds'])
                refine ⟨pre ++ [d'], L', by simp, fun e he => ?_, ?_, hL'⟩
                · rcases List.mem_append.mp he with he | he
                  · exact hnw e he
                  · rw [List.mem_singleton.mp he]; exact hw
                · rw [List.length_append, hlen]; simp only [List.length_singleton]; word
          · -- no argument left
            try wp_auto
            wp_if_destruct
            · exfalso; word
            try wp_auto
            wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
              $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
            rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
            exact .other _ _ _ (not_simpleDirective_nil _ Hnp) (bytesSimple_nil _ _) (stringsSimple_nil _ _)
      · -- a trailing `%`
        have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
          rw [List.drop_eq_nil_of_le (by word)]; simp
        (try wp_auto)
        wp_if_destruct
        · -- an argument is left: whatever it is, `visitRest`
          have Hklt : sint.nat k < xs.length := by word
          obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
              xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
            ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
            _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
          · iframe; ipureintro; exact Hx
          have hdn : format.drop (sint.nat n + 1) = [] := List.drop_eq_nil_of_le (by word)
          -- `formatSlice`: nothing after the `%`
          icases (bytesOwn_lookup_acc (k := sint.nat k) Hx) $$ Hown with ⟨Hxb, Hclose⟩
          wp_apply (wp_formatSliceB B dqb format n x ⟨Hn.1, by word⟩ (by rw [hdn]; intro _ h; cases h))
            $$ [$Hxb] as %bs_s %bs_next %bs_ok ⟨Hxb, %Hb1, %Hb2⟩
          ihave Hown := Hclose $$ Hxb
          cases bs_ok
          rotate_left
          · exfalso
            obtain ⟨h2, -, h3, -⟩ := Hb1 rfl
            word
          try wp_auto
          wp_if_destruct
          rotate_left
          · exfalso; word
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
            _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
          · iframe; ipureintro; exact Hx
          wp_apply wp_inert as %bi %Hbi
          cases bi
          · try wp_auto
            wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
              $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
            rw [Hdrop, hdn]
            exact .other _ _ _ (by simp [SimpleDirective]) (by simp [BytesSimple]) (by simp [StringsSimple])
          · have HxWf : ((format.drop (sint.nat n + 1)).head? = some (W8 115) ∨
                (format.drop (sint.nat n + 1)).head? = some (W8 118) ∨
                (format.drop (sint.nat n + 1)).head? = some (W8 120) ∨
                (parseIntVerb (format.drop (sint.nat n + 1))).isSome) →
                ∀ ii, x = interface.ok ii → ArgWf ii := by
              rw [hdn]; simp [parseIntVerb]
            wp_auto
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, by word⟩,
              _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            wp_apply wp_formatArg B format n x ⟨Hn.1, by word⟩ HxWf as %s %next %ok ⟨%Hf1, %Hf2⟩
            cases ok
            · wp_auto
              wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
                $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
              rw [Hdrop, hdn]
              exact .other _ _ _ (by simp [SimpleDirective]) (by simp [BytesSimple]) (by simp [StringsSimple])
            · exfalso
              obtain ⟨-, -, -, Hstep⟩ := Hf1 rfl
              obtain ⟨_, _, h, -⟩ := Hstep [] (by rw [hdn]; rfl)
              cases h
        · -- no argument left
          try wp_auto
          wp_if_destruct
          · exfalso; word
          try wp_auto
          wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
            $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
          wp_apply wp_arbitraryString as %junk -
          wp_for_post
          iapply HΦ
          iframe
          ipureintro
          refine ⟨Hacc junk ?_, doPrintf_exit_wrap Hpre Hvr⟩
          rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
          exact .other _ _ _ (not_simpleDirective_nil _ Hnp) (bytesSimple_nil _ _) (stringsSimple_nil _ _)
    · -- a byte other than `%`
      have hlit : fmtDirectivesAux none (format.drop (sint.nat n)) =
          fmtDirectivesAux none (format.drop (sint.nat (n + W64 1))) := by
        rw [Hdrop, show sint.nat (n + W64 1) = sint.nat n + 1 by word]
        exact fmtDirectivesAux_lit _ Hif
      rw [if_pos (show 0 ≤ sint.Z n by word), Hc]
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
      rw [← hlit]
      iframe
      iframe Hargs
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_, Hpre⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at h
      have := Hacc (c :: r) (by rw [Hdrop]; exact .byte c _ _ _ Hif h)
      simpa using this
  · -- the end of the format
    have Hnot : ¬ sint.Z n < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    have Hend : sint.nat n = format.length := by word
    rw [Hend, List.drop_length] at Hacc Hpre
    wp_auto
    wp_if_destruct
    · -- arguments are left: under `%v`
      wp_apply (wp_visitRest B dqb format n sl xs dq k wrapErrs ⟨Hn.1, by word⟩ Hflen' Hk)
        $$ [$Hsl $Hown $Hargs] as %wsl %unk ⟨Hsl, Hown, %ws, Hws, %Hvr⟩
      wp_apply wp_arbitraryString as %junk -
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hacc junk ?_, doPrintf_exit_wrap (by rw [Hend, List.drop_length]; exact Hpre) Hvr⟩
      rw [List.drop_eq_getElem_cons (show sint.nat k < xs.length by word)]
      exact .extra _ _ _
    · ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        have := Hacc [] (by rw [List.drop_eq_nil_of_le (by word)]; exact .done)
        simpa using this
      iexists []
      isplitl []
      · iexact Hnil
      ipureintro
      refine ⟨fun h => (nomatch h), fun _ ds hds => ?_, fun _ w hw => by cases hw⟩
      · obtain ⟨pre, ds', rfl, hnw, -, hds'⟩ := Hpre ds hds
        simp only [fmtDirectivesAux, Option.some.injEq] at hds'
        subst hds'
        rw [wrapArgs, List.append_nil]
        have : wrapArgsFrom 0 (pre ++ []) xs.length = [] := by
          rw [wrapArgsFrom_append_noW _ _ _ _ hnw]; rfl
        rw [List.append_nil] at this
        rw [this]; rfl

/-- The helper `fmt.doPrintf`, with no bytes lent (`wp_doPrintfB`): for arguments `argsOk` the format
under the verbs of its mode, the formatted string (`SprintfOut`), after the calls Go makes of the
arguments' methods; the arguments' slice comes back; and the arguments of the `%w` directives, unless
the model gave up (`unknown`) at a directive `fmtDirectives` refuses, every argument being `ArgWf`. -/
theorem wp_doPrintf (format : GoString) (sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (wrapErrs : Bool) :
    {{ sl ↦*{dq} xs ∗ argsOk (GF := GF) (modeVerbs wrapErrs) format xs }}
      (App (App (App (Val doPrintf) (Val #format)) (Val #sl)) (Val #wrapErrs))
    {{ (s : GoString) (wsl : GoSlice) (unknown : Bool), RET (PairV (PairV #s #wsl) #unknown);
        sl ↦*{dq} xs ∗ ⌜SprintfOut format xs s⌝ ∗ ∃ ws : List w64, wsl ↦* ws ∗
        ⌜(unknown = true → ArgsWf xs ∧ fmtDirectives format = none) ∧
         (unknown = false → ∀ ds, fmtDirectives format = some ds →
            ws = (wrapArgs ds xs.length).map (fun j : Nat => W64 (j : Int))) ∧
         (unknown = false → ∀ w ∈ ws, ∃ j : Nat, w = W64 (j : Int) ∧ j < xs.length)⌝ }} := by
  iintro %Φ ⟨Hsl, Hok⟩ HΦ
  ihave Hown := bytesOwn_none (GF := GF) (DFrac.own 1) xs
  ihave #HokB := argsOkB_of_argsOk (GF := GF) (fun _ => none) _ _ _ $$ Hok
  wp_apply (wp_doPrintfB (fun _ => none) (DFrac.own 1) format sl xs dq wrapErrs) $$ [$Hsl $Hown $HokB]
    as %s %wsl %unk ⟨Hsl, -, %Hs, Hws⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hs.toSprintfOut

end wps

end fmt

end Perennial
