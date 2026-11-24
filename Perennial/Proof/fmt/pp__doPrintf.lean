/-
The proof of `fmt.(*pp).doPrintf`.
-/
module

public import Perennial.Spec.fmt.pp__doPrintf
public import Perennial.Spec.fmt.buffer__writeString
public import Perennial.Spec.fmt.buffer__writeByte
public import Perennial.Spec.fmt.fmt__clearflags
public import Perennial.Spec.fmt.pp__argNumber
public import Perennial.Spec.fmt.parsenum
public import Perennial.Spec.fmt.pp__printArg
public import Perennial.Spec.unicode.utf8.DecodeRuneInString
public import Perennial.Proof.fmt.DoPrintfLemmas
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

set_option maxHeartbeats 4000000 in
theorem fmt.pp.doPrintf.wp_proof
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_writeByte : fmt.buffer.writeByte.spec (GF := GF) (hG := hG))
    (wp_clearflags : fmt.fmt.clearflags.spec (GF := GF) (hG := hG))
    (wp_argNumber : fmt.pp.argNumber.spec (GF := GF) (hG := hG))
    (wp_parsenum : fmt.parsenum.spec (GF := GF) (hG := hG))
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG))
    (wp_printArg : fmt.pp.printArg.spec (GF := GF) (hG := hG)) :
    fmt.pp.doPrintf.spec (GF := GF) (hG := hG) :=
    fun p bs format ps args_sl xs args dq hformat hfits => by
  wp_start as ⟨Hp, Hargs, Hxs⟩
  unfold isPrinterAny isPrinter
  icases Hp with ⟨%Hpnn, %F0, %wid0, %prec0, %x0, Hp⟩
  iNamedSuffix Hp "0"
  unfold isPrinterA
  icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, Hval, ⟨%reord, Hreord⟩, Hgood, Hpanicking, Herroring, Hwrap, Hwe⟩
  ihave %Hxslen := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hxs
  ihave %Hsllen := ownSlice_len $$ Hargs
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  ihave Hp : isPrinterA p x0 bs F0 wid0 prec0 $$ [Hbuf Hfmt Hib Harg Hval Hreord Hgood Hpanicking Herroring Hwrap Hwe]
  · unfold isPrinterA
    iframe
  ihave HI : (∃ (i argNum : w64) (rest : List Piece) (ar : List Arg) (od : GoString)
      (F : fmtFlags) (wid prec : w64) (x : GoInterface),
      "i" ∷ i_ptr ↦ i ∗ "argNum" ∷ argNum_ptr ↦ argNum ∗ "afterIndex" ∷ afterIndex_ptr ↦ false ∗
      "Hp" ∷ isPrinterA p x (bs ++ od) F wid prec ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ format.length ∧ format.drop (sint.nat i) = encode rest ∧
        Fits rest ar ∧ args.drop (sint.nat argNum) = ar ∧ 0 ≤ sint.Z argNum ∧
        sint.Z argNum ≤ args.length ∧ (∀ o, Out rest ar o → Out ps args (od ++ o))⌝ : IProp GF)
      $$ [i argNum afterIndex Hp]
  · iexists W64 0, W64 0, ps, args, [], F0, wid0, prec0, x0
    simp only [List.append_nil]
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [hformat]; rfl, hfits, rfl, by word, by word, fun o h => h⟩
  irename «end» => Hend
  wp_for HI
  obtain ⟨hi0, hilen, hdrop, hfitsr, hargs, ha0, halen, hout⟩ := Hinv
  cleanup_bool_decide
  wp_if_destruct
  · -- one more piece
    unfold isPrinterA
    icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, Hval, Hreord, ⟨%gd, Hgood⟩, Hpanicking, Herroring, Hwrap, Hwe⟩
    wp_auto
    -- the literal text up to the next `%`
    have hfl := fmt.Fits_leadLits hfitsr
    have hsplit : format.drop (sint.nat i) = (fmt.leadLits rest).1 ++ encode (fmt.leadLits rest).2 := by
      rw [hdrop, fmt.encode_leadLits rest]
    have hhead : ∀ c, (encode (fmt.leadLits rest).2).head? = some c → c = W8 37 := by
      intro c hc
      rcases fmt.leadLits_rest rest with h | ⟨R', h⟩ | ⟨zw, v, R', h⟩ <;> rw [h] at hc
      · simp [encode] at hc
      · simp [fmt.encode_cons, Piece.encode] at hc; exact hc.symm
      · cases zw <;> simp [fmt.encode_cons, Piece.encode] at hc <;> exact hc.symm
    have hin : sint.nat i ≤ format.length := by word
    have hLlen : sint.nat i + (fmt.leadLits rest).1.length ≤ format.length := by
      have := congrArg List.length hsplit
      simp only [List.length_drop, List.length_append] at this
      omega
    ihave HJ : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗
        "%Hj" ∷ ⌜sint.Z i ≤ sint.Z j ∧ sint.nat j ≤ sint.nat i + (fmt.leadLits rest).1.length⌝ :
        IProp GF) $$ [i]
    · iexists i; iframe; ipureintro; exact ⟨Int.le_refl _, by omega⟩
    wp_for HJ
    have hj0 : 0 ≤ sint.Z j := by word
    wp_join (Q := fun v => iprop(⌜v = #(decide (sint.nat j < sint.nat i + (fmt.leadLits rest).1.length))⌝ ∗
        "format" ∷ format_ptr ↦ format ∗ "i" ∷ i_ptr ↦ j)) at (if: _ then _ else _) with [format i]
    · wp_if_destruct
      · list_elem format (sint.nat j) as b
        simp only [hj0, ite_true, Hb_lookup]
        wp_auto
        iframe
        ipureintro
        rw [fmt.scan_byte hsplit hfl.1 hhead (by word) Hj.2 Hb_lookup]
      · iframe
        ipureintro
        rw [decide_eq_false (by word)]
    iintro ⟨%hv, format, i⟩
    subst hv
    cleanup_bool_decide
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      constructor <;> word
    -- the scan stops after the literal bytes `L`
    have hjL : sint.nat j = sint.nat i + (fmt.leadLits rest).1.length := by omega
    clear Hj
    wp_join iprop("Hbuf" ∷ bufferOwn (p.[pp, go!"buf"]) (bs ++ (od ++ (fmt.leadLits rest).1)) ∗
        "format" ∷ format_ptr ↦ format ∗ "i" ∷ i_ptr ↦ j ∗ "lasti" ∷ lasti_ptr ↦ i ∗ "p" ∷ p_ptr ↦ p)
      with [Hbuf format i lasti p] as ⟨Hbuf, format, i, lasti, p⟩
    · have hsl : (format.drop (sint.nat i)).take (sint.nat j - sint.nat i) = (fmt.leadLits rest).1 := by
        rw [hsplit, hjL, Nat.add_sub_cancel_left, List.take_left]
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ format.length from
        ⟨hi0, by word, by word⟩, and_self, ite_true, hsl]
      wp_auto
      wp_apply wp_writeString $$ Hbuf as Hbuf
      rw [List.append_assoc]
      wp_join_done
    · have : (fmt.leadLits rest).1 = [] := by
        apply List.eq_nil_of_length_eq_zero; word
      rw [this, List.append_nil]
      iframe
    wp_if_destruct
    · -- the end of the format: `break`
      have hR : encode (fmt.leadLits rest).2 = [] := by
        have := congrArg List.length hsplit
        simp only [List.length_drop, List.length_append] at this
        apply List.eq_nil_of_length_eq_zero; word
      obtain ⟨rfl, hout0⟩ := fmt.Fits_encode_nil hfl.2 hR
      have hOut : Out ps args (od ++ (fmt.leadLits rest).1) := by
        have := hout _ (fmt.Out_leadLits hout0); simpa using this
      have han : sint.nat argNum = args.length := by
        have := List.drop_eq_nil_iff.mp hargs; word
      have hlt : ¬ sint.Z argNum < sint.Z args_sl.len := by word
      wp_for_post
      icases Hreord with ⟨%reord', Hreord⟩
      cases reord' <;> wp_auto
      · rw [decide_eq_false hlt]
        wp_auto
        iapply HΦ
        iexists _
        rw [← List.append_assoc]
        iframe
        ipureintro; exact ⟨hOut, Hpnn⟩
      · iapply HΦ
        iexists _
        rw [← List.append_assoc]
        iframe
        ipureintro; exact ⟨hOut, Hpnn⟩
    -- a `%`: `%%` or a directive
    have hdropj : format.drop (sint.nat j) = encode (fmt.leadLits rest).2 := by
      rw [hjL, ← List.drop_drop, hsplit, List.drop_left]
    have hjlt : sint.nat j < format.length := by word
    wp_apply wp_clearflags $$ Hfmt as Hfmt
    rcases fmt.leadLits_rest rest with hR | ⟨R', hR⟩ | ⟨zw, v, R', hR⟩
    · exfalso; rw [hR] at hdropj
      have := congrArg List.length hdropj
      simp [encode] at this; omega
    · -- `%%`
      rw [hR] at hdropj hfl
      simp only [fmt.encode_cons, Piece.encode, List.cons_append, List.nil_append] at hdropj
      have hf0 : format[sint.nat j]? = some (W8 37) := by
        rw [← Nat.add_zero (sint.nat j), ← List.getElem?_drop, hdropj]; rfl
      have hf1 : format[sint.nat j + 1]? = some (W8 37) := by
        rw [← List.getElem?_drop, hdropj]; rfl
      have hlen2 : sint.nat j + 2 ≤ format.length := by
        have := congrArg List.length hdropj
        simp only [List.length_drop, List.length_cons] at this; omega
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hj1z : 0 ≤ sint.Z (j + W64 1) := by word
      wp_for
      wp_if_destruct; rotate_left
      · exfalso; word
      simp only [hj1z, ite_true, hj1, hf1]
      wp_auto
      wp_for_post
      wp_apply (wp_argNumber p argNum format (j + W64 1) _ hj1z (by rw [hj1, hf1]; decide))
      have hj1lt : sint.Z (j + W64 1) < sint.Z (W64 (format.length : Int)) := by word
      rw [decide_eq_true hj1lt]
      wp_auto
      simp only [hj1z, ite_true, hj1, hf1]
      wp_auto
      have hel : sint.nat (W64 (format.length : Int)) = format.length := by word
      have hpn : parsenumSpec format (sint.nat (j + W64 1)) (sint.nat (W64 (format.length : Int))) =
          (0, false, sint.nat (j + W64 1)) := by
        rw [hel, hj1]; exact fmt.parsenumSpec_nondigit format _ _ hf1 (by unfold fmt.IsDigit; decide)
      wp_apply (wp_parsenum format (j + W64 1) (W64 (format.length : Int)) hj1z (by word))
      simp only [hpn]
      unfold fmtOwn
      iNamed Hfmt
      icases Hfmt with ⟨Hfbuf, Hflags, Hwid, Hprec⟩
      wp_auto
      rw [show W64 (sint.nat (j + W64 1) : Int) = j + W64 1 by word]
      wp_join with [i format]
      · simp only [hj1z, ite_true, hj1, hf1]
        wp_auto
        wp_join_done
      wp_apply (wp_argNumber p argNum format (j + W64 1) _ hj1z (by rw [hj1, hf1]; decide))
      rw [decide_eq_false (show ¬ sint.Z (W64 (format.length : Int)) ≤ sint.Z (j + W64 1) by word)]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %_
      have hd1 : format.drop (sint.nat j + 1) = W8 37 :: encode R' := by
        rw [← List.drop_drop, hdropj]; rfl
      have hsl : (format.drop (sint.nat (j + W64 1))).take
          (sint.nat (W64 (format.length : Int)) - sint.nat (j + W64 1)) = W8 37 :: encode R' := by
        rw [hj1, hd1]; apply List.take_of_length_le
        have := congrArg List.length hd1
        simp only [List.length_drop] at this
        rw [← this]; word
      simp only [show 0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ sint.Z (W64 (format.length : Int)) ∧
          sint.Z (W64 (format.length : Int)) ≤ format.length from ⟨hj1z, by word, by word⟩,
        and_self, ite_true, hsl]
      wp_auto
      wp_apply wp_DecodeRuneInString as %r %size %Hd
      obtain ⟨rfl, rfl⟩ := Hd.2 _ _ rfl (by decide)
      rw [decide_eq_true (show true = decide (W32 (uint.nat (W8 37) : Int) = W32 37) by decide)]
      wp_auto
      wp_apply wp_writeByte $$ Hbuf as Hbuf
      wp_for_post
      have hfR : Fits R' ar := by cases hfl.2; assumption
      ihave Hbuf : bufferOwn (p.[pp, go!"buf"]) (bs ++ (od ++ (fmt.leadLits rest).1 ++ [W8 37])) $$ [Hbuf]
      · iExactEq Hbuf; simp
      ihave Hfmt : fmtOwn (p.[pp, go!"fmt"]) (p.[pp, go!"buf"]) _ _ _ $$ [Hfbuf Hflags Hwid Hprec]
      · unfold fmtOwn; iframe
      ihave Hp : isPrinterA p x (bs ++ (od ++ (fmt.leadLits rest).1 ++ [W8 37])) _ _ _ $$
          [Hbuf Hfmt Hib Harg Hval Hreord Hgood Hpanicking Herroring Hwrap Hwe]
      · unfold isPrinterA; iframe
      iframe
      iexists (j + W64 1 + W64 1), argNum, R', ar, od ++ (fmt.leadLits rest).1 ++ [W8 37]
      iexists _, _, _, _
      iframe
      isplitl [Hp]
      · iExactEq Hp; rfl
      ipureintro
      refine ⟨by word, by word, ?_, hfR, hargs, ha0, halen, ?_⟩
      · rw [show sint.nat (j + W64 1 + W64 1) = sint.nat j + 1 + 1 by word, ← List.drop_drop, hd1]; rfl
      · intro o ho
        have := hout _ (fmt.Out_leadLits (by rw [hR]; exact Out.percent R' ar o ho))
        simpa [List.append_assoc] using this
    · -- a directive
      rw [hR] at hdropj hfl
      obtain ⟨a, ar', rfl, hdok, hfR⟩ := fmt.Fits_dir_inv hfl.2
      have hvb := fmt.verb_bytes (fmt.DirOk_verb hdok)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hj1z : 0 ≤ sint.Z (j + W64 1) := by word
      -- the argument
      have hargs' : args[sint.nat argNum]? = some a := by
        rw [← Nat.add_zero (sint.nat argNum), ← List.getElem?_drop, hargs]; rfl
      have hanlt : sint.nat argNum < args.length := (List.getElem?_eq_some_iff.mp hargs').1
      list_elem xs (sint.nat argNum) as xa
      cases zw with
      | none =>
        simp only [fmt.encode_cons, Piece.encode, List.cons_append, List.nil_append] at hdropj
        have hf1 : format[sint.nat j + 1]? = some v := by
          rw [← List.getElem?_drop, hdropj]; rfl
        wp_for
        wp_if_destruct; rotate_left
        · exfalso
          have := congrArg List.length hdropj
          simp only [List.length_drop, List.length_cons] at this; word
        simp only [hj1z, ite_true, hj1, hf1]
        wp_auto
        obtain ⟨h35, h48, h43, h45, h32, h119, h37, h46, h42, h91, h97, h122, h128, hnd⟩ := hvb
        have hanz : sint.Z argNum < sint.Z args_sl.len := by word
        rw [decide_eq_false h35]; wp_auto
        rw [decide_eq_false h48]; wp_auto
        rw [decide_eq_false h43]; wp_auto
        rw [decide_eq_false h45]; wp_auto
        rw [decide_eq_false h32]; wp_auto
        rw [decide_eq_true h97]; wp_auto
        rw [decide_eq_true h122]; wp_auto
        rw [decide_eq_true hanz]; wp_auto
        rw [decide_eq_false h119]; wp_auto
        unfold fmtOwn
        icases Hfmt with ⟨Hfbuf, Hflags, Hwid, Hprec⟩
        wp_join iprop("Hflags" ∷ p.[pp, go!"fmt"].[fmt.fmt, go!"fmtFlags"] ↦ noFlags ∗ "p" ∷ p_ptr ↦ p)
          with [Hflags p] as ⟨Hflags, p⟩
        simp only [show 0 ≤ sint.Z argNum ∧ sint.Z argNum < sint.Z args_sl.len from ⟨ha0, hanz⟩]
        wp_apply (wp_load_slice_index args_sl (sint.Z argNum) xs dq xa ha0) $$ [Hargs] as Hargs
        · iframe; ipureintro; exact Hxa_lookup
        rw [show W32 (uint.Z v) = W32 ((uint.nat v : Nat) : Int) by word]
        icases (BigSepL2.bigSepL2_lookup_acc Hxa_lookup hargs') $$ Hxs with ⟨Hxa, Hxs⟩
        ihave Hpr : isPrinter p (bs ++ (od ++ (fmt.leadLits rest).1)) (dirFlags none) (dirWid none) (W64 0) $$
            [Hbuf Hfbuf Hflags Hwid Hprec Hib Harg Hval Hreord Hgood Hpanicking Herroring Hwrap Hwe]
        · unfold isPrinter isPrinterA fmtOwn
          iexists x
          simp only [dirFlags, dirWid, Option.getD]
          iframe
        wp_apply (wp_printArg p xa a (bs ++ (od ++ (fmt.leadLits rest).1)) none v hdok) $$ [Hpr Hxa]
          as ⟨%o, %ho, Hp, Hxa⟩
        · iframe
        ihave Hxs : ([∗list] x;a ∈ xs;args, isArg (GF := GF) x a) $$ [Hxs Hxa]
        · iapply Hxs; iexact Hxa
        wp_for_post
        wp_for_post
        ihave Hp : isPrinterA p xa (bs ++ (od ++ (fmt.leadLits rest).1 ++ o)) (dirFlags none) (dirWid none)
            (W64 0) $$ [Hp]
        · iExactEq Hp; simp
        iframe
        iexists (j + W64 1 + W64 1), (argNum + W64 1), R', ar', od ++ (fmt.leadLits rest).1 ++ o
        iexists _, _, _, _
        iframe
        isplitl [Hp]
        · iExactEq Hp; rfl
        ipureintro
        refine ⟨by word, by word, ?_, hfR, ?_, by word, by word, ?_⟩
        · rw [show sint.nat (j + W64 1 + W64 1) = sint.nat j + 2 by word, ← List.drop_drop,
            hdropj]; rfl
        · rw [show sint.nat (argNum + W64 1) = sint.nat argNum + 1 by word, ← List.drop_drop, hargs]; rfl
        · intro out hout'
          have := hout _ (fmt.Out_leadLits (by rw [hR]; exact Out.dir none v a o R' ar' out ho hout'))
          simpa [List.append_assoc] using this
      | some N =>
        have hN := fmt.DirOk_some_width hdok
        obtain ⟨h35, h48, h43, h45, h32, h119, h37, h46, h42, h91, h97, h122, h128, hnd⟩ := hvb
        obtain ⟨d0, ds, hdec, hd0, hd00⟩ := fmt.decimalNat_head hN.1
        simp only [fmt.encode_cons, Piece.encode, List.cons_append, List.nil_append,
          List.append_assoc] at hdropj
        have hf1 : format[sint.nat j + 1]? = some (W8 48) := by
          rw [← List.getElem?_drop, hdropj]; rfl
        have hf2 : format[sint.nat j + 2]? = some d0 := by
          rw [← List.getElem?_drop, hdropj, hdec]; rfl
        obtain ⟨d35, d43, d45, d32, d97, d91, d42⟩ := fmt.digit_bytes hd0
        have hlen3 : sint.nat j + 3 ≤ format.length := by
          have := congrArg List.length hdropj
          simp only [List.length_drop, List.length_cons, List.length_append, hdec] at this; omega
        unfold fmtOwn
        icases Hfmt with ⟨Hfbuf, Hflags, Hwid, Hprec⟩
        ihave HK : (∃ (k : w64) (F : fmtFlags), "i" ∷ i_ptr ↦ (j + W64 1 + k) ∗
            "Hflags" ∷ p.[pp, go!"fmt"].[fmt.fmt, go!"fmtFlags"] ↦ F ∗
            "%Hk" ∷ ⌜(k = W64 0 ∧ F = noFlags) ∨ (k = W64 1 ∧ F = { noFlags with zero' := true })⌝ :
            IProp GF) $$ [i Hflags]
        · iexists W64 0, noFlags
          rw [show j + W64 1 + W64 0 = j + W64 1 by word]
          iframe
          ipureintro; exact Or.inl ⟨rfl, rfl⟩
        wp_for HK
        rcases Hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- the `0` flag
          wp_if_destruct; rotate_left
          · exfalso; word
          rw [show sint.nat (j + W64 1 + W64 0) = sint.nat j + 1 by word]
          simp only [show 0 ≤ sint.Z (j + W64 1 + W64 0) by word, ite_true, hf1]
          wp_auto
          wp_for_post
          iframe
          iexists W64 1, _
          rw [show j + W64 1 + W64 0 + W64 1 = j + W64 1 + W64 1 by word]
          iframe
          ipureintro; exact Or.inr ⟨rfl, rfl⟩
        · -- the first digit of the width
          wp_if_destruct; rotate_left
          · exfalso; word
          rw [show sint.nat (j + W64 1 + W64 1) = sint.nat j + 2 by word]
          simp only [show 0 ≤ sint.Z (j + W64 1 + W64 1) by word, ite_true, hf2]
          wp_auto
          rw [decide_eq_false d35]; wp_auto
          rw [decide_eq_false hd00]; wp_auto
          rw [decide_eq_false d43]; wp_auto
          rw [decide_eq_false d45]; wp_auto
          rw [decide_eq_false d32]; wp_auto
          rw [decide_eq_false d97]; wp_auto
          wp_for_post
          have hJ2 : sint.nat (j + W64 1 + W64 1) = sint.nat j + 2 := by word
          have hJ2z : 0 ≤ sint.Z (j + W64 1 + W64 1) := by word
          wp_apply (wp_argNumber p argNum format (j + W64 1 + W64 1) _ hJ2z
            (by rw [hJ2, hf2]; simpa using d91))
          rw [decide_eq_true (show sint.Z (j + W64 1 + W64 1) < sint.Z (W64 (format.length : Int)) by word)]
          wp_auto
          simp only [hJ2z, ite_true, hJ2, hf2]
          wp_auto
          rw [decide_eq_false d42]
          wp_auto
          -- the width
          have hdj2 : format.drop (sint.nat j + 2) = decimalNat N ++ v :: encode R' := by
            rw [← List.drop_drop, hdropj]; rfl
          have hel : sint.nat (W64 (format.length : Int)) = format.length := by word
          have hpn : parsenumSpec format (sint.nat (j + W64 1 + W64 1)) (sint.nat (W64 (format.length : Int))) =
              (N, true, sint.nat j + 2 + (decimalNat N).length) := by
            rw [hel, hJ2]
            exact fmt.parsenumSpec_decimalNat format _ _ N hdj2
              (fun c hc => by cases hc; exact hnd) hN.2
          wp_apply (wp_parsenum format (j + W64 1 + W64 1) (W64 (format.length : Int)) hJ2z (by word))
          simp only [hpn]
          -- the verb, after the digits
          have hdK : format.drop (sint.nat j + 2 + (decimalNat N).length) = v :: encode R' := by
            rw [← List.drop_drop, hdj2, List.drop_left]
          have hKlt : sint.nat j + 2 + (decimalNat N).length < format.length := by
            have := congrArg List.length hdK
            simp only [List.length_drop, List.length_cons] at this; omega
          have hfK : format[sint.nat j + 2 + (decimalNat N).length]? = some v := by
            rw [← Nat.add_zero (sint.nat j + 2 + _), ← List.getElem?_drop, hdK]; rfl
          have hK : sint.nat (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)) =
              sint.nat j + 2 + (decimalNat N).length := by word
          have hKz : 0 ≤ sint.Z (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)) := by word
          wp_join (Q := fun r => iprop(⌜r = #false⌝ ∗ "format" ∷ format_ptr ↦ format ∗
              "i" ∷ i_ptr ↦ W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)))
            at (if: _ then _ else #false) with [i format]
          · wp_if_destruct
            · simp only [hKz, ite_true, hK, hfK]
              wp_auto
              rw [decide_eq_false h46]
              iframe; ipureintro; rfl
            · iframe
          iintro ⟨%hr, format, i⟩
          subst hr
          wp_auto
          wp_apply (wp_argNumber p argNum format _ _ hKz (by rw [hK, hfK]; simpa using h91))
          rw [decide_eq_false (show ¬ sint.Z (W64 (format.length : Int)) ≤
            sint.Z (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)) by word)]
          wp_auto
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %_
          have hslK : (format.drop (sint.nat (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)))).take
              (sint.nat (W64 (format.length : Int)) -
                sint.nat (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int))) = v :: encode R' := by
            rw [hK, hdK]; apply List.take_of_length_le
            have := congrArg List.length hdK
            simp only [List.length_drop] at this
            rw [← this]; word
          simp only [show 0 ≤ sint.Z (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)) ∧
              sint.Z (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int)) ≤
                sint.Z (W64 (format.length : Int)) ∧
              sint.Z (W64 (format.length : Int)) ≤ format.length from ⟨hKz, by word, by word⟩,
            and_self, ite_true, hslK]
          wp_auto
          wp_apply wp_DecodeRuneInString as %r %size %Hd
          obtain ⟨rfl, rfl⟩ := Hd.2 _ _ rfl h128
          obtain ⟨hw37, hw119, hw118⟩ := fmt.verb_runes (fmt.DirOk_verb hdok)
          have hanz : sint.Z argNum < sint.Z args_sl.len := by word
          rw [decide_eq_false (show ¬ (true = decide (W32 (uint.nat v : Int) = W32 37)) from
            fun h => hw37 (of_decide_eq_true h.symm))]
          wp_auto
          rw [decide_eq_false (show ¬ (true = decide (sint.Z args_sl.len ≤ sint.Z argNum)) by
            simp; word)]
          wp_auto
          rw [decide_eq_false (show ¬ (true = decide (W32 (uint.nat v : Int) = W32 119)) from
            fun h => hw119 (of_decide_eq_true h.symm))]
          wp_auto
          by_cases hv : v = W8 118
          · rw [decide_eq_true (show true = decide (W32 (uint.nat v : Int) = W32 118) by
              simp only [hw118.mpr hv, decide_true])]
            wp_auto
            simp only [show 0 ≤ sint.Z argNum ∧ sint.Z argNum < sint.Z args_sl.len from ⟨ha0, hanz⟩]
            wp_apply (wp_load_slice_index args_sl (sint.Z argNum) xs dq xa ha0) $$ [Hargs] as Hargs
            · iframe; ipureintro; exact Hxa_lookup
            icases (BigSepL2.bigSepL2_lookup_acc Hxa_lookup hargs') $$ Hxs with ⟨Hxa, Hxs⟩
            ihave Hpr : isPrinter p (bs ++ (od ++ (fmt.leadLits rest).1)) (dirFlags (some N)) (dirWid (some N))
                (W64 0) $$ [Hbuf Hfbuf Hflags Hwid Hprec Hib Harg Hval Hreord Hgood Hpanicking Herroring Hwrap Hwe]
            · unfold isPrinter isPrinterA fmtOwn
              iexists x
              simp only [dirFlags, dirWid, Option.getD]
              iframe
            wp_apply (wp_printArg p xa a (bs ++ (od ++ (fmt.leadLits rest).1)) (some N) v hdok) $$ [Hpr Hxa]
              as ⟨%o, %ho, Hp, Hxa⟩
            · iframe
            ihave Hxs : ([∗list] x;a ∈ xs;args, isArg (GF := GF) x a) $$ [Hxs Hxa]
            · iapply Hxs; iexact Hxa
            wp_for_post
            ihave Hp : isPrinterA p xa (bs ++ (od ++ (fmt.leadLits rest).1 ++ o)) (dirFlags (some N))
                (dirWid (some N)) (W64 0) $$ [Hp]
            · iExactEq Hp; simp
            iframe
            iexists (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int) + W64 1), (argNum + W64 1), R', ar', od ++ (fmt.leadLits rest).1 ++ o
            iexists _, _, _, _
            iframe
            isplitl [Hp]
            · iExactEq Hp; rfl
            ipureintro
            refine ⟨by word, by word, ?_, hfR, ?_, by word, by word, ?_⟩
            · rw [show sint.nat (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int) + W64 1) = sint.nat j + 2 + (decimalNat N).length + 1 by word,
                ← List.drop_drop, hdK]; rfl
            · rw [show sint.nat (argNum + W64 1) = sint.nat argNum + 1 by word, ← List.drop_drop, hargs]; rfl
            · intro out hout'
              have := hout _ (fmt.Out_leadLits (by rw [hR]; exact Out.dir (some N) v a o R' ar' out ho hout'))
              simpa [List.append_assoc] using this
          · rw [decide_eq_false (show ¬ (true = decide (W32 (uint.nat v : Int) = W32 118)) from
              fun h => hv (hw118.mp (of_decide_eq_true h.symm)))]
            wp_auto
            simp only [show 0 ≤ sint.Z argNum ∧ sint.Z argNum < sint.Z args_sl.len from ⟨ha0, hanz⟩]
            wp_apply (wp_load_slice_index args_sl (sint.Z argNum) xs dq xa ha0) $$ [Hargs] as Hargs
            · iframe; ipureintro; exact Hxa_lookup
            icases (BigSepL2.bigSepL2_lookup_acc Hxa_lookup hargs') $$ Hxs with ⟨Hxa, Hxs⟩
            ihave Hpr : isPrinter p (bs ++ (od ++ (fmt.leadLits rest).1)) (dirFlags (some N)) (dirWid (some N))
                (W64 0) $$ [Hbuf Hfbuf Hflags Hwid Hprec Hib Harg Hval Hreord Hgood Hpanicking Herroring Hwrap Hwe]
            · unfold isPrinter isPrinterA fmtOwn
              iexists x
              simp only [dirFlags, dirWid, Option.getD]
              iframe
            wp_apply (wp_printArg p xa a (bs ++ (od ++ (fmt.leadLits rest).1)) (some N) v hdok) $$ [Hpr Hxa]
              as ⟨%o, %ho, Hp, Hxa⟩
            · iframe
            ihave Hxs : ([∗list] x;a ∈ xs;args, isArg (GF := GF) x a) $$ [Hxs Hxa]
            · iapply Hxs; iexact Hxa
            wp_for_post
            ihave Hp : isPrinterA p xa (bs ++ (od ++ (fmt.leadLits rest).1 ++ o)) (dirFlags (some N))
                (dirWid (some N)) (W64 0) $$ [Hp]
            · iExactEq Hp; simp
            iframe
            iexists (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int) + W64 1), (argNum + W64 1), R', ar', od ++ (fmt.leadLits rest).1 ++ o
            iexists _, _, _, _
            iframe
            isplitl [Hp]
            · iExactEq Hp; rfl
            ipureintro
            refine ⟨by word, by word, ?_, hfR, ?_, by word, by word, ?_⟩
            · rw [show sint.nat (W64 ((sint.nat j + 2 + (decimalNat N).length : Nat) : Int) + W64 1) = sint.nat j + 2 + (decimalNat N).length + 1 by word,
                ← List.drop_drop, hdK]; rfl
            · rw [show sint.nat (argNum + W64 1) = sint.nat argNum + 1 by word, ← List.drop_drop, hargs]; rfl
            · intro out hout'
              have := hout _ (fmt.Out_leadLits (by rw [hR]; exact Out.dir (some N) v a o R' ar' out ho hout'))
              simpa [List.append_assoc] using this
  · -- the end of the format
    have hie : sint.nat i = format.length := by word
    rw [hie, List.drop_length] at hdrop
    obtain ⟨rfl, hout0⟩ := fmt.Fits_encode_nil hfitsr hdrop.symm
    have han : sint.nat argNum = args.length := by
      have := List.drop_eq_nil_iff.mp hargs; word
    unfold isPrinterA
    iNamed Hp
    icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, Hval, ⟨%reord', Hreord⟩, Hgood, Hpanicking, Herroring, Hwrap, Hwe⟩
    have hlt : ¬ sint.Z argNum < sint.Z args_sl.len := by word
    have hOut : Out ps args od := by simpa using hout [] hout0
    cases reord' <;> wp_auto
    · rw [decide_eq_false hlt]
      wp_auto
      iapply HΦ
      iexists od
      iframe
      ipureintro; exact ⟨hOut, Hpnn⟩
    · iapply HΦ
      iexists od
      iframe
      ipureintro; exact ⟨hOut, Hpnn⟩

end proof

end Perennial
