/-
The pure model of `FormatUint`, `FormatInt` and `ParseInt` (`internal/strconv/itoa.go`,
`atoi.go`): a number's digits in a base (`baseDigits`), the characters of the digits
(`digitChar`), `fmtUint`/`fmtInt` (what `FormatUint`/`FormatInt` return), the tables `digits` and
`smalls` the code reads them from, and `parseInt` (what `ParseInt` returns in a base between 2 and
36), with the round trip `parseInt (fmtInt m 10) 10 64 = .ok m`.
-/
module

public import Perennial.Proof.internal.strconv.ParseUintBasics

@[expose] public section

noncomputable section

namespace Perennial

namespace internal.strconv

/-! ### Digits -/

/-- Induction on a list from its end. -/
theorem list_snoc_induction {α : Type} {P : List α → Prop} (nil : P [])
    (append_singleton : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a r ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

/-- The digits of `n` in base `b ≥ 2`, most significant first (`[0]` for `0`). -/
def baseDigits (b : Nat) (hb : 2 ≤ b) (n : Nat) : List Nat :=
  if n < b then [n] else baseDigits b hb (n / b) ++ [n % b]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The number a list of digits (most significant first) denotes in base `b`. -/
def digitsVal (b : Nat) (ds : List Nat) : Nat := ds.foldl (fun a d => b * a + d) 0

theorem digitsVal_append (b : Nat) (ds : List Nat) (d : Nat) :
    digitsVal b (ds ++ [d]) = b * digitsVal b ds + d := by
  simp [digitsVal, List.foldl_append]

theorem foldl_digits (b : Nat) (ds : List Nat) (a : Nat) :
    ds.foldl (fun a d => b * a + d) a = a * b ^ ds.length + ds.foldl (fun a d => b * a + d) 0 := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (b * a + d), ih (b * 0 + d), Nat.pow_succ]
    simp only [Nat.mul_zero, Nat.zero_add]
    have : (b * a + d) * b ^ ds.length = a * (b ^ ds.length * b) + d * b ^ ds.length := by
      rw [Nat.add_mul]; congr 1; rw [Nat.mul_comm b a, Nat.mul_assoc, Nat.mul_comm b]
    omega

theorem digitsVal_cons (b d : Nat) (ds : List Nat) :
    digitsVal b (d :: ds) = d * b ^ ds.length + digitsVal b ds := by
  unfold digitsVal
  rw [List.foldl_cons, foldl_digits]
  simp

theorem digitsVal_baseDigits (b : Nat) (hb : 2 ≤ b) (n : Nat) :
    digitsVal b (baseDigits b hb n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · simp [digitsVal]
    · rw [digitsVal_append, ih (n / b) (Nat.div_lt_self (by omega) (by omega))]
      exact Nat.div_add_mod n b

theorem baseDigits_lt (b : Nat) (hb : 2 ≤ b) (n : Nat) : ∀ d ∈ baseDigits b hb n, d < b := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · intro d hd; simp at hd; omega
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (n / b) (Nat.div_lt_self (by omega) (by omega)) d hd
      · subst hd; exact Nat.mod_lt n (by omega)

theorem baseDigits_ne_nil (b : Nat) (hb : 2 ≤ b) (n : Nat) : baseDigits b hb n ≠ [] := by
  rw [baseDigits]; split <;> simp

/-- A number of digits whose first digit is not `0` is not `0`. -/
theorem digitsVal_pos (b : Nat) (hb : 2 ≤ b) (d : Nat) (ds : List Nat) (hd : d ≠ 0) :
    1 ≤ digitsVal b (d :: ds) := by
  rw [digitsVal_cons]
  have : 1 ≤ b ^ ds.length := Nat.one_le_pow _ _ (by omega)
  have : 1 ≤ d * b ^ ds.length := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd (by omega))
  omega

/-- **The digits of a number are unique**: digits below the base, not empty, without a leading
`0` (unless the only digit), are the number's `baseDigits`. -/
theorem baseDigits_digitsVal (b : Nat) (hb : 2 ≤ b) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < b) → ds ≠ [] → (ds.length = 1 ∨ ds.head? ≠ some 0) →
      baseDigits b hb (digitsVal b ds) = ds := by
  intro ds
  induction ds using list_snoc_induction with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton ds d ih =>
    intro hlt _ hhead
    have hd : d < b := hlt d (by simp)
    rw [digitsVal_append]
    rcases ds with _ | ⟨e, es⟩
    · simp only [List.nil_append, digitsVal, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
      rw [baseDigits, if_pos hd]
    · have he : e ≠ 0 := by
        rcases hhead with h | h
        · simp at h
        · intro h0; apply h; simp [h0]
      have hv := digitsVal_pos b hb e es he
      have hge : ¬ (b * digitsVal b (e :: es) + d < b) := by
        have : b ≤ b * digitsVal b (e :: es) := Nat.le_mul_of_pos_right b hv
        omega
      rw [baseDigits, if_neg hge]
      have h1 : (b * digitsVal b (e :: es) + d) / b = digitsVal b (e :: es) := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd]
        omega
      have h2 : (b * digitsVal b (e :: es) + d) % b = d := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
      rw [h1, h2, ih (fun x hx => hlt x (List.mem_append_left _ hx)) (by simp) (Or.inr (by simp [he]))]

/-! ### Characters -/

/-- A digit's character (`0-9`, then `a-z`). -/
def digitChar (d : Nat) : w8 := if d < 10 then W8 (48 + d) else W8 (87 + d)

theorem digitChar_inj {d e : Nat} (hd : d < 36) (he : e < 36) (h : digitChar d = digitChar e) :
    d = e := by
  unfold digitChar at h
  split at h <;> split at h <;>
    · have := congrArg BitVec.toNat h
      simp [W8] at this
      omega

theorem map_digitChar_inj (b : Nat) (hb : b ≤ 36) (ds es : List Nat) (hd : ∀ d ∈ ds, d < b)
    (he : ∀ e ∈ es, e < b) (h : ds.map digitChar = es.map digitChar) : ds = es := by
  induction ds generalizing es with
  | nil => cases es with
    | nil => rfl
    | cons _ _ => simp at h
  | cons d ds ih => cases es with
    | nil => simp at h
    | cons e es =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hd0 := hd d (by simp)
      have he0 := he e (by simp)
      rw [digitChar_inj (by omega) (by omega) h.1,
        ih es (fun x hx => hd x (by simp [hx])) (fun x hx => he x (by simp [hx])) h.2]

/-- The string `digits` (`"0123456789abcdefghijklmnopqrstuvwxyz"`) holds `digitChar d` at `d`. -/
theorem digits_getElem : ∀ d : Fin 36,
    (go!"0123456789abcdefghijklmnopqrstuvwxyz" : GoString)[d.val]? = some (digitChar d.val) := by
  decide +kernel

/-- The string `smalls` (`"00010203...99"`) holds the two digits of `k < 100` at `2k`, `2k+1`. -/
theorem smalls_getElem : ∀ k : Fin 100,
    (go!"00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899" : GoString)[2 * k.val]? =
      some (digitChar (k.val / 10)) ∧
    (go!"00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899" : GoString)[2 * k.val + 1]? =
      some (digitChar (k.val % 10)) := by
  decide +kernel

/-- `digits[d:d+1]`, for `d < 36`. -/
theorem digits_slice : ∀ d : Fin 36,
    ((go!"0123456789abcdefghijklmnopqrstuvwxyz" : GoString).drop d.val).take 1 = [digitChar d.val] := by
  decide +kernel

/-- `smalls[2k:2k+2]`, for `k < 100`. -/
theorem smalls_slice : ∀ k : Fin 100,
    ((go!"00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899" : GoString).drop (2 * k.val)).take 2 =
      [digitChar (k.val / 10), digitChar (k.val % 10)] := by
  decide +kernel

/-! ### `FormatUint`, `FormatInt` -/

/-- **`FormatUint(n, b)`** of a base `2 ≤ b ≤ 36`: the digits of `n` in base `b`, most
significant first, without leading zeros (`"0"` for `0`), the digits `0-9` then `a-z`. -/
def fmtUint (n : w64) (b : w64) : GoString :=
  if h : 2 ≤ b.toNat then (baseDigits b.toNat h n.toNat).map digitChar else []

/-- **`FormatInt(n, b)`** of a base `2 ≤ b ≤ 36`: `-` (byte 45) and the digits of `-n` (two's
complement, so `2^63` for the least `int64`) when `n` is negative, else the digits of `n`. -/
def fmtInt (n : w64) (b : w64) : GoString :=
  if sint.Z n < 0 then W8 45 :: fmtUint (-n) b else fmtUint n b

/-- `fmtUint` as the digits a list of digits denotes: the characters of digits below the base,
not empty, without a leading `0` unless the only digit. -/
theorem fmtUint_eq_of (n b : w64) (hb : 2 ≤ b.toNat) (ds : List Nat) (hlt : ∀ d ∈ ds, d < b.toNat)
    (hne : ds ≠ []) (hhead : ds.length = 1 ∨ ds.head? ≠ some 0) (hv : digitsVal b.toNat ds = n.toNat) :
    fmtUint n b = ds.map digitChar := by
  unfold fmtUint
  rw [dif_pos hb, ← hv, baseDigits_digitsVal _ hb ds hlt hne hhead]

/-- A number below `2 ^ k` has at most `k + 1` digits in a base `b ≥ 2`. -/
theorem baseDigits_length_le (b : Nat) (hb : 2 ≤ b) :
    ∀ (k n : Nat), n < 2 ^ k → (baseDigits b hb n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    rw [baseDigits]
    have : n < b := by simp at hn; omega
    simp [this]
  | succ k ih =>
    intro n hn
    rw [baseDigits]
    split
    · simp
    · have hq : n / b < 2 ^ k := by
        have h2 : n / b ≤ n / 2 := Nat.div_le_div_left hb (by decide)
        rw [Nat.pow_succ] at hn
        omega
      simp only [List.length_append, List.length_singleton]
      have := ih (n / b) hq
      omega

/-- The digits' value is below the base to the number of digits. -/
theorem digitsVal_lt (b : Nat) (ds : List Nat) (hlt : ∀ d ∈ ds, d < b) :
    digitsVal b ds < b ^ ds.length := by
  induction ds using list_snoc_induction with
  | nil => simp [digitsVal]
  | append_singleton ds d ih =>
    rw [digitsVal_append, List.length_append, List.length_singleton, Nat.pow_succ]
    have h1 := ih (fun x hx => hlt x (by simp [hx]))
    have h2 : d < b := hlt d (by simp)
    have : b * digitsVal b ds + d < b * (digitsVal b ds + 1) := by rw [Nat.mul_add]; omega
    have : b * (digitsVal b ds + 1) ≤ b * b ^ ds.length := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_comm (b ^ ds.length)]
    omega

/-- The decimal form of a one-digit number. -/
theorem fmtUint10_lt10 (n : w64) (h : n.toNat < 10) : fmtUint n (W64 10) = [digitChar n.toNat] :=
  fmtUint_eq_of n (W64 10) (by decide) [n.toNat] (by simp; exact h) (by simp) (Or.inl rfl)
    (by simp [digitsVal])

/-- The decimal form of a two-digit number. -/
theorem fmtUint10_lt100 (n : w64) (h1 : 10 ≤ n.toNat) (h2 : n.toNat < 100) :
    fmtUint n (W64 10) = [digitChar (n.toNat / 10), digitChar (n.toNat % 10)] := by
  have := fmtUint_eq_of n (W64 10) (by decide) [n.toNat / 10, n.toNat % 10]
    (by intro d hd; simp at hd; have : (W64 10).toNat = 10 := rfl; omega) (by simp)
    (Or.inr (by simp; omega)) (by simp [digitsVal]; have : (W64 10).toNat = 10 := rfl; omega)
  simpa using this

/-- A number below `b ^ (k + 1)` has at most `k + 1` digits in base `b`. -/
theorem baseDigits_length_le_pow (b : Nat) (hb : 2 ≤ b) :
    ∀ (k n : Nat), n < b ^ (k + 1) → (baseDigits b hb n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    rw [baseDigits]
    have : n < b := by simpa using hn
    simp [this]
  | succ k ih =>
    intro n hn
    rw [baseDigits]
    split
    · simp
    · have hq : n / b < b ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact hn
      simp only [List.length_append, List.length_singleton]
      have := ih (n / b) hq
      omega

/-- A 64-bit number has at most 20 decimal digits. -/
theorem fmtUint10_length_le (n : w64) : (fmtUint n (W64 10)).length ≤ 20 := by
  unfold fmtUint
  rw [dif_pos (by decide)]
  simp only [List.length_map]
  exact baseDigits_length_le_pow _ _ 19 n.toNat (by have := n.isLt; simp at this ⊢; omega)

/-! ### `ParseInt` -/

/-- A digit's character reads back as the digit (`digitVal`, `ParseUint`'s reading). -/
theorem digitVal_digitChar : ∀ d : Fin 36, digitVal (digitChar d.val) = some d.val := by
  decide +kernel

/-- `ParseUint`'s loop over the characters of digits below the base: their value, if it and so
every prefix's value fits. -/
theorem parseDigits_map_digitChar (base maxVal : Nat) (hb : base ≤ 36) :
    ∀ (ds : List Nat) (n : Nat), (∀ d ∈ ds, d < base) →
      ds.foldl (fun a d => base * a + d) n ≤ maxVal →
      parseDigits base maxVal (ds.map digitChar) n = .ok (ds.foldl (fun a d => base * a + d) n) := by
  intro ds
  induction ds with
  | nil => intro n _ _; rfl
  | cons d ds ih =>
    intro n hlt hle
    have hd : d < base := hlt d (by simp)
    simp only [List.foldl_cons] at hle ⊢
    have hmono : base * n + d ≤ ds.foldl (fun a d => base * a + d) (base * n + d) := by
      rw [foldl_digits]
      have : 1 ≤ base ^ ds.length := Nat.one_le_pow _ _ (by omega)
      have : base * n + d ≤ (base * n + d) * base ^ ds.length := Nat.le_mul_of_pos_right _ this
      omega
    have h3 : n * base + d ≤ maxVal := by rw [Nat.mul_comm]; omega
    rw [List.map_cons, parseDigits_cons_ok (digitVal_digitChar ⟨d, by omega⟩ : digitVal (digitChar d) = some d) hd
      h3, Nat.mul_comm n base]
    exact ih _ (fun x hx => hlt x (by simp [hx])) hle

/-- `ParseUint`'s loop returns at most its maximum, from a start at most it. -/
theorem parseDigits_ok_le (base maxVal : Nat) :
    ∀ (cs : GoString) (n m : Nat), n ≤ maxVal → parseDigits base maxVal cs n = .ok m → m ≤ maxVal := by
  intro cs
  induction cs with
  | nil => intro n m hn h; simp only [parseDigits, ParseRes.ok.injEq] at h; omega
  | cons c cs ih =>
    intro n m hn h
    simp only [parseDigits] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ih _ m (by omega) h

/-- What `ParseUint` returns fits its bit size. -/
theorem parseUint_ok_le (s : GoString) (base bitSize m : Nat)
    (h : parseUint s base bitSize = .ok m) : m ≤ 2 ^ effBitSize bitSize - 1 := by
  unfold parseUint at h
  split at h
  · cases h
  · exact parseDigits_ok_le _ _ s 0 m (Nat.zero_le _) h

/-- What `ParseInt` returns in a base between 2 and 36: a number, a syntax error, or a range error
with the value it returns. -/
inductive ParseIntRes where
  | ok (n : Int)
  | errSyntax
  | errRange (n : Int)
deriving DecidableEq

/-- `ParseInt`'s result after the sign (`neg`) is taken off `s`, leaving `t`: `ParseUint`'s result
`un` (its maximum `2^bitSize - 1` on a range error, which `ParseInt` reads as the value), a range
error with `2^(bitSize-1) - 1` or `-2^(bitSize-1)` if `un` exceeds the signed range, else `±un`.
(This follows the code: at a bit size of 1, `-1` after a range error of a negative number.) -/
def parseIntOf (neg : Bool) (t : GoString) (base bitSize : Nat) : ParseIntRes :=
  let cutoff : Nat := 2 ^ (effBitSize bitSize - 1)
  match parseUint t base bitSize with
  | .errSyntax => .errSyntax
  | r =>
    let un : Nat := match r with
      | .ok n => n
      | _ => 2 ^ effBitSize bitSize - 1
    if !neg ∧ cutoff ≤ un then .errRange (cutoff - 1)
    else if neg ∧ cutoff < un then .errRange (-(cutoff : Int))
    else .ok (if neg then -(un : Int) else un)

/-- `ParseInt(s, base, bitSize)` for a base between 2 and 36 and a bit size between 0 and 64: a
syntax error for the empty string; else `parseIntOf` after a leading `-` or `+`, if any. -/
def parseInt (s : GoString) (base bitSize : Nat) : ParseIntRes :=
  match s with
  | [] => .errSyntax
  | c :: cs =>
    if c = W8 45 then parseIntOf true cs base bitSize
    else if c = W8 43 then parseIntOf false cs base bitSize
    else parseIntOf false (c :: cs) base bitSize

/-- `ParseUint` of a decimal form reads its value back. -/
theorem parseUint_fmtUint10 (n : w64) :
    parseUint (fmtUint n (W64 10)) 10 64 = .ok n.toNat := by
  have hb : 2 ≤ (W64 10).toNat := by decide
  unfold fmtUint
  rw [dif_pos hb]
  have h10 : (W64 10).toNat = 10 := rfl
  simp only [h10]
  have hne : (baseDigits 10 (by omega) n.toNat).map digitChar ≠ [] := by
    simp [baseDigits_ne_nil]
  rw [parseUint, if_neg hne]
  have hv := digitsVal_baseDigits 10 (by omega) n.toNat
  unfold digitsVal at hv
  have := parseDigits_map_digitChar 10 (2 ^ effBitSize 64 - 1) (by omega)
    (baseDigits 10 (by omega) n.toNat) 0 (baseDigits_lt 10 (by omega) n.toNat)
    (by rw [hv]; have := n.isLt; simp [effBitSize]; omega)
  rw [this, hv]

/-- A decimal form starts with a digit, not a sign. -/
theorem fmtUint10_head (n : w64) : ∃ c cs, fmtUint n (W64 10) = c :: cs ∧ c ≠ W8 43 ∧ c ≠ W8 45 := by
  have hb : 2 ≤ (W64 10).toNat := by decide
  unfold fmtUint
  rw [dif_pos hb]
  have hlt := baseDigits_lt (W64 10).toNat hb n.toNat
  rcases h : baseDigits (W64 10).toNat hb n.toNat with _ | ⟨d, ds⟩
  · exact absurd h (baseDigits_ne_nil _ _ _)
  · have hd : d < 10 := hlt d (by rw [h]; simp)
    refine ⟨digitChar d, ds.map digitChar, rfl, ?_, ?_⟩ <;>
    · unfold digitChar
      rw [if_pos hd]
      intro he
      have := congrArg BitVec.toNat he
      simp [W8] at this
      omega

/-- **`ParseInt` reads back what `FormatInt` writes**, in base 10 at bit size 64. -/
theorem parseInt_fmtInt10 (m : w64) : parseInt (fmtInt m (W64 10)) 10 64 = .ok (sint.Z m) := by
  unfold fmtInt
  split
  · rename_i hneg
    have hu : ((-m).toNat : Int) = - sint.Z m := by word
    have hle : (-m).toNat ≤ 2 ^ 63 := by word
    have h1 : parseInt (W8 45 :: fmtUint (-m) (W64 10)) 10 64 =
        parseIntOf true (fmtUint (-m) (W64 10)) 10 64 := rfl
    rw [h1]
    unfold parseIntOf
    rw [parseUint_fmtUint10]
    simp only [effBitSize, if_neg (show ¬ (64 : Nat) = 0 by decide)]
    rw [if_neg (by simp), if_neg (by rintro ⟨-, h⟩; have : (2 : Nat) ^ (64 - 1) = 2 ^ 63 := rfl; omega),
      if_pos trivial, hu, Int.neg_neg]
  · rename_i hpos
    obtain ⟨c, cs, hc, h43, h45⟩ := fmtUint10_head m
    have hz : sint.Z m = (m.toNat : Int) := by word
    have hlt : m.toNat < 2 ^ 63 := by
      have : 0 ≤ sint.Z m := by omega
      word
    have h1 : parseInt (fmtUint m (W64 10)) 10 64 = parseIntOf false (fmtUint m (W64 10)) 10 64 := by
      rw [hc]; simp only [parseInt, if_neg h45, if_neg h43]
    rw [h1]
    unfold parseIntOf
    rw [parseUint_fmtUint10]
    simp only [effBitSize, if_neg (show ¬ (64 : Nat) = 0 by decide)]
    rw [if_neg (by rintro ⟨-, h⟩; have : (2 : Nat) ^ (64 - 1) = 2 ^ 63 := rfl; omega),
      if_neg (by simp), if_neg (by simp), hz]

end internal.strconv

end Perennial
