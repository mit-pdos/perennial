/-
**SHA-1 (FIPS 180-4), as pure definitions**, and the facts about them that the proofs of
`crypto/sha1` use. The definitions (`be32At` … `sha1`) are FIPS 180-4's §5.1.1 (padding), §5.3.1
(initial state) and §6.1 (the message schedule, the 80 rounds, the compression), written out, as
etcd-grove's `bootGo.sha1` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/BootValues.lean`), which is
the same text; the facts relate them to the shapes Go's `blockGeneric` computes them in (a 16-word
window of the schedule, `winIdx`; the majority function `((b | c) & d) | (b & c)`, `maj_go`) and
split the compression over a message's blocks (`compressAll`).
-/
module

public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace crypto.sha1

def be32At (l : List w8) (i : Nat) : w32 :=
  BitVec.ofNat 32 ((l.drop i).take 4 |>.foldl (fun acc b => acc * 256 + b.toNat) 0)

def schedule (blk : List w8) : Array w32 := Id.run do
  let mut w : Array w32 := #[]
  for t in [0:16] do
    w := w.push (be32At blk (4 * t))
  for t in [16:80] do
    w := w.push ((w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!).rotateLeft 1)
  return w

def bytes32 (x : w32) : List w8 :=
  [BitVec.ofNat 8 (x.toNat / 2 ^ 24), BitVec.ofNat 8 (x.toNat / 2 ^ 16),
    BitVec.ofNat 8 (x.toNat / 2 ^ 8), BitVec.ofNat 8 x.toNat]

def bytes64 (x : w64) : List w8 :=
  (List.range 8).map (fun i => BitVec.ofNat 8 (x.toNat / 2 ^ (8 * (7 - i))))

def pad (m : List w8) : List w8 :=
  m ++ [BitVec.ofNat 8 0x80] ++ List.replicate ((119 - m.length % 64) % 64) (BitVec.ofNat 8 0) ++
    bytes64 (BitVec.ofNat 64 (m.length * 8))

abbrev St := w32 × w32 × w32 × w32 × w32

def round (w : Array w32) (s : St) (t : Nat) : St :=
  let (a, b, c, d, e) := s
  let (f, k) : w32 × w32 :=
    if t < 20 then ((b &&& c) ||| (~~~b &&& d), BitVec.ofNat 32 0x5A827999)
    else if t < 40 then (b ^^^ c ^^^ d, BitVec.ofNat 32 0x6ED9EBA1)
    else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), BitVec.ofNat 32 0x8F1BBCDC)
    else (b ^^^ c ^^^ d, BitVec.ofNat 32 0xCA62C1D6)
  (a.rotateLeft 5 + f + e + k + w[t]!, a, b.rotateLeft 30, c, d)

def compress (h : St) (blk : List w8) : St :=
  let w := schedule blk
  let (a, b, c, d, e) := (List.range 80).foldl (round w) h
  let (h0, h1, h2, h3, h4) := h
  (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)

def init : St :=
  (BitVec.ofNat 32 0x67452301, BitVec.ofNat 32 0xEFCDAB89, BitVec.ofNat 32 0x98BADCFE,
    BitVec.ofNat 32 0x10325476, BitVec.ofNat 32 0xC3D2E1F0)

def sha1 (m : List w8) : List w8 :=
  let p := pad m
  let (h0, h1, h2, h3, h4) :=
    (List.range (p.length / 64)).foldl (fun h i => compress h ((p.drop (64 * i)).take 64)) init
  bytes32 h0 ++ bytes32 h1 ++ bytes32 h2 ++ bytes32 h3 ++ bytes32 h4

/-- the schedule's words, recursively -/
def sched (blk : List w8) : Nat → w32
  | t => if t < 16 then be32At blk (4 * t) else
      ((sched blk (t - 3) ^^^ sched blk (t - 8) ^^^ sched blk (t - 14) ^^^ sched blk (t - 16)).rotateLeft 1)
termination_by t => t
decreasing_by all_goals omega

theorem push_getElem!_lt (a : Array w32) (x : w32) (i : Nat) (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  simp [h, Array.getElem_push_lt, Nat.lt_succ_of_lt h]

theorem push_getElem!_eq (a : Array w32) (x : w32) :
    (a.push x)[a.size]! = x := by
  simp

/-- a fold that pushes `f a t` for each `t`: its size and elements -/
theorem foldl_push_spec (f : Array w32 → Nat → w32) (g : Nat → w32) :
    ∀ (n : Nat) (a : Array w32),
      (∀ t, t < a.size → a[t]! = g t) →
      (∀ b : Array w32, a.size ≤ b.size → b.size < a.size + n → (∀ t, t < b.size → b[t]! = g t) →
        f b b.size = g b.size) →
      ((List.range' a.size n).foldl (fun b t => b.push (f b t)) a).size = a.size + n ∧
      ∀ t, t < a.size + n →
        ((List.range' a.size n).foldl (fun b t => b.push (f b t)) a)[t]! = g t := by
  intro n
  induction n with
  | zero => intro a ha _; simpa using ha
  | succ n ih =>
    intro a ha hf
    simp only [List.range'_succ, List.foldl_cons]
    have hpush : ∀ t, t < (a.push (f a a.size)).size → (a.push (f a a.size))[t]! = g t := by
      intro t ht
      simp only [Array.size_push] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
      · rw [push_getElem!_lt _ _ _ h]; exact ha t h
      · subst h; rw [push_getElem!_eq]; exact hf a (by omega) (by omega) ha
    have := ih (a.push (f a a.size)) hpush (by
      intro b hb0 hb hb'; simp only [Array.size_push] at hb hb0; exact hf b (by omega) (by omega) hb')
    simp only [Array.size_push] at this
    refine ⟨by omega, ?_⟩
    intro t ht
    exact this.2 t (by omega)

theorem schedule_eq (blk : List w8) :
    schedule blk = (List.range' 16 64).foldl
      (fun w t => w.push ((w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!).rotateLeft 1))
      ((List.range' 0 16).foldl (fun w t => w.push (be32At blk (4 * t))) #[]) := by
  simp [schedule, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl]

theorem sched_lt (blk : List w8) (t : Nat) (h : t < 16) : sched blk t = be32At blk (4 * t) := by
  rw [sched]; simp [h]

theorem sched_ge (blk : List w8) (t : Nat) (h : 16 ≤ t) : sched blk t =
    ((sched blk (t - 3) ^^^ sched blk (t - 8) ^^^ sched blk (t - 14) ^^^ sched blk (t - 16)).rotateLeft 1) := by
  rw [sched]; simp [show ¬ t < 16 by omega]

theorem schedule_spec (blk : List w8) :
    (schedule blk).size = 80 ∧ ∀ t, t < 80 → (schedule blk)[t]! = sched blk t := by
  rw [schedule_eq]
  have h1 := foldl_push_spec (fun _ t => be32At blk (4 * t)) (sched blk) 16 #[]
    (by intro t ht; simp at ht) (by
      intro b _ hb _; simp at hb; exact (sched_lt blk _ hb).symm)
  simp only [List.size_toArray, List.length_nil, Nat.zero_add] at h1
  have h2 := foldl_push_spec
    (fun w t => (w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!).rotateLeft 1) (sched blk) 64
    ((List.range' 0 16).foldl (fun w t => w.push (be32At blk (4 * t))) #[]) h1.2 (by
      intro b hge hb hb'
      rw [h1.1] at hb hge
      rw [sched_ge blk _ hge, hb' _ (by omega), hb' _ (by omega), hb' _ (by omega), hb' _ (by omega)])
  rw [h1.1] at h2
  exact ⟨h2.1, fun t ht => h2.2 t ht⟩


/-! ### Go's forms -/

theorem maj_go (b c d : w32) :
    ((b ||| c) &&& d) ||| (b &&& c) = (b &&& c) ||| (b &&& d) ||| (c &&& d) := by
  ext i; simp only [BitVec.getElem_or, BitVec.getElem_and]
  cases b[i] <;> cases c[i] <;> cases d[i] <;> rfl

attribute [local irreducible] compress in
/-- The blocks of `m` compressed into `h`: its full 64-byte blocks. -/
def compressAll (h : St) (m : List w8) : St :=
  (List.range (m.length / 64)).foldl (fun h i => compress h ((m.drop (64 * i)).take 64)) h

theorem compressAll_cons_block (h : St) (blk m : List w8) (hb : blk.length = 64) :
    compressAll h (blk ++ m) = compressAll (compress h blk) m := by
  unfold compressAll
  have hl : (blk ++ m).length / 64 = m.length / 64 + 1 := by
    simp only [List.length_append, hb]; omega
  have hd : ∀ i : Nat, (blk ++ m).drop (64 * (i + 1)) = m.drop (64 * i) := by
    intro i
    rw [show 64 * (i + 1) = blk.length + 64 * i by rw [hb]; omega, ← List.drop_drop,
      List.drop_left]
  have h0 : ((blk ++ m).drop (64 * 0)).take 64 = blk := by
    simp [hb]
  rw [hl, List.range_succ_eq_map, List.foldl_cons, List.foldl_map, h0]
  simp only [hd]

theorem compressAll_short (h : St) (m : List w8) (hm : m.length < 64) : compressAll h m = h := by
  unfold compressAll
  rw [show m.length / 64 = 0 by omega]; rfl

theorem compressAll_append (h : St) (m1 m2 : List w8) (hm : m1.length % 64 = 0) :
    compressAll h (m1 ++ m2) = compressAll (compressAll h m1) m2 := by
  induction hk : m1.length / 64 generalizing h m1 with
  | zero =>
    have : m1 = [] := by apply List.eq_nil_of_length_eq_zero; omega
    subst this; simp [compressAll]
  | succ k ih =>
    have hlen : 64 ≤ m1.length := by omega
    obtain ⟨blk, rest, rfl, hb⟩ : ∃ blk rest, m1 = blk ++ rest ∧ blk.length = 64 :=
      ⟨m1.take 64, m1.drop 64, (List.take_append_drop 64 m1).symm, by simp; omega⟩
    simp only [List.length_append, hb] at hm hk
    rw [List.append_assoc, compressAll_cons_block _ _ _ hb, compressAll_cons_block _ _ _ hb]
    exact ih _ _ (by omega) (by omega)

theorem compressAll_take (h : St) (m : List w8) :
    compressAll h m = compressAll h (m.take (64 * (m.length / 64))) := by
  have hm := List.take_append_drop (64 * (m.length / 64)) m
  conv => lhs; rw [← hm]
  have hl : (m.take (64 * (m.length / 64))).length = 64 * (m.length / 64) := by
    simp; omega
  rw [compressAll_append _ _ _ (by rw [hl]; omega), compressAll_short _ _ (by simp; omega)]

/-! ### `blockGeneric`'s window of the schedule -/

/-- After `i` rounds, `w[j]` holds the schedule's word `winIdx i j` (Go keeps the last 16 words,
word `t` at `t % 16`). -/
def winIdx (i j : Nat) : Nat := if i < 16 then j else i - 16 + (j + 16 - i % 16) % 16

theorem winIdx_lt16 (i j : Nat) (hi : i < 16) : winIdx i j = j := by simp [winIdx, hi]

theorem winIdx_3 (i : Nat) (hi : 16 ≤ i) : winIdx i ((i - 3) % 16) = i - 3 := by
  simp only [winIdx, show ¬ i < 16 by omega, ite_false]; omega
theorem winIdx_8 (i : Nat) (hi : 16 ≤ i) : winIdx i ((i - 8) % 16) = i - 8 := by
  simp only [winIdx, show ¬ i < 16 by omega, ite_false]; omega
theorem winIdx_14 (i : Nat) (hi : 16 ≤ i) : winIdx i ((i - 14) % 16) = i - 14 := by
  simp only [winIdx, show ¬ i < 16 by omega, ite_false]; omega
theorem winIdx_16 (i : Nat) (hi : 16 ≤ i) : winIdx i (i % 16) = i - 16 := by
  simp only [winIdx, show ¬ i < 16 by omega, ite_false]; omega

theorem winIdx_succ (i j : Nat) (hi : 16 ≤ i) (hj : j < 16) :
    winIdx (i + 1) j = if j = i % 16 then i else winIdx i j := by
  simp only [winIdx, show ¬ i < 16 by omega, show ¬ i + 1 < 16 by omega, ite_false]
  split <;> omega

theorem winIdx_16_eq (j : Nat) (hj : j < 16) : winIdx 16 j = j := by
  simp only [winIdx, show ¬ (16 : Nat) < 16 by omega, ite_false]; omega

/-- Go's round: `t := RotateLeft32(a, 5) + f + e + w + K`, then the shift. -/
theorem round_go (w : Array w32) (a b c d e : w32) (t : Nat) (f k : w32)
    (hfk : (f, k) = (if t < 20 then ((b &&& c) ||| (~~~b &&& d), BitVec.ofNat 32 0x5A827999)
      else if t < 40 then (b ^^^ c ^^^ d, BitVec.ofNat 32 0x6ED9EBA1)
      else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), BitVec.ofNat 32 0x8F1BBCDC)
      else (b ^^^ c ^^^ d, BitVec.ofNat 32 0xCA62C1D6))) :
    round w (a, b, c, d, e) t = (a.rotateLeft 5 + f + e + w[t]! + k, a, b.rotateLeft 30, c, d) := by
  simp only [round]
  rw [← hfk]
  simp only [Prod.mk.injEq, and_true]
  ac_rfl

/-- FIPS 180-4's `f` and `K` of round `t`. -/
def fk (t : Nat) (b c d : w32) : w32 × w32 :=
  if t < 20 then ((b &&& c) ||| (~~~b &&& d), BitVec.ofNat 32 0x5A827999)
  else if t < 40 then (b ^^^ c ^^^ d, BitVec.ofNat 32 0x6ED9EBA1)
  else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), BitVec.ofNat 32 0x8F1BBCDC)
  else (b ^^^ c ^^^ d, BitVec.ofNat 32 0xCA62C1D6)

/-- Go's window after round `i` (`blockGeneric`): from round 16 on, `w[i & 0xf]` is replaced by
the next schedule word. -/
def winStep (wl : List w32) (i : Nat) : List w32 :=
  if i < 16 then wl
  else wl.set (i % 16) ((wl[(i - 3) % 16]! ^^^ wl[(i - 8) % 16]! ^^^ wl[(i - 14) % 16]! ^^^
    wl[i % 16]!).rotateLeft 1)

/-- **One of `blockGeneric`'s rounds**: from the state after `i` rounds and the window holding
the schedule words `winIdx i`, Go's step gives the state after `i + 1` rounds and the window
`winIdx (i + 1)`. -/
theorem round_step (blk : List w8) (h : St) (i : Nat) (hi : i < 80) (wl : List w32) (a b c d e : w32)
    (Hst : (List.range i).foldl (round (schedule blk)) h = (a, b, c, d, e))
    (Hw : ∀ j, j < 16 → wl[j]! = sched blk (winIdx i j)) (Hlen : wl.length = 16) :
    (List.range (i + 1)).foldl (round (schedule blk)) h =
      (a.rotateLeft 5 + (fk i b c d).1 + e + (winStep wl i)[i % 16]! + (fk i b c d).2, a,
        b.rotateLeft 30, c, d) ∧
    (winStep wl i).length = 16 ∧
    ∀ j, j < 16 → (winStep wl i)[j]! = sched blk (winIdx (i + 1) j) := by
  have hsch := (schedule_spec blk).2
  have hwi : (winStep wl i)[i % 16]! = sched blk i := by
    unfold winStep
    split
    · rename_i h16; rw [Nat.mod_eq_of_lt h16, Hw i h16, winIdx_lt16 _ _ h16]
    · rename_i h16
      have hlt : i % 16 < wl.length := by omega
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hlt]
      simp only [Option.getD_some]
      rw [Hw _ (by omega), Hw _ (by omega), Hw _ (by omega), Hw _ (by omega),
        winIdx_3 _ (by omega), winIdx_8 _ (by omega), winIdx_14 _ (by omega), winIdx_16 _ (by omega),
        sched_ge blk i (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.range_succ, List.foldl_append, Hst, List.foldl_cons, List.foldl_nil,
      round_go (schedule blk) a b c d e i (fk i b c d).1 (fk i b c d).2 rfl, hwi, hsch i hi]
  · unfold winStep; split <;> simp [Hlen]
  · intro j hj
    by_cases h16 : i < 16
    · have : winStep wl i = wl := by simp [winStep, h16]
      rw [this, Hw j hj, winIdx_lt16 _ _ h16]
      by_cases h15 : i + 1 < 16
      · rw [winIdx_lt16 _ _ h15]
      · rw [show i + 1 = 16 by omega, winIdx_16_eq j hj]
    · rw [winIdx_succ i j (by omega) hj]
      by_cases hji : j = i % 16
      · subst hji; rw [if_pos rfl, hwi]
      · rw [if_neg hji]
        unfold winStep
        rw [if_neg h16, List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji),
          ← List.getElem!_eq_getElem?_getD]
        exact Hw j hj

/-- Go's `f` of rounds 40–59, `((b | c) & d) | (b & c)`, is FIPS 180-4's majority. -/
theorem fk_maj (t : Nat) (b c d : w32) (h1 : 40 ≤ t) (h2 : t < 60) :
    fk t b c d = (((b ||| c) &&& d) ||| (b &&& c), BitVec.ofNat 32 0x8F1BBCDC) := by
  simp only [fk, show ¬ t < 20 by omega, show ¬ t < 40 by omega, h2, ite_false, ite_true, maj_go]

/-- `compress` is the fold of the 80 rounds, then the addition. -/
theorem compress_eq (g0 g1 g2 g3 g4 : w32) (blk : List w8) (a b c d e : w32)
    (H : (List.range 80).foldl (round (schedule blk)) (g0, g1, g2, g3, g4) = (a, b, c, d, e)) :
    compress (g0, g1, g2, g3, g4) blk = (g0 + a, g1 + b, g2 + c, g3 + d, g4 + e) := by
  simp only [compress, H]

/-- The compression of one more block. -/
theorem compressAll_take_succ (h : St) (bs : List w8) (k : Nat) (hk : 64 * (k + 1) ≤ bs.length) :
    compressAll h (bs.take (64 * (k + 1))) =
      compress (compressAll h (bs.take (64 * k))) ((bs.drop (64 * k)).take 64) := by
  have e : bs.take (64 * (k + 1)) = bs.take (64 * k) ++ (bs.drop (64 * k)).take 64 := by
    rw [show 64 * (k + 1) = 64 * k + 64 by omega, List.take_add]
  rw [e, compressAll_append _ _ _ (by simp; omega)]
  have h64 : ((bs.drop (64 * k)).take 64).length = 64 := by simp; omega
  conv => lhs; rw [← List.append_nil ((bs.drop (64 * k)).take 64)]
  rw [compressAll_cons_block _ _ _ h64, compressAll_short _ _ (by simp)]

theorem sha1_eq (m : List w8) : sha1 m =
    let (h0, h1, h2, h3, h4) := compressAll init (pad m)
    bytes32 h0 ++ bytes32 h1 ++ bytes32 h2 ++ bytes32 h3 ++ bytes32 h4 := rfl

end crypto.sha1
end Perennial
