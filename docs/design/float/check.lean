/-
The differential test of the IEEE 754 definitions (`Perennial/Golang/Defn/Float.lean`) against
Go: reads the vectors printed by `gen/main.go` and checks that the Lean definitions agree, a NaN
result agreeing with any NaN (the step rules allow any NaN, `go.float64Result`). See README.md.

Usage: lake env lean --run docs/design/float/check.lean vectors.txt
-/
import Perennial.Golang.Defn.Float

open Perennial

def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- Whether Lean agrees with Go's `want` on `op args`: `none` for an unknown line. -/
def check (op : String) (args : List Nat) (want : String) : Option Bool := do
  let h64 (r : w64) : Option Bool := do
    let g : w64 := BitVec.ofNat 64 (← parseHex want)
    return r == g || (float64IsNaN r && float64IsNaN g)
  let h32 (r : w32) : Option Bool := do
    let g : w32 := BitVec.ofNat 32 (← parseHex want)
    return r == g || (float32IsNaN r && float32IsNaN g)
  let hb (r : Bool) : Option Bool := return toString r == want
  match op, args with
  | "add64", [a, b] => h64 (float64Add (.ofNat 64 a) (.ofNat 64 b))
  | "sub64", [a, b] => h64 (float64Sub (.ofNat 64 a) (.ofNat 64 b))
  | "mul64", [a, b] => h64 (float64Mul (.ofNat 64 a) (.ofNat 64 b))
  | "div64", [a, b] => h64 (float64Div (.ofNat 64 a) (.ofNat 64 b))
  | "leb64", [a, b] => hb (float64Leb (.ofNat 64 a) (.ofNat 64 b))
  | "eq64", [a, b] => hb (float64Eq (.ofNat 64 a) (.ofNat 64 b))
  | "lt64", [a, b] => hb (float64Leb (.ofNat 64 a) (.ofNat 64 b) && !float64Eq (.ofNat 64 a) (.ofNat 64 b))
  | "neg64", [a] => h64 (float64Neg (.ofNat 64 a))
  | "f64to32", [a] => h32 (float64ToFloat32 (.ofNat 64 a))
  | "add32", [a, b] => h32 (float32Add (.ofNat 32 a) (.ofNat 32 b))
  | "sub32", [a, b] => h32 (float32Sub (.ofNat 32 a) (.ofNat 32 b))
  | "mul32", [a, b] => h32 (float32Mul (.ofNat 32 a) (.ofNat 32 b))
  | "div32", [a, b] => h32 (float32Div (.ofNat 32 a) (.ofNat 32 b))
  | "leb32", [a, b] => hb (float32Leb (.ofNat 32 a) (.ofNat 32 b))
  | "eq32", [a, b] => hb (float32Eq (.ofNat 32 a) (.ofNat 32 b))
  | "neg32", [a] => h32 (float32Neg (.ofNat 32 a))
  | "i64to64", [a] => h64 (int64ToFloat64 (.ofNat 64 a))
  | "u64to64", [a] => h64 (uint64ToFloat64 (.ofNat 64 a))
  | "i32to64", [a] => h64 (int32ToFloat64 (.ofNat 32 a))
  | "u32to64", [a] => h64 (uint32ToFloat64 (.ofNat 32 a))
  | _, _ => none

def main (argv : List String) : IO UInt32 := do
  let [path] := argv | IO.eprintln "usage: check.lean vectors.txt"; return 2
  let mut total := 0
  let mut bad := 0
  let mut perOp : Std.HashMap String Nat := {}
  for line in (← IO.FS.lines path) do
    let ws := (line.splitOn " ").filter (· ≠ "")
    let some (op, rest) := (ws.head?.map (fun op => (op, ws.tail))) | continue
    let some want := rest.getLast? | continue
    let some args := (rest.dropLast.mapM parseHex) | IO.eprintln s!"bad line: {line}"; return 2
    match check op args want with
    | none => IO.eprintln s!"bad line: {line}"; return 2
    | some ok =>
      total := total + 1
      perOp := perOp.insert op (perOp.getD op 0 + 1)
      unless ok do
        bad := bad + 1
        if bad ≤ 20 then IO.println s!"MISMATCH: {line}"
  for (op, k) in perOp.toList.mergeSort (fun a b => a.1 ≤ b.1) do
    IO.println s!"  {op}: {k}"
  IO.println s!"{total} vectors, {bad} mismatches"
  return if bad = 0 then 0 else 1
