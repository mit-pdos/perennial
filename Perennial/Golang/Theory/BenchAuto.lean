/-
Benchmark for `wp_auto` on straight-line code (not imported by the umbrella
`Perennial.Golang.Theory`; build with `lake build Perennial.Golang.Theory.BenchAuto`).

Each function has `n` statements `x_i := new(uint64); *x_i = *x_{i-1} + 1`
(an allocation, a load and a store each). Measure with
`lake env lean Perennial/Golang/Theory/BenchAuto.lean` (`set_option profiler true`
prints the tactic and kernel times).

Measurements (2026-10, loaded 32-core machine, whole file per size):

| statements | before (wall) | after (wall) | `wp_auto` tactic before → after | kernel before → after |
|-----------:|--------------:|-------------:|--------------------------------:|----------------------:|
| 25         | 6.3 s         | 3.2 s        | 1.2 s → 0.6 s                   | 1.9 s → 0.3 s         |
| 60         | 32 s          | 9 s          | 10.4 s → 2.0 s                  | 10.1 s → 1.4 s        |

(about 2 s of each wall time is loading the imports.) The main costs were the
kernel deciding `String` equalities while checking `subst` by `rfl`, re-abstracting
the continuation proof at every allocation, one typeclass search per hypothesis
for the `▷` of every pure step, `simp` over the whole expression after every
step, and instantiating the whole proof at every step (`mkAppNamed`).
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
open Iris Iris.BI

section bench
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true

/-- 25 statements (alloc + load + store each). -/
example : ⊢ WP gl(let: "x0" := GoAlloc go.uint64 #(W64 0) in
     "x0" <-[go.uint64] (#(W64 0) +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x1" := GoAlloc go.uint64 #(W64 1) in
     "x1" <-[go.uint64] (![go.uint64] "x0" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x2" := GoAlloc go.uint64 #(W64 2) in
     "x2" <-[go.uint64] (![go.uint64] "x1" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x3" := GoAlloc go.uint64 #(W64 3) in
     "x3" <-[go.uint64] (![go.uint64] "x2" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x4" := GoAlloc go.uint64 #(W64 4) in
     "x4" <-[go.uint64] (![go.uint64] "x3" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x5" := GoAlloc go.uint64 #(W64 5) in
     "x5" <-[go.uint64] (![go.uint64] "x4" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x6" := GoAlloc go.uint64 #(W64 6) in
     "x6" <-[go.uint64] (![go.uint64] "x5" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x7" := GoAlloc go.uint64 #(W64 7) in
     "x7" <-[go.uint64] (![go.uint64] "x6" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x8" := GoAlloc go.uint64 #(W64 8) in
     "x8" <-[go.uint64] (![go.uint64] "x7" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x9" := GoAlloc go.uint64 #(W64 9) in
     "x9" <-[go.uint64] (![go.uint64] "x8" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x10" := GoAlloc go.uint64 #(W64 10) in
     "x10" <-[go.uint64] (![go.uint64] "x9" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x11" := GoAlloc go.uint64 #(W64 11) in
     "x11" <-[go.uint64] (![go.uint64] "x10" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x12" := GoAlloc go.uint64 #(W64 12) in
     "x12" <-[go.uint64] (![go.uint64] "x11" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x13" := GoAlloc go.uint64 #(W64 13) in
     "x13" <-[go.uint64] (![go.uint64] "x12" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x14" := GoAlloc go.uint64 #(W64 14) in
     "x14" <-[go.uint64] (![go.uint64] "x13" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x15" := GoAlloc go.uint64 #(W64 15) in
     "x15" <-[go.uint64] (![go.uint64] "x14" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x16" := GoAlloc go.uint64 #(W64 16) in
     "x16" <-[go.uint64] (![go.uint64] "x15" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x17" := GoAlloc go.uint64 #(W64 17) in
     "x17" <-[go.uint64] (![go.uint64] "x16" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x18" := GoAlloc go.uint64 #(W64 18) in
     "x18" <-[go.uint64] (![go.uint64] "x17" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x19" := GoAlloc go.uint64 #(W64 19) in
     "x19" <-[go.uint64] (![go.uint64] "x18" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x20" := GoAlloc go.uint64 #(W64 20) in
     "x20" <-[go.uint64] (![go.uint64] "x19" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x21" := GoAlloc go.uint64 #(W64 21) in
     "x21" <-[go.uint64] (![go.uint64] "x20" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x22" := GoAlloc go.uint64 #(W64 22) in
     "x22" <-[go.uint64] (![go.uint64] "x21" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x23" := GoAlloc go.uint64 #(W64 23) in
     "x23" <-[go.uint64] (![go.uint64] "x22" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x24" := GoAlloc go.uint64 #(W64 24) in
     "x24" <-[go.uint64] (![go.uint64] "x23" +⟨go.uint64⟩ #(W64 1)) ;;
     #()) {{ v, (⌜v = #()⌝ : IProp GF) }} := by
  wp_auto
  ipureintro; rfl

/-- 60 statements (alloc + load + store each). -/
example : ⊢ WP gl(let: "x0" := GoAlloc go.uint64 #(W64 0) in
     "x0" <-[go.uint64] (#(W64 0) +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x1" := GoAlloc go.uint64 #(W64 1) in
     "x1" <-[go.uint64] (![go.uint64] "x0" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x2" := GoAlloc go.uint64 #(W64 2) in
     "x2" <-[go.uint64] (![go.uint64] "x1" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x3" := GoAlloc go.uint64 #(W64 3) in
     "x3" <-[go.uint64] (![go.uint64] "x2" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x4" := GoAlloc go.uint64 #(W64 4) in
     "x4" <-[go.uint64] (![go.uint64] "x3" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x5" := GoAlloc go.uint64 #(W64 5) in
     "x5" <-[go.uint64] (![go.uint64] "x4" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x6" := GoAlloc go.uint64 #(W64 6) in
     "x6" <-[go.uint64] (![go.uint64] "x5" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x7" := GoAlloc go.uint64 #(W64 7) in
     "x7" <-[go.uint64] (![go.uint64] "x6" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x8" := GoAlloc go.uint64 #(W64 8) in
     "x8" <-[go.uint64] (![go.uint64] "x7" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x9" := GoAlloc go.uint64 #(W64 9) in
     "x9" <-[go.uint64] (![go.uint64] "x8" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x10" := GoAlloc go.uint64 #(W64 10) in
     "x10" <-[go.uint64] (![go.uint64] "x9" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x11" := GoAlloc go.uint64 #(W64 11) in
     "x11" <-[go.uint64] (![go.uint64] "x10" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x12" := GoAlloc go.uint64 #(W64 12) in
     "x12" <-[go.uint64] (![go.uint64] "x11" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x13" := GoAlloc go.uint64 #(W64 13) in
     "x13" <-[go.uint64] (![go.uint64] "x12" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x14" := GoAlloc go.uint64 #(W64 14) in
     "x14" <-[go.uint64] (![go.uint64] "x13" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x15" := GoAlloc go.uint64 #(W64 15) in
     "x15" <-[go.uint64] (![go.uint64] "x14" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x16" := GoAlloc go.uint64 #(W64 16) in
     "x16" <-[go.uint64] (![go.uint64] "x15" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x17" := GoAlloc go.uint64 #(W64 17) in
     "x17" <-[go.uint64] (![go.uint64] "x16" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x18" := GoAlloc go.uint64 #(W64 18) in
     "x18" <-[go.uint64] (![go.uint64] "x17" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x19" := GoAlloc go.uint64 #(W64 19) in
     "x19" <-[go.uint64] (![go.uint64] "x18" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x20" := GoAlloc go.uint64 #(W64 20) in
     "x20" <-[go.uint64] (![go.uint64] "x19" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x21" := GoAlloc go.uint64 #(W64 21) in
     "x21" <-[go.uint64] (![go.uint64] "x20" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x22" := GoAlloc go.uint64 #(W64 22) in
     "x22" <-[go.uint64] (![go.uint64] "x21" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x23" := GoAlloc go.uint64 #(W64 23) in
     "x23" <-[go.uint64] (![go.uint64] "x22" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x24" := GoAlloc go.uint64 #(W64 24) in
     "x24" <-[go.uint64] (![go.uint64] "x23" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x25" := GoAlloc go.uint64 #(W64 25) in
     "x25" <-[go.uint64] (![go.uint64] "x24" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x26" := GoAlloc go.uint64 #(W64 26) in
     "x26" <-[go.uint64] (![go.uint64] "x25" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x27" := GoAlloc go.uint64 #(W64 27) in
     "x27" <-[go.uint64] (![go.uint64] "x26" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x28" := GoAlloc go.uint64 #(W64 28) in
     "x28" <-[go.uint64] (![go.uint64] "x27" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x29" := GoAlloc go.uint64 #(W64 29) in
     "x29" <-[go.uint64] (![go.uint64] "x28" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x30" := GoAlloc go.uint64 #(W64 30) in
     "x30" <-[go.uint64] (![go.uint64] "x29" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x31" := GoAlloc go.uint64 #(W64 31) in
     "x31" <-[go.uint64] (![go.uint64] "x30" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x32" := GoAlloc go.uint64 #(W64 32) in
     "x32" <-[go.uint64] (![go.uint64] "x31" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x33" := GoAlloc go.uint64 #(W64 33) in
     "x33" <-[go.uint64] (![go.uint64] "x32" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x34" := GoAlloc go.uint64 #(W64 34) in
     "x34" <-[go.uint64] (![go.uint64] "x33" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x35" := GoAlloc go.uint64 #(W64 35) in
     "x35" <-[go.uint64] (![go.uint64] "x34" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x36" := GoAlloc go.uint64 #(W64 36) in
     "x36" <-[go.uint64] (![go.uint64] "x35" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x37" := GoAlloc go.uint64 #(W64 37) in
     "x37" <-[go.uint64] (![go.uint64] "x36" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x38" := GoAlloc go.uint64 #(W64 38) in
     "x38" <-[go.uint64] (![go.uint64] "x37" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x39" := GoAlloc go.uint64 #(W64 39) in
     "x39" <-[go.uint64] (![go.uint64] "x38" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x40" := GoAlloc go.uint64 #(W64 40) in
     "x40" <-[go.uint64] (![go.uint64] "x39" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x41" := GoAlloc go.uint64 #(W64 41) in
     "x41" <-[go.uint64] (![go.uint64] "x40" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x42" := GoAlloc go.uint64 #(W64 42) in
     "x42" <-[go.uint64] (![go.uint64] "x41" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x43" := GoAlloc go.uint64 #(W64 43) in
     "x43" <-[go.uint64] (![go.uint64] "x42" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x44" := GoAlloc go.uint64 #(W64 44) in
     "x44" <-[go.uint64] (![go.uint64] "x43" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x45" := GoAlloc go.uint64 #(W64 45) in
     "x45" <-[go.uint64] (![go.uint64] "x44" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x46" := GoAlloc go.uint64 #(W64 46) in
     "x46" <-[go.uint64] (![go.uint64] "x45" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x47" := GoAlloc go.uint64 #(W64 47) in
     "x47" <-[go.uint64] (![go.uint64] "x46" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x48" := GoAlloc go.uint64 #(W64 48) in
     "x48" <-[go.uint64] (![go.uint64] "x47" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x49" := GoAlloc go.uint64 #(W64 49) in
     "x49" <-[go.uint64] (![go.uint64] "x48" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x50" := GoAlloc go.uint64 #(W64 50) in
     "x50" <-[go.uint64] (![go.uint64] "x49" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x51" := GoAlloc go.uint64 #(W64 51) in
     "x51" <-[go.uint64] (![go.uint64] "x50" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x52" := GoAlloc go.uint64 #(W64 52) in
     "x52" <-[go.uint64] (![go.uint64] "x51" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x53" := GoAlloc go.uint64 #(W64 53) in
     "x53" <-[go.uint64] (![go.uint64] "x52" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x54" := GoAlloc go.uint64 #(W64 54) in
     "x54" <-[go.uint64] (![go.uint64] "x53" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x55" := GoAlloc go.uint64 #(W64 55) in
     "x55" <-[go.uint64] (![go.uint64] "x54" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x56" := GoAlloc go.uint64 #(W64 56) in
     "x56" <-[go.uint64] (![go.uint64] "x55" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x57" := GoAlloc go.uint64 #(W64 57) in
     "x57" <-[go.uint64] (![go.uint64] "x56" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x58" := GoAlloc go.uint64 #(W64 58) in
     "x58" <-[go.uint64] (![go.uint64] "x57" +⟨go.uint64⟩ #(W64 1)) ;;
     let: "x59" := GoAlloc go.uint64 #(W64 59) in
     "x59" <-[go.uint64] (![go.uint64] "x58" +⟨go.uint64⟩ #(W64 1)) ;;
     #()) {{ v, (⌜v = #()⌝ : IProp GF) }} := by
  wp_auto
  ipureintro; rfl

end bench

end Perennial
