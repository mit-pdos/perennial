/-
`wp_apply` with a spec whose postcondition is a proposition introduced in the proof
(regression test, mit-pdos/perennial#680).

`wp_apply`'s post-processing used to inspect the continuation's premise (`Q` below) outside
the goal's local context; that failed on a variable the proof had introduced, the failure
admitted the goal through `<;>`'s error recovery, and the error was not shown, so the
proof elaborated with a `sorry` in it (the shape of `sync.OnceFunc`'s proof). Each theorem
below must elaborate without `sorryAx`.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial
namespace WpApplyVarPostTest

open Iris Iris.BI

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `wp_apply` of an Iris hypothesis whose postcondition is the `iintro`-ed `Q`. -/
theorem wp_apply_var_post (f : val) :
    ⊢ ∀ Q : IProp GF, (□ {{ True }} (App (Val f) (Val #())) {{ RET #(); Q }}) -∗
      WP (App (Val f) (Val #())) {{ fun _ => Q }} := by
  iintro %Q #Hf
  wp_apply Hf
  iintro HQ
  iexact HQ

/-- The same with `as`, and with `wp_apply_core`. -/
theorem wp_apply_var_post_as (f : val) :
    ⊢ ∀ Q : IProp GF, (□ {{ True }} (App (Val f) (Val #())) {{ RET #(); Q }}) -∗
      WP (App (Val f) (Val #())) {{ fun _ => Q }} := by
  iintro %Q #Hf
  wp_apply Hf as HQ
  iexact HQ

theorem wp_apply_core_var_post (f : val) :
    ⊢ ∀ Q : IProp GF, (□ {{ True }} (App (Val f) (Val #())) {{ RET #(); Q }}) -∗
      WP (App (Val f) (Val #())) {{ fun _ => Q }} := by
  iintro %Q #Hf
  wp_apply_core Hf
  iintro HQ
  iexact HQ

/-- info: 'Perennial.WpApplyVarPostTest.wp_apply_var_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_apply_var_post
/-- info: 'Perennial.WpApplyVarPostTest.wp_apply_var_post_as' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_apply_var_post_as
/-- info: 'Perennial.WpApplyVarPostTest.wp_apply_core_var_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_apply_core_var_post

end

end WpApplyVarPostTest
end Perennial
