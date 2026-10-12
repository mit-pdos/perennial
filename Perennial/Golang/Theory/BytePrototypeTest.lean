/-
Axiom check of the byte-memory prototype (`BytePrototype.lean`): every spec
should depend only on `propext`, `Classical.choice` and `Quot.sound` (no
`sorryAx`).
-/
module

public import Perennial.Golang.Theory.BytePrototype

namespace Perennial

#print axioms typedBytes_agree
#print axioms typedBytes_prod
#print axioms wp_strLit
#print axioms wp_strBytes
#print axioms wp_strEq
#print axioms wp_strConcat
#print axioms wp_strIndex
#print axioms wp_toIface
#print axioms wp_ifaceAssert2_ok
#print axioms wp_ifaceAssert2_fail
#print axioms wp_ifaceTypeEq
#print axioms wp_funcLit
#print axioms wp_funcCall
#print axioms wp_unsafeAddExample

end Perennial
