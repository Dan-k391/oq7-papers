import OQ7

namespace OQ7IntegrityScratch
axiom injected_false : False
theorem intermediate_false : False := injected_false
theorem inherited_invalid_arithmetic : (1 : Nat) = 0 := False.elim intermediate_false
#print axioms inherited_invalid_arithmetic
end OQ7IntegrityScratch
