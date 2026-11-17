import OrdinaryChart

/-! Literal sixteen-term formula for the polynomial used by Sun. -/
namespace Sun28.Ordinary
open scoped BigOperators
variable {L : Type*} [Field L]

theorem degree64_formula (b z : L) :
    logTrunc (shortDifferential b) 64 z =
      ∑ i ∈ Finset.range 16, (Nat.choose (2*i) i:L)*b^i*z^(4*i+1)/(4*i+1:ℕ) := by
  norm_num [logTrunc,shortDifferential,Finset.sum_range_succ]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.degree64_formula
