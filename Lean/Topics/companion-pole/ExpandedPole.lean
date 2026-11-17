import SignedPole

namespace SignedPole

/-- The sparse table, in decreasing lexicographic order on (b,x,v,w). -/
def expanded (b x v w : Rat) : Rat :=
  - 4913 * b^3 * v^4
  - 29478 * b^3 * v^2 * w^2
  - 44217 * b^3 * w^4
  - 289 * b^2 * x^2 * v^4
  - 1734 * b^2 * x^2 * v^2 * w^2
  - 2601 * b^2 * x^2 * w^4
  + 9826 * b^2 * x * v^4
  - 1156 * b^2 * x * v^3
  + 58956 * b^2 * x * v^2 * w^2
  - 1156 * b^2 * x * v^2 * w
  - 3468 * b^2 * x * v * w^2
  + 88434 * b^2 * x * w^4
  - 3468 * b^2 * x * w^3
  + 9826 * b^2 * v^3
  + 29478 * b^2 * v^2 * w
  + 29478 * b^2 * v * w^2
  - 3468 * b^2 * v * w
  + 88434 * b^2 * w^3
  + 578 * b * x^2 * v^3
  - 578 * b * x^2 * v^2 * w
  + 1734 * b * x^2 * v * w^2
  + 68 * b * x^2 * v * w
  - 1734 * b * x^2 * w^3
  + 2312 * b * x * v * w
  + 68 * b * x * v
  - 68 * b * x * w
  - 578 * b * v
  + 1734 * b * w
  + 17 * b
  - 34 * x^2 * v
  - 34 * x^2 * w
  + 1 * x^2
  - 34 * x

theorem coefficient_identity (b x v w : Rat) : polynomial b x v w = expanded b x v w := by
  unfold polynomial expanded
  grobner

theorem exact_expansion (b : Rat) :
    WitnessTransfer.FixedZero.PsiZero b ↔ ∃ x v w : Rat, expanded b x v w = 0 := by
  simp only [← coefficient_identity]
  exact SignedPole.exact b

end SignedPole
#print axioms SignedPole.coefficient_identity
#print axioms SignedPole.exact_expansion
