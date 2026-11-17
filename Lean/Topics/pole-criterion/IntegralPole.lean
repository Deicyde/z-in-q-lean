import PoleCriterion

namespace PoleCriterion
open Lean.Grind

/-- Expansion in the original input b and the three scaled witnesses. -/
def expanded (b u v w : Rat) : Rat :=
  1 * b^3 * v^4
  + 6 * b^3 * v^2 * w^2
  + 9 * b^3 * w^4
  + 17 * b^2 * u^2 * v^4
  + 102 * b^2 * u^2 * v^2 * w^2
  + 153 * b^2 * u^2 * w^4
  - 136 * b^2 * u * v^2 * w
  - 408 * b^2 * u * w^3
  - 17 * b^2 * v^4
  - 102 * b^2 * v^2 * w^2
  - 34 * b^2 * v^2
  - 153 * b^2 * w^4
  + 102 * b^2 * w^2
  - 578 * b * u^2 * v^2
  + 1734 * b * u^2 * w^2
  + 4624 * b * u * v * w
  - 2312 * b * u * w
  + 578 * b * v^2
  - 1734 * b * w^2
  + 289 * b
  + 4913 * u^2
  - 4913

theorem table_identity (b u v w : Rat) : expanded b u v w = integral b u v w := by
  unfold expanded integral
  grobner

theorem table_exact (b : Rat) : WitnessTransfer.FixedZero.PsiZero b ↔
    ∃ u v w : Rat, expanded b u v w=0 := by
  simpa only [table_identity] using integral_exact b

end PoleCriterion
#print axioms PoleCriterion.table_identity
#print axioms PoleCriterion.table_exact
