import ScalarUnitTree
import ScalarCoordinates

/-! Passing from three quadratic-field functions to the six scalar leaves. -/
namespace Sun28.ScalarPlaces
open ZInQ Sun28.ScalarHeight Sun28.Forward Sun28.Scalar Sun28.WitnessIndices
noncomputable section

theorem divided_coefficient {p : ℕ} [Fact p.Prime] {r : ℤ} (rn : r≠0)
    {k : ℕ} {x : ℚ} (bound : x≠0 → 1+(k:ℤ)*padicValInt p r≤padicValRat p x) :
    1≤ratOrder p (x/(r:ℚ)^k) := by
  by_cases z : x=0
  · simp [z]
  have rq : (r:ℚ)≠0 := Int.cast_ne_zero.mpr rn
  rw [rat_order_value (div_ne_zero z (pow_ne_zero _ rq)),padicValRat.div z (pow_ne_zero _ rq),
    padicValRat.pow,padicValRat.of_int]
  apply WithTop.coe_le_coe.mpr
  linarith [bound z]

theorem scalar_unit_of_depths {p : ℕ} [Fact p.Prime] {r : ℤ} (rn : r≠0)
    (w : NinePoints) (M : ℕ)
    (h : Deep p (1+padicValInt p r) (reciprocal (scalarEquiv w.H)))
    (s : Deep p (1+padicValInt p r) (reciprocal (scalarEquiv (scalarPoint w M))))
    (quotient : Deep p (1+48*padicValInt p r)
      (parameter (scalarEquiv (scalarPoint w M))/parameter (scalarEquiv w.H))) :
    scalarTree (r:ℚ) (scalarEntries w M)≠0 ∧
      padicValRat p (scalarTree (r:ℚ) (scalarEntries w M))=0 := by
  obtain ⟨hr,hi⟩ := deep_coordinates h
  obtain ⟨sr,si⟩ := deep_coordinates s
  obtain ⟨qr,qi⟩ := deep_coordinates quotient
  apply rat_tree_unit
  intro i
  fin_cases i <;> apply divided_coefficient rn <;>
    first | simpa [leafPower,scalarEntries] using hr | simpa [leafPower,scalarEntries] using hi |
            simpa [leafPower,scalarEntries] using sr | simpa [leafPower,scalarEntries] using si |
            simpa [leafPower,scalarEntries] using qr | simpa [leafPower,scalarEntries] using qi

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.divided_coefficient
#print axioms Sun28.ScalarPlaces.scalar_unit_of_depths
