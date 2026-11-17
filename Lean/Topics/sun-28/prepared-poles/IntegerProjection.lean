import PreparedPoles
import FixedCertificate
import LeastChart
import UnconditionalOrdinaryCharts

namespace Sun28.PreparedPoles
open ZInQ Ordinary Forward ScalarHeight WitnessIndices FixedPreparation Concrete
noncomputable section

/-- The point of this condition is that all four pole inputs satisfy explicit
height-free arithmetic tests at one tuple. It asks for no elliptic twist points. -/
structure PreparedAt (w : NinePoints) (x η : ℚ) : Prop where
  guards : Guards w anchor
  scales : ∀ j, (pointScale w fixedMultiplier j)^2*η∉marks ∧
    (pointScale w fixedMultiplier j)^2*η≠3 ∧ pointScale w fixedMultiplier j≠0
  ordinary : ∀ j : Fin 3,
    let A := (pointScale w fixedMultiplier j)^2
    let t := A*η
    let T := ordinaryTraceAt w fixedMultiplier anchor (beta x) A t
    T≠0 ∧ Prepared (detector A t/T^2)
  scalar : let r:=scalarRadicand (beta x)
    let W:=scalarTree r (scalarEntries w fixedMultiplier)
    ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ W≠0 ∧ Prepared (signedValue r δ gamma denominator W)

/-- The prime-selection and local-preparation target on the nine common points. -/
def IntegerPreparation : Prop :=
  ∀ k : ℤ, ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, PreparedAt (nineAffine a).doubles (k:ℚ) η

theorem prepared_certificate (twists : SimultaneousTwists) {w x η} (h : PreparedAt w x η) :
    PointCertificate w fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers := by
  obtain ⟨q,hh,b,n,t,z⟩:=h.guards
  refine ⟨q,hh,b,(rational_chart_iff _).2 n,(rational_chart_iff _).2 t,(rational_chart_iff _).2 z,h.scales,?_,?_⟩
  · intro j
    obtain ⟨live,p⟩ := h.ordinary j
    exact ⟨live,pole_of_prepared twists p⟩
  · obtain ⟨δ,sgn,nz,p⟩:=h.scalar
    exact ⟨δ,sgn,nz,pole_of_prepared twists p⟩

theorem integral_fibre (twists : SimultaneousTwists) {k : ℤ} {a : Fin 9 → AffineInput} {η : ℚ}
    (prepared : PreparedAt (nineAffine a).doubles (k:ℚ) η) :
    ∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial (k:ℚ) w=0 :=
  (polynomial_iff_certificate _).2 ⟨a,η,prepared_certificate twists prepared⟩

theorem integral_of_root (units : FiveMarkUnits.PublishedCorollary72)
    (remaining : MinimalConductors.ExactLeastHeight) {x : ℚ}
    (h : ∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial x w=0) : ∃ k : ℤ, x=(k:ℚ) := by
  obtain ⟨a,η,points⟩ := (polynomial_iff_certificate x).1 h
  obtain ⟨k,e,_⟩ := fixed_witness_sound a x η (ShortFormal.ordinaryCharts oldCutoff K0)
    ((MinimalConductors.original_iff_exact_least units).2 remaining) points
  exact ⟨k,e⟩

theorem fixed_projection (units : FiveMarkUnits.PublishedCorollary72)
    (remaining : MinimalConductors.ExactLeastHeight)
    (preparation : IntegerPreparation) (twists : SimultaneousTwists) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial x w=0) ↔ ∃ k : ℤ, x=(k:ℚ) := by
  refine ⟨integral_of_root units remaining,?_⟩
  rintro ⟨k,rfl⟩
  obtain ⟨a,η,prepared⟩:=preparation k
  exact integral_fibre twists prepared

end
end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.prepared_certificate
#print axioms Sun28.PreparedPoles.integral_fibre
#print axioms Sun28.PreparedPoles.integral_of_root
#print axioms Sun28.PreparedPoles.fixed_projection
