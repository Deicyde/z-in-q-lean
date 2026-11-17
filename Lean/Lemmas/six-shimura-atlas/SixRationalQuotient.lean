import SixConicInvariant

/-! A rational morphism from the ordinary R₃ quotient chart to a coarse
moduli scheme. Its base-field naturality and w₃ invariance follow.
The classifier has no reference to conic coordinates or to w₃. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent
noncomputable section

/-- A coarse interpretation on geometric points of a scheme over ℚ.
Here naturality is needed only for automorphisms of the algebraic closure. -/
structure CoarseInterpretation (M : Over (Spec (.of ℚ))) where
  read : (geometricDomain ⟶ M) → ModuliClass
  natural : ∀ (σ : Gal) (x : geometricDomain ⟶ M),
    read (galoisPoint σ ≫ x) = conjugateModuli σ (read x)

def shimuraClassMap {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : ShimuraClassMap where
  value p := C.read (linePoint p.quotientCoordinate ≫ chart)
  rational σ p := by
    rw [coordinate_conjugate, ← linePoint_conjugate, Category.assoc]
    exact C.natural σ _
  forget_w3 p := by rw [(deck_coordinate p).2]

theorem class_on_conic {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (p : ConicPoint) :
    (shimuraClassMap C chart).value p =
      C.read (specHom (conicAlgebraPoint p) ≫ quotientMorphism ≫ chart) := by
  rw [←Category.assoc,quotient_on_point]
  rfl

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.shimuraClassMap
#print axioms ZInQBlueprint.ShimuraAtlas.class_on_conic
