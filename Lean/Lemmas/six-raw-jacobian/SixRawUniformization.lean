import SixRawJacobian

/-! Apply the complex Jacobian statement of Baba–Granath, Corollary 3.15,
to the three modular coefficients in the published equation. -/
open CategoryTheory AlgebraicGeometry
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.ShimuraAtlas
open AbelianModel BinaryCover NormalDescent QuaternionLift
noncomputable section

/-- The group-scheme consequence of the isomorphism of principally
polarized complex surfaces in Corollary 3.15, restricted to regular sextics. -/
def RawCorollary315 (A B D : UpperHalfPlane → ℂ) (surface : UpperHalfPlane → GroupScheme ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, let f := rawPolynomial (A τ) (B τ) (D τ)
    ∀ (hd : f.natDegree = 6), f.Separable →
      ∀ [IsProper (sexticCompletion f hd).hom]
        [SmoothOfRelativeDimension 1 (sexticCompletion f hd).hom]
        [GeometricallyIrreducible (sexticCompletion f hd).hom],
        Nonempty (surface τ ≅ groupScheme ℂ (sexticCompletion f hd).hom)

/-- All comparisons involving the rational parameter, its conic lift and
the normalized algebraic sextic follow from the literal modular equation. -/
def canonicalPeriods_of_raw {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} {ι : Qbar →+* ℂ} {hom : HomBaseChange ι}
    (e l : Qbar) (he : e^2 = -6) (hl : l^2 = 2)
    (A Y Z : UpperHalfPlane → ℂ) (surface : UpperHalfPlane → GroupScheme ℂ)
    (covers : ∀ p : ConicPoint, ∃ τ : UpperHalfPlane, LiesAbove ι (A τ) (Y τ) (Z τ) p)
    (representative : ∀ (j : ℚ), OutsideCM j → ∀ p : ConicPoint, p.y^2 = 9*(j:Qbar) →
      ∃ w : PeriodRepresentative C chart ι hom p, ∀ τ : UpperHalfPlane,
        LiesAbove ι (A τ) (Y τ) (Z τ) p → Nonempty ((baseChange ι).obj w.surface ≅ surface τ))
    (cor : RawCorollary315 A (fun τ => ι e * Y τ) (fun τ => 2 * ι l * Z τ) surface) :
    CanonicalPeriods C chart ι hom where
  e := e
  l := l
  e_square := he
  l_square := hl
  A := A
  Y := Y
  Z := Z
  surface := surface
  covers := covers
  representative := representative
  cor315 := by
    intro u hu p hp τ above
    obtain ⟨hd,hs,proper,smooth,irreducible,⟨g⟩⟩ := raw_jacobian hu hp he hl ι above
    obtain ⟨letter⟩ := @cor τ hd hs proper smooth irreducible
    exact ⟨letter ≪≫ g.symm⟩

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.canonicalPeriods_of_raw
