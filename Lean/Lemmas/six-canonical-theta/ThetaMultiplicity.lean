import SignedCanonicalTheta
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.EllAddEqOrd

/-! The degree-one input to the Riemann singularity formula at every Abel point. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap GeometricMarking NormalDescent
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- For a genus-positive curve a degree-one divisor has Riemann–Roch dimension zero
or one. Dimension one means that it is linearly equivalent to a single point. -/
theorem one_section_at_abel (hg : 0 < genusFF K F) (D : Divisor K F) (hd : D.degree = 1) :
    ell D = 1 ↔ ∃ P : Place K F, Divisor.IsPrincipal (Finsupp.single P 1 - D) := by
  constructor
  · intro h
    exact (degree_one_ell D hd).mp (by rw [h];decide)
  · rintro ⟨P,f,hf,ord⟩
    have h := ell_add_of_forall_eq_ord D hf ord
    rw [add_sub_cancel] at h
    obtain ⟨t,ht,hfin,-⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F)
    have hc := ell_zero_eq_one_of_constantsAreBase (constantsAreBase_of_isAlgClosed_of_transcendental t ht)
    rw [←h]
    change Module.finrank K (LSpace (Finsupp.single P 1)) = 1
    rw [lSpace_point_eq_constants hg P]
    exact hc

/-- The section dimension in the classical singularity formula is exactly one on W₁. -/
theorem signed_degree_one_dimension {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    ∀ (D : Divisor Qbar (paperCurve u).left.functionField), D.degree = 1 → 0 < ell D → ell D = 1 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let := paper_essentially_finite hu
  intro D hd h
  apply (one_section_at_abel (by rw [paper_functionField_genus hu]; decide) D hd).mpr
  exact (degree_one_ell D hd).mp h
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.one_section_at_abel
#print axioms ZInQBlueprint.CanonicalTheta.signed_degree_one_dimension
