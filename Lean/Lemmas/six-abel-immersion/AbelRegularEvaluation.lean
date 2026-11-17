import AbelCanonicalPencil
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.FiniteFinrankRegularDifferentialsEqGenus

/-! The order-zero differential furnished by the canonical pencil has nonzero residue coefficient. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped KaehlerDifferential ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
noncomputable section
open BinaryCover GeometricMarking NormalDescent
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteFinrankRegular.AlgebraicCurve.RegularDifferentialsFinrank
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- A regular differential with nonzero coefficient in the residue field of the chosen point. -/
theorem exists_regular_evaluation (hg : 0 < genusFF K F) (P : Place K F) :
    ∃ η : Ω[F⁄K], η ∈ regularDifferentials K F ∧
      P.ordDifferential η = 0 ∧ P.evalAt (P.differentialCoeff η) ≠ 0 := by
  classical
  let : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  let : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let : Nontrivial Ω[F⁄K] := Module.nontrivial_of_finrank_eq_succ (IsCurveOver.finrank_kaehler (K:=K) (F:=F))
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  let D := canonicalDivisorOf hω
  let S := Finsupp.single P (1 : ℤ)
  have hs : LSpace (D-S) ≤ LSpace D := by
    apply lSpace_mono
    exact sub_le_self _ (by intro v; simp only [S, Finsupp.zero_apply,Finsupp.single_apply]; split_ifs <;> norm_num)
  obtain ⟨hD,hDS⟩ := canonical_point_dimensions hg P hω
  have hnle : ¬ LSpace D ≤ LSpace (D-S) := by
    intro h
    have heq := le_antisymm h hs
    have he : ell D = ell (D-S) := congrArg (fun V : Submodule K F => Module.finrank K V) heq
    change ell D = _ at hD
    change ell (D-S) + 1 = _ at hDS
    omega
  obtain ⟨f,hf,hf'⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hf0 : f ≠ 0 := fun h => hf' (h ▸ (Submodule.zero_mem (LSpace (D-S))))
  have good := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  have hval : P.ord f + D P = 0 := by
    have lower := good P
    by_contra hn
    apply hf'
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    by_cases hv : v = P
    · subst v
      simp only [Finsupp.sub_apply, S, Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.sub_apply, S, Finsupp.single_eq_of_ne hv, sub_zero]
      exact good v
  have order : P.ordDifferential (f • ω) = 0 := by
    rw [P.ordDifferential_smul hf0 (differentialCoeff_ne_zero hω P)]
    exact (congrArg (P.ord f + ·) (canonicalDivisorOf_apply hω P)).symm.trans hval
  let := IsCurveOver.finite_residueField P
  have hrat : P.IsRational := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=P.ResidueField)).2
  refine ⟨f • ω,(smul_mem_regularDifferentials_iff hω f).mpr hf,order,?_⟩
  exact P.evalAt_ne_zero hrat (differentialCoeff_ne_zero (smul_ne_zero hf0 hω) P) order

/-- Every geometric place of the actual signed sextic has a regular differential
whose residue coefficient in a local generator is nonzero. -/
theorem paper_regular_evaluation {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let F : Type := (paperCurve u).left.functionField
    ∀ P : Place Qbar F, ∃ η : Ω[F⁄Qbar], η ∈ regularDifferentials Qbar F ∧
      P.ordDifferential η = 0 ∧ P.evalAt (P.differentialCoeff η) ≠ 0 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let := paper_essentially_finite hu
  let F : Type := (paperCurve u).left.functionField
  change ∀ P : Place Qbar F, _
  intro P
  exact exists_regular_evaluation (by rw [paper_functionField_genus hu]; decide) P

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.exists_regular_evaluation
#print axioms ZInQBlueprint.SixAbelMap.paper_regular_evaluation
