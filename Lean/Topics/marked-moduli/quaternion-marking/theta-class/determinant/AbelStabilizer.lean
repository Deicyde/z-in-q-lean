import SignedCartier

/-! No nonzero translation carries the genus-two Abel curve into itself.
A point of the stabilizer would take every effective degree-one divisor
class to another such class. The Riemann–Roch stabilizer criterion forces
the translating divisor to be principal. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open SixAbelMap CanonicalTheta QuaternionMarking GeometricMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]

theorem abel_stabilizer_zero {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
    {hc : i.hom ≫ C.hom = M.toBase} {V : AbelianModel.GroupScheme K} {b : base K ⟶ C}
    (A : AbelPresentation C M i hc V b) (genus : genusFF K F = 2) (t : Additive (base K ⟶ V.X))
    (stable : ∀ x ∈ Set.range A.abel, x + t ∈ Set.range A.abel) : t = 0 := by
  let B := pointPlace C M i hc b
  let S : Divisor K F := Finsupp.single B 1
  have ds : S.degree = 1 := by
    rw [show S = Finsupp.single B 1 from rfl,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]
    norm_num
  obtain ⟨T,hT⟩ := Pic0.mk_surjective (A.divisorEquiv.symm t)
  have h : A.divisorEquiv (Pic0.mk T) = t := (congrArg A.divisorEquiv hT).trans (A.divisorEquiv.apply_symm_apply _)
  let : Nonempty (Place K F) := ⟨B⟩
  obtain ⟨Kc,g,rr⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  obtain rfl : g=2 := (CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M rr).trans genus
  have principal : (T : Divisor K F) ∈ Divisor.principal := by
    apply Divisor.mem_principal_of_forall_ell_pos_add Kc 2 rr _ T.2
    intro D hd pos
    let D₀ : Divisor.degZero (K:=K) (F:=F) := ⟨D-S,by
      change (D-S).degree = 0
      rw [map_sub,hd,ds];norm_num⟩
    have hz : A.divisorEquiv (Pic0.mk D₀) ∈ Set.range A.abel := by
      apply (presentation_W_one A D₀).mp
      change 0 < ell ((D-S)+S)
      simpa only [sub_add_cancel] using pos
    have ht := stable _ hz
    rw [←h,←map_add,←Pic0.mk_add] at ht
    have positive := (presentation_W_one A (D₀+T)).mpr ht
    change 0 < ell (((D-S)+(T : Divisor K F))+S) at positive
    rwa [show (D-S+(T : Divisor K F))+S = D+T by abel] at positive
  have zero : Pic0.mk T = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr principal)
  rw [←h,zero,map_zero]

theorem signed_abel_stabilizer_zero {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (t : JacobianPoints hu) (stable : ∀ x ∈ Set.range (rigidDivisors hu).abel,
      x+t ∈ Set.range (rigidDivisors hu).abel) : t = 0 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let := paper_essentially_finite hu
  let A := rigidPresentation hu
  have image : Set.range (rigidDivisors hu).abel = Set.range A.abel := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨WeightedCurvePoints.weightedEquiv_pullback hu p,rfl⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨q,rfl⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective p
      exact ⟨q,rfl⟩
  rw [image] at stable
  exact abel_stabilizer_zero A (paper_functionField_genus hu) t stable

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.abel_stabilizer_zero
#print axioms ZInQBlueprint.ThetaClass.signed_abel_stabilizer_zero
