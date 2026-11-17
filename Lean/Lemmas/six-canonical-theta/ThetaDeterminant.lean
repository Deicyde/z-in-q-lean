import ThetaClassifying
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.ThetaSectionNeZeroStabilizerTrivial
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.InvertibleThetaBundle
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapDataLeIsUnit
import Nyll.JacobianVarieties.Picard.Deformation.CurveModelFinrankCotangentSpaceZeroSectionEqGenusFF

/-! The determinant of cohomology, for the point-divisor normalization, cuts out W₁ on geometric points. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve GoodReductionJacobian NeronModelInfra MonoidalCategory
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
  [Algebra.EssFiniteType K F]
variable (C : Over (Spec (.of K))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] (b : base K ⟶ C)
variable {J : RelativePic0Designation K C.hom}
  (h : RepresentsRelSubPic C.hom (schemePoint b) (algEquivZeroCut C.hom (schemePoint b)) J)
  (aj : SchemeHomOver C.hom J.toBase)

/-- The theta section belongs to the invertible determinant bundle for the universal line
bundle twisted by 4b; its vanishing is the degree-one Brill–Noether condition. -/
theorem exists_designated_theta (M : CurveModel K F) (e : M.C ≅ C.left) (he : e.hom ≫ C.hom = M.toBase)
    (hgF : genusFF K F = 2) (hsm : Smooth J.toBase) (hpr : IsProper J.toBase)
    (H : IsPointedAbel C (schemePoint b) J h aj) :
    let L := thetaBundle C.hom (schemePoint b) J.toBase h.poincare 4 3
    Scheme.Modules.IsInvertible L ∧ ∃ θ : 𝟙_ J.P.Modules ⟶ L, θ ≠ 0 ∧
      ∀ x : base K ⟶ Over.mk J.toBase, Scheme.Modules.pullbackSection x.left θ = 0 ↔
        ∃ p : base K ⟶ C, p.left ≫ aj.1 = x.left := by
  let ε := schemePoint b
  let := hsm
  let := hpr
  have hg : ∀ (E : Type) [Field E] [Algebra K E] (N : CurveModel K E) (k : N.C ≅ C.left)
      (_ : k.hom ≫ C.hom = N.toBase) (Kc : Divisor K E) (g : ℕ),
      (∀ D : Divisor K E, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) → g = 2 := by
    intro E _ _ N k hk Kc g rr
    have back : e.inv ≫ M.toBase = C.hom := (congrArg (e.inv ≫ ·) he).symm.trans (e.inv_hom_id_assoc _)
    have iso := JacobianVarieties.Picard.Proofs.CotangentGenus.P2mTJ.algEquivOfIso N M (k ≪≫ e.symm)
      (show (k.hom ≫ e.inv) ≫ M.toBase = N.toBase by rw [Category.assoc,back,hk])
    exact (CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq N rr).trans
      ((genusFF_eq_of_algEquiv iso).trans hgF)
  have aux : ∀ m : ℕ, ∃ A : SmoothProperCurve.FiniteMapData C.hom ε, m ≤ A.m := by
    intro m
    obtain ⟨A,hm,-⟩ := SmoothProperCurve.exists_finiteMapData_le_isUnit K C.hom ε m
    exact ⟨A,hm⟩
  obtain ⟨A,-⟩ := aux 0
  have hg' := SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed
    K C.hom ε A 2 hg
  have hf := subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    K C.hom ε 2 hg' h.poincare h.poincare_mem 4 (by decide)
  obtain ⟨θ,hθ⟩ := exists_pullbackSection_thetaBundle_poincare_eq_zero_iff
    K C.hom ε aux J h hsm hpr 2 hg (by decide) 4 (by decide)
  refine ⟨isInvertible_thetaBundle K C.hom ε aux h.poincare 4 3 hf, θ, ?_,
    fun x => (hθ x).trans (H0_iff_abel C b h aj M e he H x)⟩
  let B : {p : Spec (.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
    ⟨ε.1 ≫ e.inv, by rw [←he,Category.assoc,e.inv_hom_id_assoc];exact ε.2⟩
  have hB : B.1 ≫ e.hom = ε.1 := by change (ε.1 ≫ e.inv) ≫ e.hom = _; simp
  let v := M.pointEquivPlace B
  let : Nonempty (Place K F) := ⟨v⟩
  let := (show RepresentsRelSubPic C.hom ε (algEquivZeroGroupCut C.hom ε).toSubPicCondition J from h).grpObj
  obtain ⟨pts,-,dict⟩ := exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos K C.hom ε J h M e he B hB
  obtain ⟨Kc,g,rr⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  obtain rfl : g = 2 := hg F M e he Kc g rr
  obtain ⟨D,degD,hzero⟩ := RROpens.exists_degree_eq_sub_one_and_ell_eq_zero Kc 2 rr
  let S := Finsupp.single v (1:ℤ)
  have degS : Divisor.degree S = 1 := by
    rw [show S = Finsupp.single v (1:ℤ) from rfl,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed v];norm_num
  let Dv : Divisor.degZero (K:=K) (F:=F) := ⟨D-S,by
    change Divisor.degree (D-S) = 0
    rw [map_sub,degD,degS];norm_num⟩
  intro hz
  have van : Scheme.Modules.pullbackSection (pts (Pic0.mk Dv)).left θ = 0 := by
    rw [hz];exact JacobianVarieties.Picard.Proofs.ThetaStabilizer.StabJacSol.pullbackSection_zero _ _
  have pos := (dict Dv 1).mp ((hθ _).mp van)
  change 0 < ell ((D-S)+S) at pos
  rw [sub_add_cancel,hzero] at pos
  exact lt_irrefl _ pos
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.exists_designated_theta
