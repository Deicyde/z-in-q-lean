import ThetaPicardModel
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.TranslateThetaBundleTensorIso
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.ThetaBundleTensorPointDifferenceTensorPullbackIso

/-! Translating the pointed determinant by the actual class of P-b. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.DeterminantAutoduality
open SixAbelMap CanonicalTheta AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable {C : Over (Spec (.of K))} [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] {b : base K ⟶ C} {V : GroupScheme K}
  {e : V ≅ groupScheme K C.hom} {m : C ⟶ V.X}
variable (P : Pointed b e m)

/-- Normalization is recorded by the actual universal rigidified sheaf. -/
def evaluationLine (p : base K ⟶ C) : V.X.left.Modules :=
  (Scheme.Modules.pullback P.toRepresenting.hom.left).obj
    ((Scheme.Modules.pullback (rigSection C.hom P.J.toBase (schemePoint p))).obj P.represents.poincare.L)

omit [IsAlgClosed K] in
theorem evaluationLine_invertible (p : base K ⟶ C) : (evaluationLine P p).IsInvertible :=
  (P.represents.poincare.isInvertible.pullback _).pullback _

omit [IsAlgClosed K] in
theorem representing_mul {T : Over (Spec (.of K))} (x y : T ⟶ V.X) :
    letI := PGroup C (schemePoint b) P.represents
    (x*y) ≫ P.toRepresenting.hom = (x ≫ P.toRepresenting.hom)*(y ≫ P.toRepresenting.hom) := by
  let := PGroup C (schemePoint b) P.represents
  let g := e.hom.hom.hom.hom
  let ε := schemePoint b
  let z := (presentation K C.hom).pointedComparisonOver ε P.represents
  change (x*y) ≫ (g ≫ z.hom) = (x ≫ (g ≫ z.hom))*(y ≫ (g ≫ z.hom))
  simp only [← Category.assoc,MonObj.mul_comp]
  apply (overHomEquivSchemeHomOver T P.J.toBase).injective
  have hm := pointedComparison_mul C.hom ε P.represents T.hom
    (overHomEquivSchemeHomOver T _ (x ≫ g)) (overHomEquivSchemeHomOver T _ (y ≫ g))
  have hi := (groupLaw K C.hom).overHomEquivSchemeHomOver_mul T (x ≫ g) (y ≫ g)
  exact (congrArg (pointedComparisonPoint C.hom ε P.represents T.hom) hi).trans hm

variable (M : CurveModel K F) (i : M.C ≅ C.left) (hi : i.hom ≫ C.hom = M.toBase)
  (hgF : genusFF K F = 2)

set_option linter.unusedSectionVars false in
include M i hi hgF in
/-- On the representing Picard scheme, the translated determinant times the
Poincaré evaluation at p is the unshifted determinant. -/
theorem representing_point_formula (p : base K ⟶ C) :
    letI := PGroup C (schemePoint b) P.represents
    let JB := Over.mk P.J.toBase
    let q := p ≫ Over.homMk P.aj.1 P.aj.2
    let tr := 𝟙 JB * (CartesianMonoidalCategory.toUnit JB ≫ q)
    let L := thetaBundle C.hom (schemePoint b) P.J.toBase P.represents.poincare 4 3
    Nonempty ((Scheme.Modules.pullback tr.left).obj L ⊗
      (Scheme.Modules.pullback (rigSection C.hom P.J.toBase (schemePoint p))).obj P.represents.poincare.L ≅ L) := by
  let := PGroup C (schemePoint b) P.represents
  let ε := schemePoint b
  let h := P.represents
  let J := P.J
  let S := Spec (.of K)
  let JB := Over.mk J.toBase
  let q : base K ⟶ JB := p ≫ Over.homMk P.aj.1 P.aj.2
  let U := h.poincare
  let tJ : SchemeHomOver J.toBase (𝟙 S) := ⟨J.toBase,Category.comp_id _⟩
  let cst := CartesianMonoidalCategory.toUnit JB ≫ q
  let tr := 𝟙 JB * cst
  let ov (f : JB ⟶ JB) : SchemeHomOver J.toBase J.toBase := ⟨f.left,f.w⟩
  let N := U.pullbackAlong (schemePoint q)
  let z := (presentation K C.hom).pointedComparisonOver ε h
  let zs := (Over.forget _).mapIso z
  let : IsIso z.inv.left := inferInstanceAs (IsIso zs.inv)
  let : IsProper (toBase K C.hom) := proper K C.hom
  have hz : z.inv.left ≫ (toBase K C.hom) = J.toBase := z.inv.w
  let : IsProper J.toBase := by rw [←hz]; infer_instance
  have aux : ∀ m₀ : ℕ, ∃ A : SmoothProperCurve.FiniteMapData C.hom ε, m₀ ≤ A.m := by
    intro m₀
    obtain ⟨A,hm,-⟩ := SmoothProperCurve.exists_finiteMapData_le_isUnit K C.hom ε m₀
    exact ⟨A,hm⟩
  have hg : ∀ (E : Type) [Field E] [Algebra K E] (M' : CurveModel K E) (k : M'.C ≅ C.left)
      (_ : k.hom ≫ C.hom = M'.toBase) (Kc : Divisor K E) (g : ℕ),
      (∀ D : Divisor K E, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) → g = 2 := by
    intro E _ _ M' k hk Kc g rr
    have back : i.inv ≫ M.toBase = C.hom := (congrArg (i.inv ≫ ·) hi).symm.trans (i.inv_hom_id_assoc _)
    have iso := JacobianVarieties.Picard.Proofs.CotangentGenus.P2mTJ.algEquivOfIso M' M (k ≪≫ i.symm)
      (show (k.hom ≫ i.inv) ≫ M.toBase = M'.toBase by rw [Category.assoc,back,hk])
    exact (CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M' rr).trans ((genusFF_eq_of_algEquiv iso).trans hgF)
  obtain ⟨A,-⟩ := aux 0
  have hgeo := SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed K C.hom ε A 2 hg
  have hf := subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    K C.hom ε 2 hgeo U h.poincare_mem 4 (by decide)
  have idU : (U.pullbackAlong (ov (𝟙 JB))).L ≅ U.L :=
    (Scheme.Modules.pullbackCongr (baseChangeSnd_id C.hom J.toBase)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _
  have htu : (CartesianMonoidalCategory.toUnit JB).left = J.toBase := Over.toUnit_left
  have adj : (N.pullbackAlong tJ).L ≅ (U.pullbackAlong (ov cst)).L :=
    (Scheme.Modules.pullbackComp (baseChangeSnd C.hom tJ) (baseChangeSnd C.hom (schemePoint q))).app _ ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp C.hom (schemePoint q) tJ)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (congrArg (baseChangeSnd C.hom)
      (show postComp (schemePoint q) tJ = ov cst from Subtype.ext (congrArg (· ≫ q.left) htu).symm))).app _
  let h' : RepresentsRelSubPic C.hom ε (algEquivZeroGroupCut C.hom ε).toSubPicCondition J := h
  have mulU : (U.tensor (N.pullbackAlong tJ)).L ≅ (U.pullbackAlong (ov tr)).L :=
    (idU.symm ⊗ᵢ adj) ≪≫ (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h' (𝟙 JB) cst).some.symm
  obtain ⟨E⟩ := nonempty_pullback_thetaBundle_iso K C.hom ε aux U 4 3 hf (ov tr) (U.tensor (N.pullbackAlong tJ)) mulU
  let b' : SchemeHomOver (𝟙 S) C.hom := ⟨𝟙 _ ≫ ε.1,by simp [ε,S]⟩
  have eb : b' = ε := Subtype.ext (Category.id_comp _)
  obtain ⟨eN⟩ := P.classifies.2 K (𝟙 _) (schemePoint p)
  change N.L ≅ pointSubBasepointModule (a:=C.hom) (schemePoint p) b' at eN
  rw [eb] at eN
  obtain ⟨c⟩ := nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
    K C.hom ε aux 2 hgeo U h.poincare_mem (schemePoint p) N (h.poincare_mem.pullback _) eN 4 (by decide)
  exact ⟨(E ⊗ᵢ Iso.refl _) ≪≫ c⟩

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.evaluationLine_invertible
#print axioms ZInQBlueprint.DeterminantAutoduality.representing_mul
#print axioms ZInQBlueprint.DeterminantAutoduality.representing_point_formula
