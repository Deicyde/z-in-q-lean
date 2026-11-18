import PicardPolynomial
import PaperCohomology

/-! The reciprocal charts of an arbitrary separable sextic over a number
field give two Laurent coordinates on its first Čech group. This computes
the geometric genus and the relative dimension of its unpointed Jacobian. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian GoodReductionJacobian
open ZInQBlueprint.BinaryCover ZInQBlueprint.BinaryCover.Cech ZInQBlueprint.SexticEmbedding
open ZInQBlueprint.AbelianModel
open ZOverQ.Qualitative.PicardDescent ZOverQ.Qualitative.PicardLocalization
open ZOverQ.Qualitative.PicardConjugation ZOverQ.Qualitative.PicardPolynomial
open ZInQ ZInQ.QualitativeHeight

namespace ZOverQ.Qualitative.PicardSurfaceDimension
noncomputable section
attribute [local instance] filteredCommGrpHasColimitsOfShape
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K]

private def twoCharts (f g : K[X]) (h : SexticOverlap K f g) :
    (gluedOver K f g h).left.TwoAffineOpenCover where
  U0 := atlasOpen K f g h (some false)
  U1 := atlasOpen K f g h (some true)
  isAffineOpen_U0 := @isAffineOpen_opensRange _ _ (inferInstanceAs (IsAffine (Spec (.of (Cover f))))) _ inferInstance
  isAffineOpen_U1 := @isAffineOpen_opensRange _ _ (inferInstanceAs (IsAffine (Spec (.of (Cover g))))) _ inferInstance
  sup_eq_top := atlas_union K f g h
  isAffineOpen_inf := (atlas_intersection K f g h) ▸
    @isAffineOpen_opensRange _ _ (inferInstanceAs (IsAffine (Spec (.of (Punctured K f))))) _
      (inferInstanceAs (IsOpenImmersion (atlasMap K f g h none)))

private def difference {X : Scheme.{0}} (U V W : X.Opens) (i : W ≤ U) (j : W ≤ V) :
    Γ(X,U) × Γ(X,V) →+ Γ(X,W) :=
  (((X.presheaf.map (homOfLE i).op).hom.toAddMonoidHom).comp (AddMonoidHom.fst _ _)) -
  (((X.presheaf.map (homOfLE j).op).hom.toAddMonoidHom).comp (AddMonoidHom.snd _ _))

private def signedCokernel {X : Scheme.{0}} (c : X ⟶ Spec (.of K)) (v : X.TwoAffineOpenCover)
    (W : X.Opens) (h : W=v.U0 ⊓ v.U1) :
    (v.structureSheafSections c).H1 ≃+
      Γ(X,W) ⧸ (difference v.U0 v.U1 W (h ▸ inf_le_left) (h ▸ inf_le_right)).range := by
  subst W
  let D := difference v.U0 v.U1 (v.U0 ⊓ v.U1) inf_le_left inf_le_right
  let S := v.structureSheafSections c
  have rev (a : Γ(X,v.U0)) (b : Γ(X,v.U1)) : S.cechDiff (a,b) = -D (a,b) := by
    rw [TwoChartCech.Sections.cechDiff_apply]
    change (1 : Γ(X,v.U0 ⊓ v.U1)) * _ - _ = -(_ - _)
    rw [one_mul, neg_sub]
    rfl
  apply QuotientAddGroup.congr _ _ (AddEquiv.refl Γ(X,v.U0 ⊓ v.U1))
  ext z
  constructor
  · rintro ⟨_,⟨⟨a,b⟩,rfl⟩,rfl⟩
    exact ⟨-(a,b), (map_neg D (a,b)).trans (rev a b).symm⟩
  · rintro ⟨⟨a,b⟩,rfl⟩
    refine ⟨_,⟨-(a,b),rfl⟩,?_⟩
    change S.cechDiff (-(a,b)) = D (a,b)
    rw [map_neg,rev,neg_neg]

variable [NumberField K]

/-- An additive identification with the two residual Laurent coefficients
already detects the dimension over a number field by restriction of scalars. -/
theorem finrank_of_addEquiv {W : Type} [AddCommGroup W] [Module K W]
    (coordinates : W ≃+ K × K) : Module.finrank K W = 2 := by
  let : Module ℚ W := Module.compHom W (algebraMap ℚ K)
  let : IsScalarTower ℚ K W := ⟨fun q k w => by
    rw [Algebra.smul_def q k]
    exact mul_smul (algebraMap ℚ K q) k w⟩
  let E : W ≃ₗ[ℚ] K × K := { coordinates with map_smul' := map_rat_smul coordinates }
  have h := E.finrank_eq
  rw [← Module.finrank_mul_finrank ℚ K W, Module.finrank_prod] at h
  have eqn : Module.finrank ℚ K * Module.finrank K W = Module.finrank ℚ K * 2 := by
    simpa only [Nat.mul_two] using h
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := K)) eqn

/-- The Čech group of the actual affine overlap has dimension two for every
ordinary binary sextic. The two residues are the coefficients of X⁻¹ and X⁻². -/
theorem chart_finrank (f g : K[X]) (h : SexticOverlap K f g) :
    Module.finrank K (((twoCharts f g h).structureSheafSections (gluedOver K f g h).hom).H1) = 2 := by
  let E := signedCokernel (gluedOver K f g h).hom (twoCharts f g h) _ (atlas_intersection K f g h)
  exact finrank_of_addEquiv (E.trans ((coordinateQuotient K h).trans (quotientEquiv K h).toAddEquiv))

private theorem regularCompletion {f : K[X]} (d : f.natDegree = 6) (s : f.Separable) :
    let D := sexticCompletion f d
    IsProper D.hom ∧ SmoothOfRelativeDimension 1 D.hom ∧ GeometricallyIntegral D.hom := by
  let D := sexticCompletion f d
  let X := Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))
  obtain ⟨hI,hP,hS,hDim,_⟩ := sexticCompletion_geometry d s
  let : AlgebraicGeometry.IsIntegral D.left := hI
  let : Smooth D.hom := hS
  let e : D ≅ X := (completion_is_quadrics d s).exists.choose
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  refine ⟨hP,ZInQBlueprint.SixJacobian.relative_dimension_one D.hom hDim,?_⟩
  rw [← e.hom.w, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
  exact geometric_integral_quadrics f d s

/-- Every smooth sextic completion over a number field has geometric genus two. -/
theorem geometricGenus_two (f : K[X]) (d : f.natDegree = 6) (s : f.Separable) :
    letI := (regularCompletion d s).2.2
    SmoothProperCurve.geometricGenus K (sexticCompletion f d).hom = 2 := by
  let D := sexticCompletion f d
  let : IsProper D.hom := (regularCompletion d s).1
  let : SmoothOfRelativeDimension 1 D.hom := (regularCompletion d s).2.1
  let : GeometricallyIntegral D.hom := (regularCompletion d s).2.2
  let h := reverse_sextic_overlap d
  rw [← SmoothProperCurve.finrank_H1_eq_geometricGenus K D.hom (twoCharts f f.reverse h)]
  exact chart_finrank f f.reverse h

/-- The dimension belongs to the actual group scheme of the proper completion. -/
theorem completionJacobian_dimension_two (f : K[X]) (d : f.natDegree = 6) (s : f.Separable) :
    SmoothOfRelativeDimension 2 (completionJacobian f d s).X.hom := by
  let D := sexticCompletion f d
  let : IsProper D.hom := (regularCompletion d s).1
  let : SmoothOfRelativeDimension 1 D.hom := (regularCompletion d s).2.1
  let : GeometricallyIntegral D.hom := (regularCompletion d s).2.2
  rw [← geometricGenus_two f d s]
  exact JacobianVarieties.Picard.Unpointed.smoothOfRelativeDimension K D.hom

/-- Every nonsingular Picard sextic gives an abelian surface. -/
theorem jacobian_dimension_two (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    SmoothOfRelativeDimension 2 (jacobian u v hu hv hD).X.hom := by
  let f := PicardLocal.sextic u v
  let d := fibre_degree u v hv
  let s := PicardLocal.good_fibre_separable (by norm_num : (2:K) ≠ 0) (by norm_num : (3:K) ≠ 0) hu hv hD
  let D := sexticCompletion f d
  let C := Over.mk (projectiveStructure (Picard.coefficients u v))
  let : IsProper D.hom := (regularCompletion d s).1
  let : SmoothOfRelativeDimension 1 D.hom := (regularCompletion d s).2.1
  let : GeometricallyIntegral D.hom := (regularCompletion d s).2.2
  let : IsProper C.hom := proper_projectiveStructure _
  let e : D ≅ C := completionIso u v hu hv hD
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  have sq : IsPullback e.inv.left C.hom D.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩
  let : SmoothOfRelativeDimension 1 C.hom := MorphismProperty.of_isPullback
    (P := @SmoothOfRelativeDimension 1) sq (regularCompletion d s).2.1
  let : GeometricallyIntegral C.hom := MorphismProperty.of_isPullback
    (P := @GeometricallyIntegral) sq (regularCompletion d s).2.2
  let sh := (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of K))) CommGrpCat.{1}).mapIso
    (ZInQBlueprint.IntegralPicard.CurveMap.pullIso e)
  let j : jacobian u v hu hv hD ≅ completionJacobian f d s :=
    (JacobianVarieties.Picard.Unpointed.sheafGroupSchemeIso K C.hom).symm ≪≫
    SchemeTheory.RepresentedGroups.iso
      (ordinaryRelativePicardZeroGroupSheaf C.hom).obj (ordinaryRelativePicardZeroGroupSheaf D.hom).obj
      (JacobianVarieties.Picard.Unpointed.groupSheafRepresentation K C.hom)
      (JacobianVarieties.Picard.Unpointed.groupSheafRepresentation K D.hom)
      ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of K))) CommGrpCat.{1}).mapIso sh) ≪≫
    JacobianVarieties.Picard.Unpointed.sheafGroupSchemeIso K D.hom
  let i := (CommGrp.forget _).mapIso j
  let : IsIso i.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso i).hom))
  have pull : IsPullback i.hom.left (jacobian u v hu hv hD).X.hom (completionJacobian f d s).X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨i.hom.w.trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 2) pull (completionJacobian_dimension_two f d s)

theorem familyJacobian_dimension_two (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (σ : fixedField ≃ₐ[ℚ] fixedField) :
    SmoothOfRelativeDimension 2 (familyJacobian t d ht hd σ).X.hom := by
  unfold familyJacobian
  apply jacobian_dimension_two

theorem twistedJacobian_dimension_two (t : ℚ) (ht : t ∉ contactSet) :
    SmoothOfRelativeDimension 2 (twistedJacobian t ht).X.hom := by
  unfold twistedJacobian
  apply familyJacobian_dimension_two

/-- Dimension two survives every field embedding, including embeddings into a
finite unramified local field or an algebraic closure. -/
theorem baseChange_dimension_two {L : Type} [Field L] (φ : fixedField →+* L)
    (t : ℚ) (ht : t ∉ contactSet) :
    SmoothOfRelativeDimension 2 ((baseChange φ).obj (twistedJacobian t ht)).X.hom := by
  let : SmoothOfRelativeDimension 2 (twistedJacobian t ht).X.hom := twistedJacobian_dimension_two t ht
  exact inferInstanceAs (SmoothOfRelativeDimension 2 (pullback.snd (twistedJacobian t ht).X.hom
    (Spec.map (CommRingCat.ofHom φ))))

end
end ZOverQ.Qualitative.PicardSurfaceDimension

#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.finrank_of_addEquiv
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.chart_finrank
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.geometricGenus_two
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.completionJacobian_dimension_two
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.jacobian_dimension_two
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.familyJacobian_dimension_two
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.twistedJacobian_dimension_two
#print axioms ZOverQ.Qualitative.PicardSurfaceDimension.baseChange_dimension_two
