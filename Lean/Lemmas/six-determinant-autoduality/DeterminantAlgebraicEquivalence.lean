import SignedAutoduality

/-! Algebraic equivalence of every Poincaré evaluation, witnessed by the original curve. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantAutoduality
open SixAbelMap CanonicalTheta AbelianModel GeometricMarking QuaternionMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- Swap the factors of C×J. Along the constant point the family restricts to its rigidification. -/
private def sliceIso {k : Type} [Field k] {X C : Scheme} (x : X ⟶ Spec (.of k)) (c : C ⟶ Spec (.of k))
    (L : (pullback c x).Modules) (p : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    (Scheme.Modules.pullback (baseChangeSnd x p)).obj
      ((Scheme.Modules.pullback (pullbackSymmetry x c).hom).obj L) ≅
    (Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj ((Scheme.Modules.pullback (rigSection c x p)).obj L) := by
  have w : baseChangeSnd x p ≫ (pullbackSymmetry x c).hom =
      pullback.fst x (𝟙 _) ≫ rigSection c x p := by
    apply pullback.hom_ext
    · simp only [Category.assoc,pullbackSymmetry_hom_comp_fst,baseChangeSnd,rigSection,
        pullback.map,pullback.lift_snd,pullback.lift_fst]
      rw [←Category.assoc,pullback.condition,Category.comp_id]
    · simp only [Category.assoc,pullbackSymmetry_hom_comp_snd,baseChangeSnd,rigSection,
        pullback.map,pullback.lift_fst,pullback.lift_snd,Category.comp_id]
  exact (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr w).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

variable {K : Type} [Field K] {C : Over (Spec (.of K))} [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] {b : base K ⟶ C} {V : GroupScheme K}
  {e : V ≅ JacobianVarieties.Picard.Unpointed.groupScheme K C.hom} {m : C ⟶ V.X}
theorem evaluation_algebraically_trivial (P : Pointed b e m) (p : base K ⟶ C) :
    IsAlgEquivZero V.X.hom (evaluationLine P p) := by
  apply IsAlgEquivZero.pullback P.toRepresenting.hom.left P.toRepresenting.hom.w
  let x := P.J.toBase
  let L := P.represents.poincare
  let D := (Scheme.Modules.pullback (pullbackSymmetry x C.hom).hom).obj L.L
  refine ⟨C.left,C.hom,inferInstance,inferInstance,D,L.isInvertible.pullback _,
    schemePoint b,schemePoint p,⟨?_⟩,⟨sliceIso x C.hom L.L (schemePoint p)⟩⟩
  exact sliceIso x C.hom L.L (schemePoint b) ≪≫
    (Scheme.Modules.pullback _).mapIso L.rigidified.some ≪≫ Scheme.Modules.pullbackUnitIso _

/-- Algebraically trivial actual invertible modules form a subgroup of the Picard group. -/
def picardZero {k : Type} [Field k] {X : Scheme} (x : X ⟶ Spec (.of k)) :
    AddSubgroup (Additive (PicUnits X)) where
  carrier := {c | ∃ (L : X.Modules) (hL : L.IsInvertible), IsAlgEquivZero x L ∧ c = Additive.ofMul (lineClass L hL)}
  zero_mem' := by
    obtain ⟨N,hN,hn,⟨iso⟩⟩ := ThetaClass.SameClass.refl x (𝟙_ X.Modules)
    refine ⟨N,hN,hn,?_⟩
    change (1 : PicUnits X) = lineClass N hN
    apply Units.ext
    rw [Units.val_one,lineClass_val,Skeleton.one_eq]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨iso.symm ≪≫ λ_ N⟩
  add_mem' := by
    rintro _ _ ⟨L,hL,h,rfl⟩ ⟨M,hM,k,rfl⟩
    exact ⟨L ⊗ M,hL.tensor hM,h.tensor k,congrArg Additive.ofMul (lineClass_tensor hL hM).symm⟩
  neg_mem' := by
    rintro _ ⟨L,hL,h,rfl⟩
    obtain ⟨N,hN,⟨z⟩⟩ := hL.exists_tensor_inverse
    refine ⟨N,hN,h.of_tensor_iso_unit z,?_⟩
    change (lineClass L hL)⁻¹ = lineClass N hN
    apply inv_eq_iff_mul_eq_one.mpr
    apply Units.ext
    rw [Units.val_one,Units.val_mul,lineClass_val,lineClass_val,←Skeleton.toSkeleton_tensorObj,Skeleton.one_eq]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨z⟩

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

theorem signed_evaluation_algZero (p : FibrePoints u) :
    IsAlgEquivZero (geometricJacobian hu).X.hom (signedEvaluation hu p) := by
  let := paperProper u
  let := paperIntegral hu
  let := paperSmooth hu
  exact evaluation_algebraically_trivial (signedPointed hu) (WeightedCurvePoints.weightedEquiv_pullback hu p)

theorem signed_image_in_picardZero :
    (signedPolarization hu).range ≤ picardZero (geometricJacobian hu).X.hom := by
  rw [range_eq_poincare]
  apply (AddSubgroup.closure_le _).mpr
  rintro _ ⟨p,rfl⟩
  exact ⟨_,signedEvaluation_invertible hu p,signed_evaluation_algZero hu p,rfl⟩

theorem signed_principal_iff_picardZero :
    ThetaClass.PrincipalTranslations (A:=geometricJacobian hu) (signedThetaLine hu) ↔
      picardZero (geometricJacobian hu).X.hom = AddSubgroup.closure (Set.range (evaluationClass hu)) := by
  rw [signed_principal_iff]
  constructor
  · intro h
    refine le_antisymm ?_ ((range_eq_poincare hu) ▸ signed_image_in_picardZero hu)
    rintro _ ⟨N,hN,hn,rfl⟩
    exact h N hN hn
  · intro eqn N hN hn
    rw [←eqn]
    exact ⟨N,hN,hn,rfl⟩

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.evaluation_algebraically_trivial
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_evaluation_algZero
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_image_in_picardZero
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_principal_iff_picardZero
