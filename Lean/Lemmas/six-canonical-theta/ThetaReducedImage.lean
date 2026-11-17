import SignedCanonicalTheta
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! The reduced zero scheme of a theta section is the scheme-theoretic Abel image. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap BinaryCover NormalDescent GeometricMarking QuaternionMarking
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A quasi-compact morphism from a reduced scheme has a radical image ideal. -/
theorem radical_image_ideal {C X : Scheme} [IsReduced C] (m : C ⟶ X) [QuasiCompact m] :
    m.ker.radical = m.ker := by
  ext U : 2
  change (m.ker.ideal U).radical = m.ker.ideal U
  rw [Scheme.Hom.ker_apply]
  apply Ideal.radical_eq_iff.mpr
  rintro a ⟨n,hn⟩
  exact RingHom.mem_ker.mpr (IsNilpotent.eq_zero ⟨n,by simpa only [←map_pow] using (RingHom.mem_ker.mp hn)⟩)

/-- Over an algebraically closed field, equality on rational points identifies the
radical of the section ideal with the ideal of the scheme-theoretic image. -/
theorem radical_eq_image_of_pointwise {K : Type} [Field K] [IsAlgClosed K]
    {C X : Over (Spec (.of K))} [IsReduced C.left] [LocallyOfFiniteType C.hom] [LocallyOfFiniteType X.hom]
    (m : C ⟶ X) [QuasiCompact m.left] {L : X.left.Modules} (hL : L.IsInvertible) (s : 𝟙_ _ ⟶ L)
    (hs : ∀ x : base K ⟶ X, Scheme.Modules.pullbackSection x.left s = 0 ↔ ∃ p : base K ⟶ C, p ≫ m = x) :
    (Scheme.Modules.zeroSchemeIdeal s).radical = m.left.ker := by
  let I := Scheme.Modules.zeroSchemeIdeal s
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  let o := IsLocalRing.closedPoint K
  have lhs : (I.support : Set X.left) ⊆ closure (Set.range m.left) := by
    rw [←closure_inter_closedPoints I.support.isClosed]
    apply closure_minimal _ isClosed_closure
    rintro x ⟨hx,hc⟩
    let p : base K ⟶ X := Over.homMk (pointOfClosedPoint X.hom x hc) (pointOfClosedPoint_comp _ _ _)
    have pe : p.left o = x := pointOfClosedPoint_apply _ _ _ _
    have zero : Scheme.Modules.pullbackSection p.left s = 0 :=
      (hL.pullbackSection_eq_zero_iff_mem_support s p.left).mpr (pe.symm ▸ hx)
    obtain ⟨q,hq⟩ := (hs p).mp zero
    exact subset_closure ⟨q.left o,(congrArg (fun z : base K ⟶ X => z.left o) hq).trans pe⟩
  have pre : IsClosed (m.left ⁻¹' (I.support : Set X.left)) := I.support.isClosed.preimage m.left.continuous
  have kernel : closedPoints C.left ⊆ m.left ⁻¹' (I.support : Set X.left) := by
    intro x hc
    let p : base K ⟶ C := Over.homMk (pointOfClosedPoint C.hom x hc) (pointOfClosedPoint_comp _ _ _)
    have pe : p.left o = x := pointOfClosedPoint_apply _ _ _ _
    have hz := (hL.pullbackSection_eq_zero_iff_mem_support s (p ≫ m).left).mp
      ((hs (p ≫ m)).mpr ⟨p,rfl⟩)
    change m.left (p.left o) ∈ (I.support : Set X.left) at hz
    simpa only [pe,Set.mem_preimage] using hz
  have all := closure_minimal kernel pre
  rw [closure_closedPoints] at all
  have rhs : closure (Set.range m.left) ⊆ (I.support : Set X.left) := by
    apply closure_minimal _ I.support.isClosed
    rintro _ ⟨x,rfl⟩
    exact all (Set.mem_univ x)
  have same : I.support = m.left.ker.support := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker]
    exact Set.Subset.antisymm lhs rhs
  calc
    _ = Scheme.IdealSheafData.vanishingIdeal I.support := Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal m.left.ker.support := congrArg _ same
    _ = _ := Scheme.IdealSheafData.vanishingIdeal_support.trans (radical_image_ideal m.left)

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- The kernel is the actual Abel map's scheme-theoretic image, with no assumption
of closed immersion, formal unramifiedness, or reducedness for the theta divisor. -/
theorem signedThetaSection_reduced_ideal :
    (Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).radical = (rigidMorphism hu).left.ker := by
  let := sourceIntegral hu
  let := paper_proper ℚ u
  let : IsProper (paperCurve u).hom := inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let J := (geometricJacobian hu).X
  let : IsProper (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).proper
  let : IsProper J.hom := inferInstanceAs (IsProper (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let m := rigidMorphism hu
  let : IsProper (m.left ≫ J.hom) := by rw [Over.w]; infer_instance
  let : IsProper m.left := IsProper.of_comp m.left J.hom
  apply radical_eq_image_of_pointwise m (signedThetaLine_invertible hu)
  intro x
  have eq := (Set.ext_iff.mp (signedThetaSection_zeros hu) (Additive.ofMul x))
  change Scheme.Modules.pullbackSection x.left (signedThetaSection hu) = 0 ↔ _ at eq
  rw [eq]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨WeightedCurvePoints.weightedEquiv_pullback hu y,congrArg Additive.toMul ((rigid_on_points hu y).symm.trans hy)⟩
  · rintro ⟨p,hp⟩
    obtain ⟨y,hy⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective p
    exact ⟨y,(rigid_on_points hu y).trans (congrArg Additive.ofMul ((congrArg (· ≫ m) hy).trans hp))⟩

end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.radical_image_ideal
#print axioms ZInQBlueprint.CanonicalTheta.radical_eq_image_of_pointwise
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaSection_reduced_ideal
