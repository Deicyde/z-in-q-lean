import ThetaTranslation
import AbelOrbitGeometry
import ThetaSubcurve

/-! Restriction to the genus-two Abel curve replaces strong Torelli on a stabilizer of its translates. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixThetaRestriction
open GeometricMarking MarkedForm WeightedCurvePoints SixAbelMap QuaternionMarking NormalDescent GoodReductionJacobian
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- The underlying Abel morphism is the one classifying the literal point differences. -/
def abelMorphism : paperCurve u ⟶ (geometricJacobian hu).X :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  letI := (signedModel hu).curve
  (realization hu).morphism

/-- Every isomorphism of the actual complete curve acts in the indicated weighted coordinates. -/
def CurveLifts : Prop :=
  ∀ e : paperCurve u ≅ paperCurve u, ∃ t : Lift u (δ u), ∀ p : FibrePoints u,
    weightedEquiv_pullback hu (t.action p) = weightedEquiv_pullback hu p ≫ e.hom

abbrev underlyingIso {A B : AbelianModel.GroupScheme Qbar} (a : A ≅ B) : A.X ≅ B.X where
  hom := a.hom.hom.hom.hom
  inv := a.inv.hom.hom.hom
  hom_inv_id := congrArg (fun m : A ⟶ A => m.hom.hom.hom) a.hom_inv_id
  inv_hom_id := congrArg (fun m : B ⟶ B => m.hom.hom.hom) a.inv_hom_id

private theorem translate_image (a : geometricJacobian hu ≅ geometricJacobian hu)
    (t : JacobianPoints hu) (h :
      (groupAction a) '' Set.range (weightedAbel hu) = Set.range (fun p => weightedAbel hu p+t)) :
    ThetaSubcurve.pointImage (abelMorphism hu ≫ (underlyingIso a).hom) =
      ThetaSubcurve.pointImage (abelMorphism hu ≫ (translation t).hom) := by
  let c := weightedEquiv_pullback hu
  have hleft (p : FibrePoints u) :
      Additive.ofMul (c p ≫ abelMorphism hu ≫ (underlyingIso a).hom) =
        groupAction a (weightedAbel hu p) := by
    change c p ≫ (abelMorphism hu ≫ (underlyingIso a).hom) = (c p ≫ abelMorphism hu) ≫ (underlyingIso a).hom
    exact (Category.assoc _ _ _).symm
  have hright (p : FibrePoints u) :
      Additive.ofMul (c p ≫ abelMorphism hu ≫ (translation t).hom) = weightedAbel hu p+t := by
    rw [←Category.assoc]
    exact translate_point (weightedAbel hu p) t
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    obtain ⟨v,rfl⟩ := c.surjective p
    have he : groupAction a (weightedAbel hu v) ∈ Set.range (fun q => weightedAbel hu q+t) :=
      h ▸ ⟨_,⟨v,rfl⟩,rfl⟩
    obtain ⟨w,hw⟩ := he
    exact ⟨c w,(hright w).trans (hw.trans (hleft v).symm)⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨w,rfl⟩ := c.surjective p
    have he : weightedAbel hu w+t ∈ (groupAction a) '' Set.range (weightedAbel hu) :=
      h.symm ▸ ⟨w,rfl⟩
    obtain ⟨_,⟨v,rfl⟩,hv⟩ := he
    exact ⟨c v,(hleft v).trans (hv.trans (hright w).symm)⟩

/-- An automorphism preserving the family of translates restricts, after one translation,
to an actual scheme automorphism of the marked genus-two curve. -/
theorem restrict_theta (closed : IsClosedImmersion (abelMorphism hu).left)
    (a : geometricJacobian hu ≅ geometricJacobian hu)
    (ha : preservesTheta (divisorData hu) a) :
    ∃ (t : JacobianPoints hu) (z : paperCurve u ≅ paperCurve u),
      z.hom ≫ abelMorphism hu ≫ (translation t).hom = abelMorphism hu ≫ (underlyingIso a).hom := by
  let := sourceIntegral hu
  let : IsProper (paperCurve u).hom := by
    let := BinaryCover.paper_proper ℚ u
    exact inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (BinaryCover.paperModel ℚ u).hom
      (BinaryCover.scalarMap ℚ Qbar)))
  let := closed
  obtain ⟨t,ht⟩ := exists_translate (divisorData hu) a ha
  let i := abelMorphism hu
  let j := i ≫ (translation t).hom
  let : IsClosedImmersion j.left := by
    change IsClosedImmersion (i.left ≫ (translation t).hom.left)
    let : IsIso (translation t).hom.left :=
      inferInstanceAs (IsIso (((Over.forget _).mapIso (translation t)).hom))
    infer_instance
  obtain ⟨z,hz,_⟩ := ThetaSubcurve.iso_of_pointImage i j (underlyingIso a) (translate_image hu a t ht)
  exact ⟨t,z,hz⟩

/-- The curve and its coordinates are the only geometric inputs in the genus-two restriction argument. -/
theorem polarizedTorelli_of_abel_closed (closed : IsClosedImmersion (abelMorphism hu).left)
    (coords : CurveLifts hu) :
    PolarizedTorelli (divisorData hu) (preservesTheta (divisorData hu)) := by
  intro a ha
  obtain ⟨t,z,hz⟩ := restrict_theta hu closed a ha
  obtain ⟨l,hl⟩ := coords z
  refine ⟨l,?_⟩
  have mappt (p : FibrePoints u) : groupAction a (weightedAbel hu p) = weightedAbel hu (l.action p) + t := by
    let c := weightedEquiv_pullback hu
    calc
      groupAction a (weightedAbel hu p) = Additive.ofMul (c p ≫ abelMorphism hu ≫ (underlyingIso a).hom) := by
        change (c p ≫ abelMorphism hu) ≫ (underlyingIso a).hom = c p ≫ (abelMorphism hu ≫ (underlyingIso a).hom)
        exact Category.assoc _ _ _
      _ = Additive.ofMul (c p ≫ z.hom ≫ abelMorphism hu ≫ (translation t).hom) := by rw [hz]
      _ = Additive.ofMul ((c (l.action p) ≫ abelMorphism hu) ≫ (translation t).hom) := by
        change c p ≫ z.hom ≫ abelMorphism hu ≫ (translation t).hom =
          (c (l.action p) ≫ abelMorphism hu) ≫ (translation t).hom
        rw [Category.assoc,hl,Category.assoc]
      _ = weightedAbel hu (l.action p) + t := translate_point (weightedAbel hu (l.action p)) t
  intro p q
  change groupAction a (weightedAbel hu p-weightedAbel hu q) = weightedAbel hu (l.action p)-weightedAbel hu (l.action q)
  rw [map_sub,mappt,mappt]
  abel

end
end ZInQBlueprint.SixThetaRestriction
#print axioms ZInQBlueprint.SixThetaRestriction.abelMorphism
#print axioms ZInQBlueprint.SixThetaRestriction.restrict_theta
#print axioms ZInQBlueprint.SixThetaRestriction.polarizedTorelli_of_abel_closed
