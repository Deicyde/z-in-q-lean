import SixThetaRestriction

/-! Restriction for any specified geometric Abel morphism and divisor presentation. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixThetaRestriction
open GeometricMarking MarkedForm WeightedCurvePoints SixAbelMap QuaternionMarking NormalDescent GoodReductionJacobian
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet) (D : DivisorData hu)
  (m : paperCurve u ⟶ (geometricJacobian hu).X)
  (hm : ∀ p, D.abel p = Additive.ofMul (weightedEquiv_pullback hu p ≫ m))

include hm

private theorem presentation_image (a : geometricJacobian hu ≅ geometricJacobian hu)
    (t : JacobianPoints hu) (h :
      (groupAction a) '' Set.range (D.abel) = Set.range (fun p => D.abel p+t)) :
    ThetaSubcurve.pointImage (m ≫ (underlyingIso a).hom) =
      ThetaSubcurve.pointImage (m ≫ (translation t).hom) := by
  let c := weightedEquiv_pullback hu
  have hleft (p : FibrePoints u) :
      Additive.ofMul (c p ≫ m ≫ (underlyingIso a).hom) =
        groupAction a (D.abel p) := by
    rw [hm]
    change c p ≫ (m ≫ (underlyingIso a).hom) = (c p ≫ m) ≫ (underlyingIso a).hom
    exact (Category.assoc _ _ _).symm
  have hright (p : FibrePoints u) :
      Additive.ofMul (c p ≫ m ≫ (translation t).hom) = D.abel p+t := by
    rw [←Category.assoc]
    rw [hm]
    exact translate_point (Additive.ofMul (c p ≫ m)) t
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    obtain ⟨v,rfl⟩ := c.surjective p
    have he : groupAction a (D.abel v) ∈ Set.range (fun q => D.abel q+t) :=
      h ▸ ⟨_,⟨v,rfl⟩,rfl⟩
    obtain ⟨w,hw⟩ := he
    exact ⟨c w,(hright w).trans (hw.trans (hleft v).symm)⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨w,rfl⟩ := c.surjective p
    have he : D.abel w+t ∈ (groupAction a) '' Set.range (D.abel) :=
      h.symm ▸ ⟨w,rfl⟩
    obtain ⟨_,⟨v,rfl⟩,hv⟩ := he
    exact ⟨c v,(hleft v).trans (hv.trans (hright w).symm)⟩

/-- An automorphism preserving the family of translates restricts, after one translation,
to an actual scheme automorphism of the marked genus-two curve. -/
theorem restrict_presentation (closed : IsClosedImmersion m.left)
    (a : geometricJacobian hu ≅ geometricJacobian hu)
    (ha : preservesTheta D a) :
    ∃ (t : JacobianPoints hu) (z : paperCurve u ≅ paperCurve u),
      z.hom ≫ m ≫ (translation t).hom = m ≫ (underlyingIso a).hom := by
  let := sourceIntegral hu
  let : IsProper (paperCurve u).hom := by
    let := BinaryCover.paper_proper ℚ u
    exact inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (BinaryCover.paperModel ℚ u).hom
      (BinaryCover.scalarMap ℚ Qbar)))
  let := closed
  obtain ⟨t,ht⟩ := exists_translate D a ha
  let i := m
  let j := i ≫ (translation t).hom
  let : IsClosedImmersion j.left := by
    change IsClosedImmersion (i.left ≫ (translation t).hom.left)
    let : IsIso (translation t).hom.left :=
      inferInstanceAs (IsIso (((Over.forget _).mapIso (translation t)).hom))
    infer_instance
  obtain ⟨z,hz,_⟩ := ThetaSubcurve.iso_of_pointImage i j (underlyingIso a) (presentation_image hu D m hm a t ht)
  exact ⟨t,z,hz⟩

/-- The curve and its coordinates are the only geometric inputs in the genus-two restriction argument. -/
theorem polarizedTorelli_of_presentation (closed : IsClosedImmersion m.left)
    (coords : CurveLifts hu) :
    PolarizedTorelli D (preservesTheta D) := by
  intro a ha
  obtain ⟨t,z,hz⟩ := restrict_presentation hu D m hm closed a ha
  obtain ⟨l,hl⟩ := coords z
  refine ⟨l,?_⟩
  have mappt (p : FibrePoints u) : groupAction a (D.abel p) = D.abel (l.action p) + t := by
    let c := weightedEquiv_pullback hu
    calc
      groupAction a (D.abel p) = Additive.ofMul (c p ≫ m ≫ (underlyingIso a).hom) := by
        rw [hm]
        change (c p ≫ m) ≫ (underlyingIso a).hom = c p ≫ (m ≫ (underlyingIso a).hom)
        exact Category.assoc _ _ _
      _ = Additive.ofMul (c p ≫ z.hom ≫ m ≫ (translation t).hom) := by rw [hz]
      _ = Additive.ofMul ((c (l.action p) ≫ m) ≫ (translation t).hom) := by
        change c p ≫ z.hom ≫ m ≫ (translation t).hom =
          (c (l.action p) ≫ m) ≫ (translation t).hom
        rw [Category.assoc,hl,Category.assoc]
      _ = D.abel (l.action p) + t := by
        rw [hm]
        exact translate_point (Additive.ofMul (c (l.action p) ≫ m)) t
  intro p q
  rw [map_sub,mappt,mappt]
  abel

end
end ZInQBlueprint.SixThetaRestriction
#print axioms ZInQBlueprint.SixThetaRestriction.restrict_presentation
#print axioms ZInQBlueprint.SixThetaRestriction.polarizedTorelli_of_presentation
