import AbelOrbitEndpoint
import OpenPointEquality

/-! The affine formula for an automorphism of the actual signed curve extends
uniquely to the two points at infinity and to every geometric point. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open BinaryCover GeometricMarking NormalDescent MarkedForm WeightedCurvePoints
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev coordinateSupport {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p : FibrePoints u) :
    (paperCurve u).left := AffinePointAction.support (weightedEquiv_pullback hu p)

/-- Agreement on a nonempty open computes a relative morphism on the complete curve. -/
theorem curve_hom_ext_open {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (f g : paperCurve u ⟶ paperCurve u) (U : (paperCurve u).left.Opens)
    (hU : (U : Set (paperCurve u).left).Nonempty)
    (h : ∀ p : FibrePoints u, coordinateSupport hu p ∈ U →
      weightedEquiv_pullback hu p ≫ f = weightedEquiv_pullback hu p ≫ g) : f = g := by
  let := sourceIntegral hu
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : IsProper (paperCurve u).hom :=
    inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  apply AffinePointAction.ext_of_open_points f g U hU
  intro s hs
  obtain ⟨p,rfl⟩ := (weightedEquiv_pullback hu).surjective s
  exact h p hs

/-- A certified change of variables on one open determines the scheme automorphism
as well as the action of its coefficients on every weighted point. -/
theorem sign_and_action_of_open {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (e : paperCurve u ≅ paperCurve u) (t : Lift u (δ u))
    (U : (paperCurve u).left.Opens) (hU : (U : Set (paperCurve u).left).Nonempty)
    (h : ∀ p : FibrePoints u, coordinateSupport hu p ∈ U →
      weightedEquiv_pullback hu p ≫ e.hom = weightedEquiv_pullback hu (t.action p)) :
    (e = Iso.refl _ ∨ e = geometricDeck hu) ∧
      ∀ p : FibrePoints u, weightedEquiv_pullback hu p ≫ e.hom =
        weightedEquiv_pullback hu (t.action p) := by
  have hd : δ u ≠ 0 := by exact_mod_cast Nat.ne_of_gt (GlobalTwist.delta_pos u)
  rcases lift_action_sign hu hd t with ht | ht
  · have he : e.hom = 𝟙 _ := by
      apply curve_hom_ext_open hu _ _ U hU
      intro p hp
      simpa only [ht,Equiv.refl_apply,Category.comp_id] using h p hp
    refine ⟨Or.inl (Iso.ext he), ?_⟩
    intro p
    simp only [ht,Equiv.refl_apply,he,Category.comp_id]
  · have he : e.hom = (geometricDeck hu).hom := by
      apply curve_hom_ext_open hu _ _ U hU
      intro p hp
      simpa only [ht,weighted_deck hu] using h p hp
    refine ⟨Or.inr (Iso.ext he), ?_⟩
    intro p
    rw [he,ht,weighted_deck hu]

theorem weighted_action_of_open {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (e : paperCurve u ≅ paperCurve u) (t : Lift u (δ u))
    (U : (paperCurve u).left.Opens) (hU : (U : Set (paperCurve u).left).Nonempty)
    (h : ∀ p : FibrePoints u, coordinateSupport hu p ∈ U →
      weightedEquiv_pullback hu p ≫ e.hom = weightedEquiv_pullback hu (t.action p)) :
    ∀ p : FibrePoints u, weightedEquiv_pullback hu p ≫ e.hom =
        weightedEquiv_pullback hu (t.action p) :=
  (sign_and_action_of_open hu e t U hU h).2

/-- The coordinate hypothesis in the Torelli restriction can be checked on an
individual nonempty open for each automorphism and each chosen coefficient matrix. -/
def OpenCurveLifts {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Prop :=
  ∀ e : paperCurve u ≅ paperCurve u, ∃ (t : Lift u (δ u)) (U : (paperCurve u).left.Opens),
    (U : Set (paperCurve u).left).Nonempty ∧ ∀ p : FibrePoints u, coordinateSupport hu p ∈ U →
      weightedEquiv_pullback hu (t.action p) = weightedEquiv_pullback hu p ≫ e.hom

theorem curve_lifts_iff_open {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (∀ e : paperCurve u ≅ paperCurve u, ∃ t : Lift u (δ u), ∀ p : FibrePoints u,
      weightedEquiv_pullback hu (t.action p) = weightedEquiv_pullback hu p ≫ e.hom) ↔
      OpenCurveLifts hu := by
  constructor
  · intro h e
    obtain ⟨t,ht⟩ := h e
    exact ⟨t,⊤,⟨AffinePointAction.support (basepoint hu),Set.mem_univ _⟩,fun p _ => ht p⟩
  · intro h e
    obtain ⟨t,U,hU,ht⟩ := h e
    exact ⟨t,fun p => (weighted_action_of_open hu e t U hU (fun q hq => (ht q hq).symm) p).symm⟩

end
end ZInQBlueprint.SixAbelMap

#print axioms ZInQBlueprint.SixAbelMap.curve_hom_ext_open
#print axioms ZInQBlueprint.SixAbelMap.sign_and_action_of_open
#print axioms ZInQBlueprint.SixAbelMap.weighted_action_of_open
#print axioms ZInQBlueprint.SixAbelMap.curve_lifts_iff_open
