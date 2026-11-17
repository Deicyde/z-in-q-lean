import OpenWeightedAction

/-! The literal finite affine chart suffices for the coordinate formula of Voight, (43.3.3). -/
open CategoryTheory AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open BinaryCover GeometricMarking NormalDescent MarkedForm WeightedCurvePoints
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev finitePoint {u : ℚ} (q : Finite (paperForm u (δ u))) : FibrePoints u :=
  toWeighted _ (.inl q)

private abbrev finiteInclusion {u : ℚ} (hu : u ∉ ZInQ.contactSet) :=
  chartInclusion Qbar _ _ (paper_overlap Qbar u) false ≫ (baseChangeIso hu).hom

private theorem finite_open {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    IsOpenImmersion (finiteInclusion hu).left := by
  change IsOpenImmersion ((chartInclusion Qbar _ _ (paper_overlap Qbar u) false).left ≫ (baseChangeIso hu).hom.left)
  infer_instance

/-- The open of the complete model represented by normalized finite affine coordinates. -/
theorem finite_affine_open {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ U : (paperCurve u).left.Opens, (U : Set (paperCurve u).left).Nonempty ∧
      ∀ p : FibrePoints u, coordinateSupport hu p ∈ U ↔
        ∃ q : Finite (paperForm u (δ u)), finitePoint q = p := by
  let j : SpecOver (R := Qbar) (Cover (paper Qbar u false)) ⟶ paperCurve u := finiteInclusion hu
  let : IsOpenImmersion j.left := finite_open hu
  let U := j.left.opensRange
  have incl (q : Finite (paperForm u (δ u))) :
      weightedEquiv_pullback hu (finitePoint q) =
        affineSection Qbar (paper Qbar u false) ⟨q.1, by simpa only
          [paper_evaluate,Bool.false_eq_true,ite_false] using q.2⟩ ≫ j := by
    rw [weightedEquiv_pullback_apply]
    change weightedSections Qbar hu (toWeighted _ (.inl q)) ≫ _ = _
    rw [weighted_finite]
    exact Category.assoc _ _ _
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (paperForm u (δ u) (0,1)) (by decide : 0 < 2)
  let q0 : Finite (paperForm u (δ u)) := ⟨(0,y),hy⟩
  refine ⟨U,?_,?_⟩
  · refine ⟨coordinateSupport hu (finitePoint q0),?_⟩
    change _ ∈ Set.range j.left
    unfold coordinateSupport AffinePointAction.support
    rw [incl]
    exact ⟨_,rfl⟩
  intro p
  constructor
  · intro hp
    let s := weightedEquiv_pullback hu p
    have hr : Set.range s.left ⊆ Set.range j.left := by
      rintro _ ⟨x,rfl⟩
      have e : x = IsLocalRing.closedPoint Qbar := @Subsingleton.elim (PrimeSpectrum Qbar) inferInstance _ _
      rw [e]
      exact hp
    let k := IsOpenImmersion.lift j.left s.left hr
    have hk : k ≫ j.left = s.left := IsOpenImmersion.lift_fac _ _ _
    let m : basePoint ⟶ SpecOver (R := Qbar) (Cover (paper Qbar u false)) :=
      Over.homMk k (by rw [← j.w, ← Category.assoc,hk,s.w])
    obtain ⟨q,hq⟩ := (affineSection_bijective Qbar (paper Qbar u false)).surjective m
    let r : Finite (paperForm u (δ u)) := ⟨q.1,by
      simpa only [paper_evaluate,Bool.false_eq_true,ite_false] using q.2⟩
    refine ⟨r,(weightedEquiv_pullback hu).injective ?_⟩
    rw [incl]
    change affineSection Qbar _ q ≫ j = s
    rw [hq]
    exact Over.OverMorphism.ext hk
  · rintro ⟨q,rfl⟩
    change _ ∈ Set.range j.left
    unfold coordinateSupport AffinePointAction.support
    rw [incl]
    exact ⟨_,rfl⟩

theorem weighted_action_of_finite {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (e : paperCurve u ≅ paperCurve u) (t : Lift u (δ u))
    (h : ∀ q : Finite (paperForm u (δ u)), weightedEquiv_pullback hu (finitePoint q) ≫ e.hom =
      weightedEquiv_pullback hu (t.action (finitePoint q))) :
    ∀ p : FibrePoints u, weightedEquiv_pullback hu p ≫ e.hom = weightedEquiv_pullback hu (t.action p) := by
  obtain ⟨U,hU,hp⟩ := finite_affine_open hu
  apply weighted_action_of_open hu e t U hU
  intro p hpU
  obtain ⟨q,rfl⟩ := (hp p).mp hpU
  exact h q

/-- For a lift of this particular sextic the matrix has scalar projective action.
In particular the displayed denominator in the affine formula vanishes nowhere. -/
theorem denominator_ne {u : ℚ} (hu : u ∉ ZInQ.contactSet) (t : Lift u (δ u)) (x : Qbar) :
    (t.lin (x,1)).2 ≠ 0 := by
  obtain ⟨a,b,c,d,hm,hlin⟩ := base_matrix t.lin
  have hd : δ u ≠ 0 := by exact_mod_cast Nat.ne_of_gt (GlobalTwist.delta_pos u)
  have he (x z : Qbar) : paperForm u (δ u) (a*x+b*z,c*x+d*z) =
      (t.unitY : Qbar)^2*paperForm u (δ u) (x,z) := by rw [← hlin]; exact t.equation _
  obtain ⟨_,hc,ha,hn,_⟩ := paper_matrix_signs hu hd hm he
  simpa only [hlin,hc,zero_mul,zero_add,mul_one,← ha] using hn

/-- A finite output with the two normalized affine coordinate formulas has
the weighted class computed by the homogeneous lift. -/
theorem finite_lift_formula {u : ℚ} (hu : u ∉ ZInQ.contactSet) (t : Lift u (δ u))
    (q r : Finite (paperForm u (δ u)))
    (hx : r.1.1 = (t.lin (q.1.1,1)).1 / (t.lin (q.1.1,1)).2)
    (hy : r.1.2 = (t.unitY : Qbar)*q.1.2 / (t.lin (q.1.1,1)).2^3) :
    t.action (finitePoint q) = finitePoint r := by
  obtain ⟨v,hv,hb,hyv⟩ := CurveChart.coordinateEquiv_coordinates t.lin t.unitY t.equation
    (finiteRep (paperForm u (δ u)) q)
  change CurveChart.coordinateEquiv _ _ _ (Quotient.mk _ (finiteRep _ q)) = Quotient.mk _ (finiteRep _ r)
  rw [hv]
  apply Quotient.sound
  let d := (t.lin (q.1.1,1)).2
  have hd : d ≠ 0 := denominator_ne hu t _
  refine ⟨(Units.mk0 d hd)⁻¹,?_,?_⟩
  · apply Prod.ext
    · change r.1.1 = _ * v.base.1
      rw [hb,hx]
      change _ / d = d⁻¹ * _
      rw [div_eq_inv_mul]
      rfl
    · change (1 : Qbar) = _ * v.base.2
      rw [hb]
      change 1 = d⁻¹*d
      rw [inv_mul_cancel₀ hd]
  · change r.1.2 = _ * v.y
    rw [hy,hyv]
    change _ / d^3 = (d⁻¹)^3 * _
    rw [div_eq_inv_mul,inv_pow]
    rfl

/-- A literal affine formula on the smooth model suffices to recover the complete action.
Here the target pair is read in normalized affine coordinates. -/
theorem weighted_action_of_voight {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (e : paperCurve u ≅ paperCurve u) (t : Lift u (δ u))
    (h : ∀ q : Finite (paperForm u (δ u)), ∃ r : Finite (paperForm u (δ u)),
      weightedEquiv_pullback hu (finitePoint q) ≫ e.hom = weightedEquiv_pullback hu (finitePoint r) ∧
      r.1.1 = (t.lin (q.1.1,1)).1 / (t.lin (q.1.1,1)).2 ∧
      r.1.2 = (t.unitY : Qbar)*q.1.2 / (t.lin (q.1.1,1)).2^3) :
    ∀ p : FibrePoints u, weightedEquiv_pullback hu (t.action p) = weightedEquiv_pullback hu p ≫ e.hom := by
  intro p
  symm
  apply weighted_action_of_finite hu e t _ p
  intro q
  obtain ⟨r,he,hx,hy⟩ := h q
  rw [finite_lift_formula hu t q r hx hy]
  exact he

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.finite_affine_open
#print axioms ZInQBlueprint.SixAbelMap.weighted_action_of_finite
#print axioms ZInQBlueprint.SixAbelMap.denominator_ne
#print axioms ZInQBlueprint.SixAbelMap.finite_lift_formula
#print axioms ZInQBlueprint.SixAbelMap.weighted_action_of_voight
