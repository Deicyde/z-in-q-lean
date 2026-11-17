import PaperWeightedPoints
import SexticDeckPoints

/-! The geometric equivalence intertwines the literal scheme involution with
the sign action on weighted triples. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover CurveChart MarkedForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [CharZero K]

def negateFinite {G : K × K → K} (q : Finite G) : Finite G :=
  ⟨(q.1.1,-q.1.2),by simpa using q.2⟩

def negateInfinity {G : K × K → K} (q : Infinity G) : Infinity G :=
  ⟨-q.1,by simpa using q.2⟩

omit [CharZero K] in
theorem negY_normal (G : K×K→K) (q : Normal G) :
    negY G (toWeighted G q) = toWeighted G (q.map negateFinite negateInfinity) := by
  have formula (z : K × K) : G ((LinearEquiv.refl K _) z) = ((-1:Kˣ):K)^2*G z := by simp
  have solve (a b : CurveChart.Rep G) (hb : b.base=a.base) (hy : b.y = -a.y) :
      negY G (Quotient.mk _ a) = Quotient.mk _ b := by
    obtain ⟨v,hv,hvb,hvy⟩ := CurveChart.coordinateEquiv_coordinates (LinearEquiv.refl K _) (-1:Kˣ) formula a
    change CurveChart.coordinateEquiv _ _ _ _ = _
    rw [hv]
    apply congrArg (Quotient.mk _)
    apply CurveChart.Rep.ext
    · exact hvb.trans hb.symm
    · simpa [hy] using hvy
  cases q with
  | inl q => exact solve _ _ rfl rfl
  | inr q => exact solve _ _ rfl rfl

abbrev paperDeck (u : ℚ) : paperModel K u ≅ paperModel K u := deckOver _ _ (paper_overlap K u)

theorem equiv_deck {u : ℚ} (hu : u∉ZInQ.contactSet) (p : Points (F K u)) :
    weightedSections K hu (negY _ p) = weightedSections K hu p ≫ (paperDeck u).hom := by
  obtain ⟨a,rfl⟩ := toWeighted_surjective _ (paper_homogeneous K hu) p
  rw [negY_normal]
  cases a with
  | inl a =>
    change weightedSections K hu (toWeighted _ (.inl (negateFinite a))) = _
    rw [weighted_finite (K:=K) hu (negateFinite a),weighted_finite (K:=K) hu a]
    let v : AffineCoords K (paper K u false) := ⟨a.1, by simpa only [paper_evaluate,Bool.false_eq_true,ite_false] using a.2⟩
    exact (chart_deck (paper K u false) (paper K u true) (paper_overlap K u) false v).symm
  | inr a =>
    change weightedSections K hu (toWeighted _ (.inr (negateInfinity a))) = _
    rw [weighted_infinity (K:=K) hu (negateInfinity a),weighted_infinity (K:=K) hu a]
    let v : AffineCoords K (paper K u true) := infinityCoord _ ⟨a.1, by simpa only [paper_evaluate,ite_true] using a.2⟩
    exact (chart_deck (paper K u false) (paper K u true) (paper_overlap K u) true v).symm

theorem infinity_value_ne {u : ℚ} (hu : u∉ZInQ.contactSet) : F K u (1,0) ≠ 0 := by
  have hd : (GlobalTwist.delta u : K) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  rw [F,paper_formula hu]
  simpa [IntegralSextic.form,IntegralSextic.alpha,IntegralSextic.beta,IntegralSextic.gamma] using
    (paperScale_ne hu hd)

theorem infinity_not_fixed {u : ℚ} (hu : u∉ZInQ.contactSet) (y : Infinity (F K u)) :
    weightedSections K hu (toWeighted _ (.inr y)) ≫ (paperDeck u).hom ≠
      weightedSections K hu (toWeighted _ (.inr y)) := by
  rw [weighted_infinity]
  intro h
  have hy : y.1=0 := (chart_fixed_iff _ _ (paper_overlap K u) true _).1 h
  exact infinity_value_ne hu (by rw [← y.2,hy]; simp)

end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.negY_normal
#print axioms ZInQBlueprint.WeightedCurvePoints.equiv_deck
#print axioms ZInQBlueprint.WeightedCurvePoints.infinity_value_ne
#print axioms ZInQBlueprint.WeightedCurvePoints.infinity_not_fixed
