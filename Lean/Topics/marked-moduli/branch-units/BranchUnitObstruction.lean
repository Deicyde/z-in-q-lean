import RationalBranchHeight
import Mathlib.NumberTheory.Padics.PadicNorm

/-! Local arithmetic of the invariant of ten projective branch coordinates. -/
open Polynomial
namespace ZInQBlueprint.BranchHeight
namespace UnitObstruction
open SexticThetaHeight
noncomputable section

/-- If the invariant has absolute value less than one and the constant is a unit,
at least one branch coordinate has absolute value different from one. -/
theorem nonunit_of_invariant {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {j c : K} (hc : v c = 1) (hj : v j < 1) (b : Fin 10 → K)
    (he : j^2*(∑ i, b i)^10 = c^2*∏ i, b i) : ∃ i, v (b i) ≠ 1 := by
  by_contra! h
  have hs : v (∑ i, b i) ≤ 1 := (hv.apply_sum_univ_le (l := b)).trans (ciSup_le fun i => (h i).le)
  have eq := congrArg v he
  simp only [map_mul,map_pow,map_prod,h,hc,one_pow,Finset.prod_const_one,mul_one] at eq
  have hpow : v j ^ 2 < 1 := by simpa using pow_lt_pow_left₀ hj (v.nonneg j) (by decide : 2 ≠ 0)
  have hp : v (∑ i, b i)^10 ≤ 1 := pow_le_one₀ (v.nonneg _) hs
  exact (lt_of_le_of_lt (mul_le_of_le_one_right (sq_nonneg _) hp) hpow).ne eq


/-- The restriction of an absolute value above p to the rational numbers. Positive powers
allow the standard changes of normalization. -/
def LiesOver {K : Type*} [Field K] [CharZero K] (p : ℕ) (v : AbsoluteValue K ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ q : ℚ, v (q:K) = (padicNorm p q : ℝ)^t

theorem paper_nonunit_of_valuations {p : ℕ} [hprime : Fact p.Prime] {u δ : ℚ}
    (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) (hjval : 0 < padicValRat p (SixContact.J u))
    (hcval : padicValRat p (3779136:ℚ)=0) {r : Fin 6 → ℂ} (hr : Function.Injective r)
    (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (v : AbsoluteValue (weightField r) ℝ) (hv : IsNonarchimedean v) (hplace : LiesOver p v) :
    ∃ i, v (weights r i) ≠ 1 := by
  rcases hplace with ⟨t,ht,h⟩
  have hJQ := (CoarseConic.unmarked_range hu).2.ne
  have hcnorm : (padicNorm p (3779136:ℚ) : ℝ) = 1 := by
    rw [padicNorm.eq_zpow_of_nonzero (by norm_num),hcval]
    norm_num
  have hjnorm : (padicNorm p (SixContact.J u) : ℝ) < 1 := by
    rw [padicNorm.eq_zpow_of_nonzero hJQ]
    exact_mod_cast zpow_lt_one_of_neg₀ (a:=(p:ℚ)) (n := -padicValRat p (SixContact.J u))
      (by exact_mod_cast hprime.out.one_lt) (neg_lt_zero.mpr hjval)
  have hc : v (3779136:weightField r) = 1 := by
    simpa only [Rat.cast_ofNat,hcnorm,Real.one_rpow] using h 3779136
  have hj : v (SixContact.J u : weightField r) < 1 := by
    rw [h]
    exact Real.rpow_lt_one (by exact_mod_cast padicNorm.nonneg (p:=p) _) hjnorm ht
  obtain ⟨hs,he⟩ := paper_pair hu hδ hr hz
  exact nonunit_of_invariant v hv hc hj _ ((eq_div_iff (pow_ne_zero 10 hs)).mp he)
end
end UnitObstruction
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.nonunit_of_invariant
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.paper_nonunit_of_valuations
