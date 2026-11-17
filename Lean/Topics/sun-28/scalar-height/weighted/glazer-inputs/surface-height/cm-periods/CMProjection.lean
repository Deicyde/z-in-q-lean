import CMPeriod
import DiamondProjection
namespace ZInQBlueprint.CMPeriods
open Sun28 Sun28.Concrete Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open Sun28.MultiplierChoice ZInQBlueprint.DiamondHeight ZInQBlueprint.WildLevel
noncomputable section
set_option exponentiation.threshold 250
/-- Six primes of the fixed cutoff already dominate the entire CM contribution. -/
theorem radical_lower (A B : ℤ) : 30030 ≤ heightRadical A B := by
  let S : Finset ℕ := {2,3,5,7,11,13}
  have sub : S ⊆ oldCutoff := by
    intro p hp
    simp only [S, Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide),by decide⟩
  have h := Finset.prod_le_prod_of_subset_of_one_le (f:=fun p:ℕ => p) sub
    (fun p hp _ => (Finset.mem_filter.mp hp).2.one_lt.le)
  have small : (∏ p ∈ S, p) = 30030 := by decide
  rw [small] at h
  exact h.trans (Nat.le_mul_of_pos_right cutoffProduct (pos_odd A B))
theorem cm_comparison (table : SmallClassDiscriminants) {h : ℝ} (P : PeriodPresentation h) (A B : ℤ) :
    let R := (heightRadical A B : ℝ)
    h ≤ 6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R))) := by
  let R := (heightRadical A B : ℝ)
  change h ≤ 6*R+8*Real.log _
  have r : (30030:ℝ) ≤ R := Nat.cast_le.mpr (radical_lower A B)
  have h0 := surface_le table P
  have m : (1:ℝ) ≤ max 1 (max (Real.log 576) (6*R)) := le_max_left _ _
  have l := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by norm_num : (1:ℝ)≤14^32*576) m)
  linarith only [h0,r,l]

/-- Slope-specific geometry remaining after the CM height calculation.
The metric comparison must hold for the same surface as the chosen branch. -/
def MarkedFibres (C K : ℝ) : Prop := ∀ A B : ℤ, Int.gcd A B=1 → (∀ i, oldForm i A B≠0) →
  ∃ h:ℝ, pairLogHeight A B≤2*max 0 h+K ∧
    (let R := heightRadical A B
     (∃ F : QuotientFibre R h, (F.level:ℝ) ≤ C*(R:ℝ)^2) ∨ Nonempty (PeriodPresentation h))
theorem marked_quotients {C K : ℝ} (table : SmallClassDiscriminants) (fibres : MarkedFibres C K) :
    MarkedQuotients C K := by
  intro A B cop off
  obtain ⟨h,metric,branches⟩ := fibres A B cop off
  rcases branches with modular | periods
  · exact ⟨h,metric,Or.inl modular⟩
  · obtain ⟨P⟩ := periods
    exact ⟨h,metric,Or.inr (cm_comparison table P A B)⟩
theorem one_sign_of_periods (table : SmallClassDiscriminants)
    (fibres : MarkedFibres (210^300) 128) (points : JointSelectedMenus) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 oneSignPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  one_sign_of_quotients (marked_quotients table fibres) points x
end
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.radical_lower
#print axioms ZInQBlueprint.CMPeriods.cm_comparison
#print axioms ZInQBlueprint.CMPeriods.marked_quotients
#print axioms ZInQBlueprint.CMPeriods.one_sign_of_periods
