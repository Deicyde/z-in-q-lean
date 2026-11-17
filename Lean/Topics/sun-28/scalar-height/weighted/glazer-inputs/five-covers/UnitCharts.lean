import LeastChart

/-! The explicit last inequality in Murty and Pasten, JNT 133 (2013), §8, on the ten charts. -/
namespace ZInQBlueprint.FiveCovers
open Finset Height Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors
noncomputable section

/-- The last displayed estimate in the proof of Theorem 1.2 (before the authors round
the coefficients). Section 8 passes from the primitive triple to two rational units. -/
def MurtyPastenEstimate : Prop := ∀ (S : Finset ℕ), (∀ p∈S,p.Prime) → ∀ x y : ℚ,
  RationalSUnit S x → RationalSUnit S y → x+y=1 →
  4*max (logHeight₁ x) (logHeight₁ y)-2*Real.log 2 <
    (96/5:ℝ)*(primeProduct S:ℝ)*Real.log (primeProduct S:ℝ)
     +(26617/500:ℝ)*(primeProduct S:ℝ)+49273/500

def chartBound (n : ℕ) : ℝ := (24/5:ℝ)*(n:ℝ)*Real.log (n:ℝ)+14*(n:ℝ)+57

/-- The unit estimate plus the height change of chart, retaining one logarithm. -/
theorem chart_height (published : MurtyPastenEstimate) {A B : ℤ}
    (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10) :
    pairLogHeight A B < chartBound (leastConductor t A B) := by
  let S:=leastSet t A B
  let x:=crossRatio (first t) (second t) (third t) A B
  have pr (p : ℕ) (hp : p∈S) : p.Prime := small_primes t A B (least_subset t A B off hp)
  have u:=(least_set_iff t A B off S).2 (fun _ h=>h)
  have h:=published S pr x (1-x) u.1 u.2 (by ring)
  have compare : logHeight₁ x ≤ max (logHeight₁ x) (logHeight₁ (1-x)) := le_max_left ..
  have change : pairLogHeight A B≤logHeight₁ x+32 := crossRatio_height _ _ _ (ne_of_lt (increasing t).1)
    (ne_of_lt (lt_trans (increasing t).1 (increasing t).2)) (ne_of_lt (increasing t).2) cop off
  have l : Real.log 2≤1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have n : (1:ℝ)≤leastConductor t A B := Nat.one_le_cast.mpr (least_positive t off)
  change _ < (96/5:ℝ)*(leastConductor t A B:ℝ)*Real.log (leastConductor t A B:ℝ)
    +(26617/500:ℝ)*leastConductor t A B+49273/500 at h
  unfold chartBound
  linarith only [h,compare,change,l,n]

/-- Use the actual least of the ten supports. -/
theorem least_chart_height (published : MurtyPastenEstimate) {A B : ℤ}
    (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    pairLogHeight A B < chartBound (best A B) := by
  obtain ⟨t,e⟩:=best_attained A B
  rw [←e]
  exact chart_height published cop off t

def RemainingChartHeight : Prop := ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
  glazerConstant24*(oddProduct A B:ℝ)^24 < chartBound (best A B) → target A B

theorem original_iff_chart (published : MurtyPastenEstimate) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ RemainingChartHeight := by
  constructor
  · exact fun h A B cop off _=>h A B cop off
  · intro remain A B cop off
    rcases le_or_gt (chartBound (best A B)) (glazerConstant24*(oddProduct A B:ℝ)^24) with h|h
    · have b:=((least_chart_height published cop off).le).trans h
      simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using b
    · exact remain A B cop off h

end
end ZInQBlueprint.FiveCovers
#print axioms ZInQBlueprint.FiveCovers.chart_height
#print axioms ZInQBlueprint.FiveCovers.least_chart_height
#print axioms ZInQBlueprint.FiveCovers.original_iff_chart
