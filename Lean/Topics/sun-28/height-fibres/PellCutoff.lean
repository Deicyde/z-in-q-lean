import PellSectors

/-! The published Pell estimate removes all primitive slopes in a logarithmic
neighborhood of the contact at infinity, including all integral slopes. -/
namespace Sun28.HeightFibres
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors
noncomputable section
set_option exponentiation.threshold 2000
set_option maxRecDepth 8192

/-- Glazer's literal coefficient absorbs 2^810 times the 24th power of the
full contact radical. The fixed primorial is spent just once. -/
theorem original_margin (A B : ℤ) :
    2^810*(heightRadical A B:ℝ)^24≤glazerConstant24*(oddProduct A B:ℝ)^24 := by
  have c : (2:ℝ)^810≤(4608:ℝ)^165888 := by
    calc
      _ ≤ (4608:ℝ)^810 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by decide)
  have o : 0≤(oddProduct A B:ℝ)^24:=by positivity
  have cap : (2:ℝ)^810≤2*(4608^165888+6^100) := by
    let M:ℝ:=(4608:ℝ)^165888
    let Q:ℝ:=(6:ℝ)^100
    have m0 : 0≤M:=pow_nonneg (by norm_num) _
    have q0 : 0≤Q:=pow_nonneg (by norm_num) _
    change (2:ℝ)^810≤M at c
    change (2:ℝ)^810≤2*(M+Q)
    apply c.trans ((le_add_of_nonneg_right q0).trans _)
    rw [two_mul]
    exact le_add_of_nonneg_right (add_nonneg m0 q0)
  have eq : glazerConstant24=2*((4608:ℝ)^165888+6^100)*(cutoffProduct:ℝ)^24+128 := by
    simp only [glazerConstant24,cutoffProduct,primeProduct,Nat.cast_prod]
  rw [heightRadical,Nat.cast_mul,mul_pow,eq,add_mul,mul_assoc]
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right cap (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) o)).trans
    (le_add_of_nonneg_right (mul_nonneg (by norm_num : (0:ℝ)≤128) o))

theorem denominator_sector (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0)
    (small : numberLog B≤(heightRadical A B:ℝ)^14) : target A B := by
  let T:ℝ:=heightRadical A B
  have one : 1≤T := by
    exact Nat.one_le_cast.mpr (show 1≤heightRadical A B from Nat.mul_pos pos_cutoff (pos_odd A B))
  have h:=denominator_height pell regulator disc off
  change pairLogHeight A B≤2^190*T^19+2^170*T^10*(numberLog B+12) at h
  have lo : T^19≤T^24 := pow_le_pow_right₀ one (by decide)
  have le14 : 1≤T^14 := one_le_pow₀ one
  have sum : numberLog B+12≤13*T^14 := by change numberLog B≤T^14 at small;linarith
  have w := mul_le_mul_of_nonneg_left sum (show 0≤(2:ℝ)^170*T^10 by positivity)
  have eq : (2:ℝ)^170*T^10*(13*T^14)=13*2^170*T^24 := by ring
  rw [eq] at w
  have ht : pairLogHeight A B≤2^810*T^24 := by
    calc
      _ ≤ _ := h
      _ ≤ 2^190*T^24+13*2^170*T^24 :=
        add_le_add (mul_le_mul_of_nonneg_left lo (by positivity)) w
      _ = ((2:ℝ)^190+13*2^170)*T^24 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (by decide : (2:ℕ)^190+13*2^170≤2^810)) (pow_nonneg (le_trans (by norm_num) one) _)
  have endpt:=ht.trans (original_margin A B)
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using endpt

/-- Every integer slope outside the original marks is covered uniformly. -/
theorem integer_slope (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) (A : ℤ) (off : ∀ i,oldForm i A 1≠0) : target A 1 :=
  denominator_sector pell regulator disc off (by
    have z : numberLog 1=0 := by norm_num [numberLog]
    rw [z]
    exact pow_nonneg (Nat.cast_nonneg _) _)

def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (heightRadical A B:ℝ)^14<numberLog B →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

/-- Both tests use the very same primitive pair and the original constant. -/
theorem original_iff_remaining (units : PublishedCorollary72) (pell : PublishedPell312)
    (regulator : RegulatorBound) (disc : BiquadraticDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining := by
  constructor
  · exact fun full A B cop off _ _=>full A B cop off
  · intro remain
    apply (original_iff_exact_least units).mpr
    intro A B cop off failed
    rcases le_or_gt (numberLog B) ((heightRadical A B:ℝ)^14) with small|large
    · exact denominator_sector pell regulator disc off small
    · exact remain A B cop off large failed

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.original_margin
#print axioms Sun28.HeightFibres.denominator_sector
#print axioms Sun28.HeightFibres.integer_slope
#print axioms Sun28.HeightFibres.original_iff_remaining
