import CubicHeight

namespace Sun28.HeightCubics
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQBlueprint.TwistDescent
noncomputable section

/-- An elementary monomial criterion with no restriction on the number of prime factors. -/
theorem small_estimate {N t:ℕ} (np:0<N) (tp:0<t) (small:N≤t^11) :
    estimate N≤2^30*(t:ℝ)^24 := by
  let T:ℝ:=t
  let M:ℝ:=62208*(N:ℝ)^2
  have one:1≤T:=Nat.one_le_cast.mpr tp
  have n1:1≤(N:ℝ):=Nat.one_le_cast.mpr np
  have pos:0<(N:ℝ):=lt_of_lt_of_le zero_lt_one n1
  have tpos:0<T:=lt_of_lt_of_le zero_lt_one one
  have nle:(N:ℝ)≤T^11:=by dsimp only [T];exact_mod_cast small
  have lc:=Real.log_le_log pos nle
  rw [Real.log_pow] at lc
  have lt:=Real.log_le_sub_one_of_pos tpos
  have l2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  have lC:=Real.log_le_log (by norm_num:(0:ℝ)<62208) (show (62208:ℝ)≤2^16 by norm_num)
  rw [Real.log_pow] at lC
  have lm:Real.log M≤38*T:=by
    rw [show M=62208*(N:ℝ)^2 from rfl,Real.log_mul (by norm_num) (pow_ne_zero _ pos.ne'),Real.log_pow]
    push_cast at lc lC ⊢
    linarith only [lc,lC,l2,lt,one]
  have lc₀ : Real.log (4*(N:ℝ)^6)≤68*T :=by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ pos.ne'),Real.log_pow,show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    push_cast at lc ⊢
    linarith only [lc,l2,lt,one]
  have M1:1≤M :=by dsimp only [M]; nlinarith only [one_le_pow₀ n1 (n:=2)]
  have mcap:M≤62208*T^22:=by
    dsimp only [M];rw [show 22=11*2 by decide,pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos.le nle 2) (by norm_num)
  have loss:=mul_le_mul mcap (pow_le_pow_left₀ (Real.log_nonneg M1) lm 2) (sq_nonneg _) (by positivity)
  have prev:T≤T^24:=by simpa using pow_le_pow_right₀ one (show 1≤24 by decide)
  change 5*Real.log (4*(N:ℝ)^6)+6*M*(Real.log M)^2+35≤2^30*T^24
  nlinarith only [loss,lc₀,prev,one_le_pow₀ one (n:=24)]

def Covered (A B:ℤ) : Prop :=
  ∃ r:ThreeRows,estimate (chartN r A B)≤glazerConstant24*(oddProduct A B:ℝ)^24

theorem covered_of_conductor {A B:ℤ} (r:ThreeRows) (modest:chartN r A B≤heightRadical A B^11) :
    Covered A B := by
  have pos:0<chartN r A B:=Finset.prod_pos fun _ mem=>(places_prime mem).pos
  have posT:0<heightRadical A B:=Nat.mul_pos pos_cutoff (pos_odd _ _)
  have h:=small_estimate pos posT modest
  have c: (2:ℝ)^30≤2^810:=pow_le_pow_right₀ (by norm_num) (by decide)
  exact ⟨r,(h.trans (mul_le_mul_of_nonneg_right c (by positivity))).trans (original_margin A B)⟩

theorem five_height_of_cubic (mordell:SupportedMordell74) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (cover:Covered A B) : target A B := by
  obtain ⟨r,small⟩:=cover
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using
    (triple_height mordell r cop off).trans small

def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Covered A B → target A B

theorem original_iff_cubics (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (mordell:SupportedMordell74) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining := by
  constructor
  · exact fun full A B cop off _ _ _ _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_pairs units pell classes formula).mpr
    intro A B cop off s l f c p
    by_cases covered:Covered A B
    · exact five_height_of_cubic mordell cop off covered
    · exact rem A B cop off s l f c p covered
end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.small_estimate
#print axioms Sun28.HeightCubics.covered_of_conductor
#print axioms Sun28.HeightCubics.five_height_of_cubic
#print axioms Sun28.HeightCubics.original_iff_cubics
