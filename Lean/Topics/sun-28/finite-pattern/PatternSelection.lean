import NumericalPattern

namespace Sun28.FinitePattern
open Finset Filter Topology Sun28.SinglePrime Sun28.ContactFactors Sun28.ContactSieve
open Sun28.MediumSieve Sun28.WeightedSelection
noncomputable section

/-- A one-sided count of a single rational-prime function on the actual quadratic forms.
The width threshold may depend on the finite cutoff and on the fixed dilation. -/
def PatternThreshold (A : Fin 3 → ℚ) (d K L : ℕ) (δ : ℝ) : Prop :=
  ∃ ω : ℕ → ℕ, (∀ j, ∀ᶠ b : ℕ in atTop, ω b ≤ rowWidth j b) ∧
    ∀ w : ℕ → ℕ, Tendsto w atTop atTop →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℕ in atTop, (w b : ℝ)^2 ≤ ε*b) →
      (∀ᶠ b : ℕ in atTop, ω b ≤ w b) →
      ∀ᶠ b : ℕ in atTop, δ*((b : ℝ)*w b) ≤ patternMass A d K L b (w b)

/-- The finite base, its coefficient, and the square-root threshold are independent of
the last cutoff. Only cofinally many final cutoffs need the stated lower count. -/
def LowerInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ (K : ℕ) (α : ℝ), B ≤ K ∧ 0 < α ∧
      ∀ m : ℕ, ∃ L : ℕ, max K m ≤ L ∧
        PatternThreshold (Sun28.RealPoleBounds.fixedScale n) d K L (α / Real.sqrt L)

def UpperInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ), 0 < d → 0 < κ → (∀ p ∈ T,p.Prime) → 2 ∈ T →
      ∀ H Y : ℝ, ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ L : ℕ, K ≤ L → ∃ J, LogRow (Sun28.RealPoleBounds.fixedScale n) d H Y T κ L J C

def PrimeUpperInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ), 0 < d → 0 < κ → (∀ p ∈ T,p.Prime) → 2 ∈ T →
      ∀ H Y : ℝ, ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ L : ℕ, K ≤ L → ∃ J, PrimeRow (Sun28.RealPoleBounds.fixedScale n) d H Y T κ L J C

theorem upper_of_prime (input : PrimeUpperInputs) : UpperInputs := by
  intro X c q n hr d κ T dp kp primes two H Y
  obtain ⟨K,C,non,all⟩ := input X c q n hr d κ T dp kp primes two H Y
  refine ⟨max K 2,C,non,?_⟩
  intro L hL
  obtain ⟨J,upper⟩ := all L ((le_max_left _ _).trans hL)
  exact ⟨J,one_prime_transfer (by omega) non upper⟩

/-- A finite product of local proportions is one sufficient normalization for the lower
bound. This step uses only Gauss's finite norm fibres and the factorial estimate. -/
theorem threshold_of_product {A : Fin 3 → ℚ} {d K L : ℕ} {α : ℝ}
    (big : 7 ≤ K) (logK : 416 ≤ Real.log K) (kl : K ≤ L) (non : 0 ≤ α)
    (input : PatternThreshold A d K L (α * ∏ p ∈ places K L,(atom p)^(shifts A).card)) :
    PatternThreshold A d K L (α / Real.sqrt L) := by
  obtain ⟨ω,slow,count⟩ := input
  refine ⟨ω,slow,fun w grow short bound => ?_⟩
  filter_upwards [count w grow short bound] with b hb
  apply le_trans _ hb
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (product_cost big logK kl (GaussianSelection.shifts_card_le A)) non

variable {A : Fin 3 → ℚ} {d κ K L J : ℕ} {T : Finset ℕ} {H Y δ C : ℝ}

theorem surplus_at (finite : PatternThreshold A d K L δ)
    (middle : LogRow A d H Y T κ L J C)
    (big : 2 ≤ K) (kl : K ≤ L) (inT : ∀ p ∈ T,p ≤ K) (inAux : ∀ p ∈ κ.primeFactors,p ≤ K)
    (pos : 0 < δ) (margin : C/(L:ℝ) < δ/2) :
    ∃ S : Finset (Record A d H Y), surplus T κ L S := by
  obtain ⟨ω,slow,count⟩ := finite
  let pred := fun j b => J ≤ j → ∀ t : ℕ, b = lengthAt t →
    middleMass T κ L (logCutoff A t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) b (rowWidth j b)) ≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((b:ℝ)*rowWidth j b)
  have rows (j : ℕ) : ∀ᶠ b in atTop,pred j b := by
    by_cases enough : J ≤ j
    case neg => exact Eventually.of_forall (fun _ h => False.elim (enough h))
    obtain ⟨t₀,h⟩ := eventually_atTop.mp (middle j enough)
    refine eventually_atTop.mpr ⟨2^(400*t₀)+1,?_⟩
    intro b hb _ t eq
    have ht : t₀ ≤ t := by
      by_contra! ne
      have le := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left 400 ne.le)
      rw [eq,length_pow] at hb
      omega
    exact eq ▸ h t ht
  obtain ⟨s,up,good,grow,short⟩ := choose_width ω pred slow rows
  let w := fun b => rowWidth (s b) b
  let boxes : CountingBoxes A d H Y := numericalBoxes w
    (fun m => eventually_atTop.mp (tendsto_atTop.mp grow m))
    (fun ε ep => eventually_atTop.mp (short ε ep))
  have count' := count w grow short (good.mono (fun b h => h.2))
  have main := count'.and (eventually_pattern_le_main (A:=A) (L:=L) (d:=d) (H:=H) (Y:=Y) inT inAux w short)
  have near := (relative_error A).eventually_lt_const (by linarith : 0 < δ/4)
  have eps := eventual_error up (by linarith : 0 < δ/4)
  have total := main.and ((eventually_area_pos boxes).and (eps.and good))
  have stages := up.eventually (eventually_ge_atTop J)
  have all := (length_grows.eventually (total.and stages)).and
    (near.and ((tendsto_atTop.mp (cutoff_grows A) L).and (cutoff_within A)))
  obtain ⟨t,⟨⟨⟨⟨mass,inc⟩,ar,error,mid,_⟩,stage⟩,small,lr,within⟩⟩ := all.exists
  let N := lengthAt t
  let W := w N
  have wid : W ≤ side t := (Nat.div_le_self _ _).trans_eq (Nat.sqrt_eq' _)
  have large := log_tail (A:=A) (d:=d) (H:=H) (Y:=Y) T κ t W wid (by omega) within
    (fun p hp => (inT p hp).trans (kl.trans lr)) (fun p hp => (inAux p hp).trans (kl.trans lr))
  let S := box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let Z : ℝ := (N:ℝ)*W
  have hi : removedMass T κ (logCutoff A t) S ≤ (meanConstant A/(growthBound A t:ℝ))*Z := large
  have md : middleMass T κ L (logCutoff A t) S ≤ (C/(L:ℝ)+1/((s N:ℝ)+1))*Z := mid stage t rfl
  change 0 < Z at ar
  have lower : δ*Z ≤ mainMass T κ L S := mass.trans inc
  refine ⟨S,?_⟩
  change removedMass T κ L S < mainMass T κ L S
  rw [split_removed _ _ _ _ lr _]
  apply (add_le_add md hi).trans_lt
  apply lt_of_lt_of_le _ lower
  rw [←add_mul]
  apply mul_lt_mul_of_pos_right _ ar
  change 1/((s N:ℝ)+1) ≤ δ/4 at error
  linarith

/-- Independent base thresholds and independent constants for the two analytic
estimates suffice. The finite count compares only the single common prime set. -/
theorem positive_surplus (lower : LowerInputs) (upper : UpperInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K₁,C,non,upp⟩ := upper X c q n roots d κ T dp kp primes two H Y
  let B := max 2 (max (T.sup id) (κ.primeFactors.sup id))
  obtain ⟨K,α,bk,ap,low⟩ := lower X c q n roots d dp B
  obtain ⟨m,hm⟩ := exists_nat_gt ((2*C/α)^2)
  obtain ⟨L,hL,finite⟩ := low (max m K₁)
  have kl : K ≤ L := (le_max_left _ _).trans hL
  have ku : K₁ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have ml : m ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have k2 : 2 ≤ K := (le_max_left _ _).trans bk
  have lp : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have sp := Real.sqrt_pos.2 lp
  have sq := Real.sq_sqrt lp.le
  have cap : (2*C/α)^2 < (L:ℝ) := hm.trans_le (by exact_mod_cast ml)
  have lt : 2*C/α < Real.sqrt (L : ℝ) := (Real.lt_sqrt (div_nonneg (by positivity) ap.le)).mpr cap
  have prod := (div_lt_iff₀ ap).mp lt
  have margin : C/(L:ℝ) < (α / Real.sqrt L)/2 := by
    apply (div_lt_iff₀ lp).mpr
    field_simp [sp.ne']
    nlinarith only [prod,mul_lt_mul_of_pos_right prod sp,sq,congrArg (fun t : ℝ => α*t) sq]
  obtain ⟨J,rows⟩ := upp L ku
  have tin (p : ℕ) (mem : p ∈ T) : p ≤ K :=
    (Finset.le_sup (f:=id) mem).trans ((le_max_left _ _).trans ((le_max_right _ _).trans bk))
  have ain (p : ℕ) (mem : p ∈ κ.primeFactors) : p ≤ K :=
    (Finset.le_sup (f:=id) mem).trans ((le_max_right _ _).trans ((le_max_right _ _).trans bk))
  exact ⟨L, surplus_at finite rows k2 kl tin ain (div_pos ap sp) margin⟩

end
end Sun28.FinitePattern
#print axioms Sun28.FinitePattern.upper_of_prime
#print axioms Sun28.FinitePattern.threshold_of_product
#print axioms Sun28.FinitePattern.surplus_at
#print axioms Sun28.FinitePattern.positive_surplus
