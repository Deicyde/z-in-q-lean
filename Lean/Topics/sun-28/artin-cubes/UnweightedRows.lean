import HybridProjection
import PaperPattern

namespace Sun28.CutoffCount
open Finset Filter Topology Sun28.FinitePattern Sun28.SinglePrime Sun28.ContactFactors Sun28.PrimeMass
noncomputable section
open scoped Classical

/-- Number of integer pairs in the dyadic box for which all forms are positive
primes in the same two-sign set. Each pair is counted once. -/
def count (A : Fin 3 → ℚ) (d L N W : ℕ) : ℕ :=
  (((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun q : ℕ × ℕ => d ∣ q.2)).filter
    fun q => ∀ i : ↥(shifts A), 0 ≤ form A q i ∧ commonPrime L L (form A q i).toNat).card

/-- Restricting to narrow enough fixed rows puts every form above N/4. -/
theorem guard_rows (A : Fin 3 → ℚ) : ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ N : ℕ in atTop,
    ∀ q ∈ Ioc (N/2) N ×ˢ Icc 1 (rowWidth j N),
      ∀ i : ↥(shifts A), (N:ℝ)/4 ≤ (form A q i:ℝ) := by
  apply fixed_rows (P:=fun N W => ∀ q ∈ Ioc (N/2) N ×ˢ Icc 1 W, ∀ i : ↥(shifts A), (N:ℝ)/4 ≤ (form A q i:ℝ))
  intro w short
  let C : ℝ := (maxCoefficient A:ℝ)+1
  have cp : 0<C := by dsimp [C];positivity
  filter_upwards [short (1/(4*C)) (by positivity)] with N h
  intro q mem i
  obtain ⟨hu,hw⟩ := mem_product.mp mem
  have u := (mem_Ioc.mp hu).1
  have wle : (q.2:ℝ) ≤ w N := by exact_mod_cast (mem_Icc.mp hw).2
  have low : (N:ℝ) < 2*q.1 := by exact_mod_cast (show N<2*q.1 by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) q.2) wle 2
  have lim : C*(q.2:ℝ)^2 ≤ (N:ℝ)/4 := by
    apply (mul_le_mul_of_nonneg_left (hs.trans h) cp.le).trans_eq
    field_simp
  have ci : (offset (dilation A) i).natAbs ≤ maxCoefficient A :=
    Finset.le_sup (f:=fun i : ↥(shifts A) => (offset (dilation A) i).natAbs) (mem_univ _)
  have lower : -(offset (dilation A) i) ≤ (maxCoefficient A:ℤ) :=
    (neg_le_abs _).trans (by simpa only [← Int.natCast_natAbs] using (Int.ofNat_le.mpr ci))
  have coeff : -C ≤ ((offset (dilation A) i : ℤ):ℝ) := by
    dsimp [C];have : -((offset (dilation A) i : ℤ):ℝ) ≤ maxCoefficient A := by exact_mod_cast lower
    linarith
  unfold form;push_cast
  linarith only [low,lim,mul_le_mul_of_nonneg_right coeff (sq_nonneg (q.2:ℝ)),show (-C)*(q.2:ℝ)^2= -(C*(q.2:ℝ)^2) by ring]

private theorem weight_nonneg (L : ℕ) (m : ℤ) : 0 ≤ primeWeight L L m := by
  unfold primeWeight;split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.2.1.one_le)
  · rfl

/-- Removing the logarithmic weights costs at most the explicit factor (log N/2)^k. -/
theorem mass_of_count (A : Fin 3 → ℚ) (d L N W : ℕ) (large : 16 ≤ N)
    (guards : ∀ q ∈ Ioc (N/2) N ×ˢ Icc 1 W, ∀ i : ↥(shifts A), (N:ℝ)/4 ≤ (form A q i:ℝ)) :
    ((Real.log (N:ℝ))/2)^(shifts A).card * count A d L N W ≤ patternMass A d L L N W := by
  let S := (Ioc (N/2) N ×ˢ Icc 1 W).filter (fun q : ℕ × ℕ => d ∣ q.2)
  let good := fun q : ℕ × ℕ => ∀ i : ↥(shifts A),0 ≤ form A q i ∧ commonPrime L L (form A q i).toNat
  have top : (16:ℝ) ≤ N := by exact_mod_cast large
  have np : 0<(N:ℝ) := by linarith
  have lg := Real.log_le_log (by norm_num : 0<(16:ℝ)) top
  rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow] at lg
  norm_num only [Nat.cast_ofNat] at lg
  have cut : Real.log (N:ℝ)/2 ≤ Real.log ((N:ℝ)/4) := by
    rw [Real.log_div np.ne' (by norm_num)];linarith
  have each (q : ℕ × ℕ) (hq : q ∈ S.filter good) :
      (Real.log (N:ℝ)/2)^(shifts A).card ≤ patternWeight A L L q := by
    obtain ⟨hit,ok⟩ := mem_filter.mp hq
    rw [show (Real.log (N:ℝ)/2)^(shifts A).card = ∏ _i : ↥(shifts A), Real.log (N:ℝ)/2 by simp [div_pow]]
    apply prod_le_prod₀ (fun _ _ => div_nonneg (Real.log_nonneg (by linarith)) (by norm_num))
    intro i _
    have hi := guards q (mem_filter.mp hit).1 i
    rw [primeWeight,ite_eq_left (ok i)]
    have e : (((form A q i).toNat:ℕ):ℝ)=(form A q i:ℝ) := by exact_mod_cast Int.toNat_of_nonneg (ok i).1
    rw [e];exact cut.trans (Real.log_le_log (by positivity) hi)
  calc
    _ = ∑ _q ∈ S.filter good,(Real.log (N:ℝ)/2)^(shifts A).card := by simp [S,good,count,mul_comm]
    _ ≤ ∑ q ∈ S.filter good,patternWeight A L L q := sum_le_sum each
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun q _ _ => prod_nonneg (fun i _ => weight_nonneg _ _))

/-- Lower bounds for the ordinary number of simultaneous prime values. -/
def rows (A : Fin 3 → ℚ) (d L : ℕ) (δ : ℝ) : Prop :=
  ∀ J : ℕ, ∃ j ≥ J, ∃ᶠ t : ℕ in atTop,
    let N := Sun28.SinglePrime.lengthAt t
    let W := rowWidth j N
    δ*((N:ℝ)*W)/(Real.log (N:ℝ))^(shifts A).card ≤ count A d L N W

theorem frequent_of_count {A : Fin 3 → ℚ} {d L : ℕ} {δ : ℝ} (h : rows A d L δ) :
    frequentRows A d L L (δ/(2:ℝ)^(shifts A).card) := by
  obtain ⟨I,guard⟩ := guard_rows A
  intro J
  obtain ⟨j,hj,found⟩ := h (max I J)
  refine ⟨j,(le_max_right _ _).trans hj,?_⟩
  have late := Sun28.SinglePrime.length_grows.eventually (eventually_ge_atTop (16:ℕ))
  have g := Sun28.SinglePrime.length_grows.eventually (guard j ((le_max_left _ _).trans hj))
  apply found.and_eventually (late.and g) |>.mono
  rintro t ⟨hc,large,guards⟩
  let N := Sun28.SinglePrime.lengthAt t
  let W := rowWidth j N
  have big : 16≤N := large
  have lp := Real.log_pos (by exact_mod_cast (show 1<N by omega) : (1:ℝ)<N)
  have power := pow_pos lp (shifts A).card
  change δ*((N:ℝ)*W)/(Real.log (N:ℝ))^(shifts A).card ≤ count A d L N W at hc
  have m := mass_of_count A d L N W big guards
  change δ/(2:ℝ)^(shifts A).card*((N:ℝ)*W) ≤ patternMass A d L L N W
  apply le_trans _ m
  rw [div_pow]
  have two := pow_pos (by norm_num : (0:ℝ)<2) (shifts A).card
  apply (le_of_mul_le_mul_right (a:=(2:ℝ)^(shifts A).card) _ two)
  calc
    _ = δ*((N:ℝ)*W) := by field_simp
    _ ≤ (count A d L N W:ℝ)*(Real.log (N:ℝ))^(shifts A).card := (div_le_iff₀ power).mp hc
    _ = _ := by field_simp

end
end Sun28.CutoffCount
#print axioms Sun28.CutoffCount.guard_rows
#print axioms Sun28.CutoffCount.mass_of_count
#print axioms Sun28.CutoffCount.frequent_of_count
