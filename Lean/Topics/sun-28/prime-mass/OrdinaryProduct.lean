import OrdinaryFactors

namespace Sun28.PrimeMass
open Finset Sun28.SinglePrime Sun28.MediumSieve
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem beta_positive {p : ℕ} [Fact p.Prime] (c : ι → ZMod p) : 0 < beta c := by
  have pp := (Fact.out : p.Prime)
  have np : (univ.image c).card ≤ p := by simpa using (card_le_univ (univ.image c))
  have n : 0 < ∑ v : ZMod p,(permitted c v).card := by
    rw [ordinary_count]; exact Nat.mul_pos (by have := pp.one_lt; omega) (by omega)
  have pr : (0:ℝ)<p := by exact_mod_cast pp.pos
  have l : (1:ℝ)/(p:ℝ)<1 := (div_lt_one pr).mpr (by exact_mod_cast pp.one_lt)
  unfold beta
  exact div_pos (div_pos (by exact_mod_cast n) (sq_pos_of_pos pr)) (pow_pos (sub_pos.mpr l) _)

private theorem product_lower (S : Finset ℕ) (f : ℕ → ℝ) (non : ∀ p ∈ S,0≤f p)
    (small : ∀ p ∈ S,f p≤1) : 1-∑ p ∈ S,f p ≤ ∏ p ∈ S,(1-f p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S h ih =>
    rw [prod_insert h,sum_insert h]
    have ni := non i (mem_insert_self ..)
    have si := small i (mem_insert_self ..)
    have rest := ih (fun p hp => non p (mem_insert_of_mem hp)) (fun p hp => small p (mem_insert_of_mem hp))
    have sum0 := sum_nonneg (s:=S) (f:=f) fun p hp => non p (mem_insert_of_mem hp)
    apply le_trans _ (mul_le_mul_of_nonneg_left rest (sub_nonneg.mpr si))
    nlinarith only [mul_nonneg ni sum0]

/-- The ordinary factors on every tail retain at least half the mass.
The bound is uniform in the integral coefficients and the final cutoff. -/
theorem ordinary_product (c : ι → ℤ) (k13 : Fintype.card ι ≤ 13) (L R : ℕ) (base : 676 ≤ L) :
    1/2 ≤ ∏ q ∈ (places L R).attach,
      let _inst : Fact q.val.Prime := ⟨(mem_places.mp q.property).2.2⟩
      beta (fun i => (c i : ZMod q.val)) := by
  let f := fun p : ℕ => 338/(p:ℝ)^2
  let S := places L R
  have non (p : ℕ) (_ : p ∈ S) : 0 ≤ f p := by dsimp [f]; positivity
  have small (p : ℕ) (hp : p ∈ S) : f p ≤ 1 := by
    have pp : (676:ℝ) ≤ p := by exact_mod_cast base.trans (mem_places.mp hp).1.le
    dsimp [f];apply (div_le_iff₀ (by positivity : 0<(p:ℝ)^2)).mpr; nlinarith
  have ls : (676:ℝ) ≤ L := by exact_mod_cast base
  have sum : ∑ p ∈ S,f p ≤ 1/2 := by
    have eq : ∑ p ∈ S,f p = 338*(∑ p ∈ S,1/(p:ℝ)^2) := by rw [mul_sum];apply sum_congr rfl;intro p _;dsimp [f]; ring
    rw [eq]
    apply (mul_le_mul_of_nonneg_left (reciprocal_squares L R (by omega)) (by norm_num : (0:ℝ)≤338)).trans
    rw [mul_one_div,div_le_iff₀ (by linarith : (0:ℝ)<L)]; linarith
  calc
    (1:ℝ)/2 ≤ 1-∑ p ∈ S,f p := by linarith
    _ ≤ ∏ p ∈ S,(1-f p) := product_lower S f non small
    _ = ∏ q ∈ S.attach,(1-f q.val) := (Finset.prod_attach S (fun p => 1-f p)).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun q _ => sub_nonneg.mpr (small _ q.property))
      intro q _
      let _inst : Fact q.val.Prime := ⟨(mem_places.mp q.property).2.2⟩
      have cap : 2*Fintype.card ι ≤ q.val := by have := (mem_places.mp q.property).1;omega
      apply le_trans _ (beta_large (fun i => (c i : ZMod q.val)) cap)
      have kk : (Fintype.card ι:ℝ) ≤ 13 := by exact_mod_cast k13
      dsimp [f]
      apply sub_le_sub_left
      have hsq : (Fintype.card ι:ℝ)^2 ≤ 13^2 := pow_le_pow_left₀ (by positivity) kk 2
      exact div_le_div_of_nonneg_right (by linarith only [hsq]) (sq_nonneg _)
end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.beta_positive
#print axioms Sun28.PrimeMass.ordinary_product
