import OrdinaryProducts
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Sun28.Ordinary
open Height

/-- Sun's B, the maximum of 1 and the absolute values of the four integer indices. -/
noncomputable def indexSize (n : Fin 4 → ℤ) : ℝ :=
  max 1 (max |(n 0 : ℝ)| (max |(n 1 : ℝ)| (max |(n 2 : ℝ)| |(n 3 : ℝ)|)))

theorem one_le_indexSize (n : Fin 4 → ℤ) : 1 ≤ indexSize n := le_max_left _ _
theorem abs_first_le_indexSize (n : Fin 4 → ℤ) : |(n 0 : ℝ)| ≤ indexSize n :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- A positive explicit coefficient, with the additive term of Corollary 2.4 retained. -/
def ordinaryConstant (C c₁ c₂ : ℝ) := 1+c₁*C+c₂

private theorem height_from_divisibility (S : Finset ℕ) (t : Fin 3 → ℚ) {A B C c₁ c₂ : ℝ}
    {N k : ℕ} (hn : 0<N) (ha : 0≤A) (hexp : (k:ℝ)*A=24)
    (hC : 1≤C) (hc : 0≤c₁) (hc' : 0≤c₂)
    (five : ∀ j, logHeight₁ (t j) ≤ C*(∏ p ∈ contactPrimes S (t j), (p:ℝ))^24)
    (scale : ∀ H : ℝ, 1≤H → (∀ j, logHeight₁ (t j)≤H) → B^2≤c₁*H+c₂)
    (divides : ∀ j, (∏ p ∈ contactPrimes S (t j), p)^k ∣ N) :
    B^2≤ordinaryConstant C c₁ c₂*(1+(N:ℝ)^A) := by
  have n1 : (1:ℝ)≤N := by exact_mod_cast hn
  have ra := Real.one_le_rpow n1 ha
  have h := scale (C*(N:ℝ)^A) (one_le_mul_of_one_le_of_one_le hC ra) (by
    intro j
    apply (five j).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤C)
    let R : ℕ := ∏ p ∈ contactPrimes S (t j), p
    have db : R^k≤N := Nat.le_of_dvd hn (divides j)
    have re : (R:ℝ)^k ≤ (N:ℝ) := by exact_mod_cast db
    have ord := Real.rpow_le_rpow (by positivity : 0≤(R:ℝ)^k) re ha
    rw [←Real.rpow_natCast (R:ℝ) k, ←Real.rpow_mul (by positivity),hexp] at ord
    simpa [R] using ord)
  have prod : 0≤c₁*C := mul_nonneg hc (by linarith)
  have rem := mul_nonneg hc' (zero_le_one.trans ra)
  unfold ordinaryConstant
  linarith only [h,ra,prod,rem]

/-- Sun, Lemma 7.1, on the same three arguments as the ordinary pole predicates. -/
theorem ordinary_height_bounds (S : Finset ℕ) (t : Fin 3 → ℚ) (n : Fin 4 → ℤ) (β : ℚ)
    {C c₁ c₂ : ℝ} (hC : 1≤C) (hc : 0≤c₁) (hc' : 0≤c₂)
    (five : ∀ j, logHeight₁ (t j) ≤ C*(∏ p ∈ contactPrimes S (t j), (p:ℝ))^24)
    (scale : ∀ H : ℝ, 1≤H → (∀ j, logHeight₁ (t j)≤H) → (indexSize n)^2≤c₁*H+c₂)
    (products : ∀ j, (∏ p ∈ contactPrimes S (t j), (p:ℤ))^64 ∣ lucas (n 1) (n 2) (n 3) ∧
      (∏ p ∈ contactPrimes S (t j), p)^16 ∣ (β-n 0).num.natAbs) :
    (lucas (n 1) (n 2) (n 3)≠0 → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+|((lucas (n 1) (n 2) (n 3) : ℤ) : ℝ)|^(3/8:ℝ))) ∧
    (β≠(n 0:ℚ) → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+((β-n 0).num.natAbs:ℝ)^(3/2:ℝ))) := by
  constructor
  · intro hn
    let Δ := lucas (n 1) (n 2) (n 3)
    have h := height_from_divisibility S t (N:=Δ.natAbs) (k:=64) (A:=3/8)
      (Int.natAbs_pos.mpr hn) (by norm_num) (by norm_num)
      hC hc hc' five scale (fun j => by
        have dv := (products j).1
        rw [←Nat.cast_prod] at dv
        have nat := Int.natAbs_dvd_natAbs.mpr dv
        simpa only [Int.natAbs_pow,Int.natAbs_natCast] using nat)
    simpa only [Δ,Nat.cast_natAbs,Int.cast_abs] using h
  · intro hn
    have nz : (β-n 0).num ≠ 0 := by
      simpa using (sub_ne_zero.mpr hn : β-(n 0:ℚ)≠0)
    exact height_from_divisibility S t (N:=(β-n 0).num.natAbs) (k:=16) (A:=3/2)
      (Int.natAbs_pos.mpr nz) (by norm_num) (by norm_num)
      hC hc hc' five scale (fun j => (products j).2)

end Sun28.Ordinary
#print axioms Sun28.Ordinary.one_le_indexSize
#print axioms Sun28.Ordinary.abs_first_le_indexSize
#print axioms Sun28.Ordinary.ordinary_height_bounds
