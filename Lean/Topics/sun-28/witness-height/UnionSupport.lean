import MaximumSlope
import HeightTransport

/-! Combine the prime divisibilities before taking the largest height. -/
namespace Sun28.WitnessHeight
open Sun28.Ordinary Height
noncomputable section

def contactUnion (S : Finset ℕ) (t : Fin 3 → ℚ) : Finset ℕ :=
  Finset.univ.biUnion (fun j => contactPrimes S (t j))

def unionRadical (S : Finset ℕ) (t : Fin 3 → ℚ) : ℕ := ∏ p∈contactUnion S t,p

theorem member_radical_dvd (S : Finset ℕ) (t : Fin 3 → ℚ) (j : Fin 3) :
    contactRadical S (t j) ∣ unionRadical S t := by
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hp⟩

theorem union_pos (S : Finset ℕ) (t : Fin 3 → ℚ) :
    0 < unionRadical S t := Finset.prod_pos (fun p hp => by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    exact (mem_contactPrimes.mp hi).1.pos)

theorem member_radical_le (S : Finset ℕ) (t : Fin 3 → ℚ) (j : Fin 3) :
    contactRadical S (t j) ≤ unionRadical S t :=
  Nat.le_of_dvd (union_pos S t) (member_radical_dvd S t j)

theorem union_power_dvd (S : Finset ℕ) (t : Fin 3 → ℚ) (k : ℕ) (a : ℤ)
    (localDiv : ∀ j, (contactRadical S (t j):ℤ)^k ∣ a) : (unionRadical S t:ℤ)^k ∣ a := by
  unfold unionRadical
  rw [Nat.cast_prod]
  apply product_prime_powers
  · intro p hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    exact (mem_contactPrimes.mp hj).1
  · intro p hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    have dp : p ∣ contactRadical S (t j) := Finset.dvd_prod_of_mem _ hj
    exact (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr dp) k).trans (localDiv j)

theorem union_discrepancies (S : Finset ℕ) (t : Fin 3 → ℚ) (Δ : ℤ) (J : ℕ)
    (each : ∀ j, (∏ p∈contactPrimes S (t j),(p:ℤ))^64 ∣ Δ ∧
      (∏ p∈contactPrimes S (t j),p)^16 ∣ J) :
    (unionRadical S t:ℤ)^64 ∣ Δ ∧ unionRadical S t^16 ∣ J := by
  constructor
  · exact union_power_dvd S t 64 Δ (fun j => by simpa only [contactRadical,Nat.cast_prod] using (each j).1)
  · have d := union_power_dvd S t 16 (J:ℤ) (fun j => by exact_mod_cast (each j).2)
    exact_mod_cast d

/-- Only the largest ordinary height is compared with the product of all
contact primes. A prime present in more than one detector occurs once. -/
theorem ordinary_of_union (S : Finset ℕ) (t : Fin 3 → ℚ) (n : Fin 4 → ℤ) (β : ℚ)
    {C c₁ c₂ : ℝ} (hC : 1≤C) (hc₁ : 0≤c₁) (hc₂ : 0≤c₂)
    (scale : ∀ H : ℝ, 1≤H → (∀ i, logHeight₁ (t i)≤H) → (indexSize n)^2≤c₁*H+c₂)
    (j : Fin 3) (largest : ∀ i, logHeight₁ (t i)≤logHeight₁ (t j))
    (height : logHeight₁ (t j)≤C*(unionRadical S t:ℝ)^24)
    (each : ∀ i, (∏ p∈contactPrimes S (t i),(p:ℤ))^64 ∣ lucas (n 1) (n 2) (n 3) ∧
      (∏ p∈contactPrimes S (t i),p)^16 ∣ (β-n 0).num.natAbs) :
    (lucas (n 1) (n 2) (n 3)≠0 → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+|((lucas (n 1) (n 2) (n 3):ℤ):ℝ)|^(3/8:ℝ))) ∧
    (β≠(n 0:ℚ) → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+((β-n 0).num.natAbs:ℝ)^(3/2:ℝ))) := by
  let R := unionRadical S t
  have pos : 0<R := union_pos S t
  have r1 : (1:ℝ)≤R := by exact_mod_cast Nat.succ_le_of_lt pos
  have small := scale (C*(R:ℝ)^24) (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ r1))
    (fun i => (largest i).trans height)
  obtain ⟨d64,d16⟩ := union_discrepancies S t _ _ each
  have transfer (N k : ℕ) (a:ℝ) (hn:0<N) (ha:0≤a) (exp:(k:ℝ)*a=24) (dvd:R^k∣N) :
      (indexSize n)^2≤ordinaryConstant C c₁ c₂*(1+(N:ℝ)^a) := by
    have nat := Nat.le_of_dvd hn dvd
    have re : (R:ℝ)^k≤(N:ℝ) := by exact_mod_cast nat
    have pow := Real.rpow_le_rpow (by positivity : 0≤(R:ℝ)^k) re ha
    rw [←Real.rpow_natCast (R:ℝ) k,←Real.rpow_mul (by positivity),exp] at pow
    have cap : (R:ℝ)^24≤(N:ℝ)^a := by simpa using pow
    have H := small.trans (add_le_add_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left cap (zero_le_one.trans hC)) hc₁) c₂)
    have rest : 0≤(N:ℝ)^a := Real.rpow_nonneg (by positivity) _
    unfold ordinaryConstant
    nlinarith only [H,mul_nonneg hc₁ (zero_le_one.trans hC),mul_nonneg hc₂ rest,rest]
  constructor
  · intro nz
    have nd : R^64 ∣ (lucas (n 1) (n 2) (n 3)).natAbs := by
      simpa [R] using Int.natAbs_dvd_natAbs.mpr d64
    simpa only [Nat.cast_natAbs,Int.cast_abs] using transfer _ 64 (3/8) (Int.natAbs_pos.mpr nz)
      (by norm_num) (by norm_num) nd
  · intro nz
    have live : (β-n 0).num≠0 := by simpa using (sub_ne_zero.mpr nz : β-(n 0:ℚ)≠0)
    exact transfer _ 16 (3/2) (Int.natAbs_pos.mpr live) (by norm_num) (by norm_num) d16

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.member_radical_dvd
#print axioms Sun28.WitnessHeight.union_power_dvd
#print axioms Sun28.WitnessHeight.union_discrepancies
#print axioms Sun28.WitnessHeight.ordinary_of_union
#print axioms Sun28.WitnessHeight.union_pos
#print axioms Sun28.WitnessHeight.member_radical_le
