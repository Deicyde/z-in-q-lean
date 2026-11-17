import PrimeSummation
import Mathlib.NumberTheory.Chebyshev

namespace Sun28.PrimeMass
open Finset Sun28.SinglePrime
noncomputable section

/-- Chebyshev's estimate controls a single dyadic block. -/
theorem block (M : ℕ) (pos : 0 < M) :
    (∑ p ∈ places M (2*M), Real.log p / (p : ℝ)^2) ≤ 2*Real.log 4 / M := by
  have mp : (0 : ℝ) < M := by exact_mod_cast pos
  have inc : places M (2*M) ⊆ Nat.primesLE (2*M) := fun p hp =>
    Nat.mem_primesLE.mpr (mem_places.mp hp).2
  have logs := Chebyshev.theta_le_log4_mul_x (x:=((2*M : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at logs
  calc
    _ ≤ ∑ p ∈ places M (2*M), Real.log p / (M : ℝ)^2 := by
      apply sum_le_sum; intro p hp
      have le : (M : ℝ) ≤ p := by exact_mod_cast (mem_places.mp hp).1.le
      have lp : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (mem_places.mp hp).2.2.one_le)
      gcongr
    _ = (∑ p ∈ places M (2*M), Real.log p) / (M : ℝ)^2 := by rw [sum_div]
    _ ≤ (Real.log 4 * ((2*M : ℕ) : ℝ)) / (M : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (sum_le_sum_of_subset_of_nonneg inc fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)).trans logs
    _ = _ := by push_cast; field_simp

private theorem dyadic (L n : ℕ) (pos : 0 < L) :
    (∑ p ∈ places L (2^n*L), Real.log p / (p : ℝ)^2) ≤
      4*Real.log 4 * (1/(L:ℝ) - 1/((2^n*L : ℕ) : ℝ)) := by
  induction n with
  | zero => simp [places]
  | succ n ih =>
    let M := 2^n*L
    have mp : 0 < M := Nat.mul_pos (by positivity) pos
    have lm : L ≤ M := Nat.le_mul_of_pos_left L (by positivity)
    have join : places L (2*M) = places L M ∪ places M (2*M) := by
      ext p; simp only [mem_union,mem_places]
      constructor
      · rintro ⟨lo,hi,prime⟩
        by_cases h : p ≤ M
        · exact Or.inl ⟨lo,h,prime⟩
        · exact Or.inr ⟨Nat.lt_of_not_ge h,hi,prime⟩
      · rintro (⟨lo,hi,prime⟩ | ⟨lo,hi,prime⟩)
        · exact ⟨lo,hi.trans (show M≤2*M by omega),prime⟩
        · exact ⟨lm.trans_lt lo,hi,prime⟩
    have dis : Disjoint (places L M) (places M (2*M)) := by
      apply disjoint_left.mpr; intro p h h'; exact (mem_places.mp h').1.not_ge (mem_places.mp h).2.1
    rw [show 2^(n+1)*L = 2*M by dsimp [M]; ring,join,sum_union dis]
    apply (add_le_add ih (block M mp)).trans_eq
    change 4*Real.log 4*(1/(L:ℝ)-1/(M:ℝ)) + 2*Real.log 4/(M:ℝ) = _
    push_cast
    ring

/-- The bound is uniform in the last prime in the sum. -/
theorem reciprocal_prime_tail (L R : ℕ) (two : 2 ≤ L) :
    (∑ p ∈ places L R, 1/(p:ℝ)^2) ≤ (4*Real.log 4)/((L:ℝ)*Real.log L) := by
  have pos : 0 < L := by omega
  have lp : 0 < Real.log (L:ℝ) := Real.log_pos (by exact_mod_cast (show 1<L by omega))
  have major : R ≤ 2^R*L := (Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_right _ pos)
  have sub : places L R ⊆ places L (2^R*L) := fun p hp =>
    mem_places.mpr ⟨(mem_places.mp hp).1, (mem_places.mp hp).2.1.trans major,(mem_places.mp hp).2.2⟩
  have b : (∑ p ∈ places L R, Real.log p / (p:ℝ)^2) ≤ 4*Real.log 4/(L:ℝ) := by
    apply (sum_le_sum_of_subset_of_nonneg sub (fun p hp _ => div_nonneg
      (Real.log_nonneg (by exact_mod_cast (mem_places.mp hp).2.2.one_le)) (sq_nonneg _))).trans
    apply (dyadic L R pos).trans
    calc _ ≤ 4*Real.log 4*(1/(L:ℝ)) := mul_le_mul_of_nonneg_left
           (sub_le_self _ (by positivity : 0≤1/((2^R*L:ℕ):ℝ))) (by positivity)
         _ = _ := by ring
  rw [←div_div]
  apply (le_div_iff₀ lp).mpr
  rw [sum_mul]
  apply le_trans _ b
  apply sum_le_sum; intro p hp
  have logle := Real.log_le_log (by exact_mod_cast pos) (show (L:ℝ)≤p by exact_mod_cast (mem_places.mp hp).1.le)
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right logle (sq_nonneg _)
end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.block
#print axioms Sun28.PrimeMass.reciprocal_prime_tail
