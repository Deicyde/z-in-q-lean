import DivisorPower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Sun28.SieveTail.Uniform
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection
noncomputable section

/-- Explicit tau(|κ|v²) ≤ constant × N^(1/k) on the entire v²≤N range. -/
theorem divisor_uniform {κ : ℤ} (k : ℕ) (kp : 0 < k) {v N : ℕ} (vsmall : v^2≤N) :
    let m := (κ*(v:ℤ)^2).natAbs
    (m.divisors.card:ℝ) ≤ ((divisorConstant k*κ.natAbs:ℕ):ℝ)^((k:ℝ)⁻¹)*(N:ℝ)^((k:ℝ)⁻¹) := by
  let m := (κ*(v:ℤ)^2).natAbs
  change (m.divisors.card:ℝ)≤_
  by_cases zm : m=0
  · rw [zm]
    simp only [Nat.divisors_zero,Finset.card_empty,Nat.cast_zero]
    positivity
  have msmall : m ≤ κ.natAbs*N := by
    change (κ*(v:ℤ)^2).natAbs≤_
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using Nat.mul_le_mul_left κ.natAbs vsmall
  have h : m.divisors.card^k≤(divisorConstant k*κ.natAbs)*N := by
    exact (divisor_power k kp zm).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (divisorConstant k) msmall)
  have rn : 0≤((divisorConstant k*κ.natAbs:ℕ):ℝ) := Nat.cast_nonneg _
  rw [←Real.mul_rpow rn (Nat.cast_nonneg _)]
  apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (mul_nonneg rn (Nat.cast_nonneg _))
    (show 0<(k:ℝ) by exact_mod_cast kp)).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast h

variable {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}

/-- The Gaussian record norm envelope depends only on the long side N when
the short side satisfies v²≤N. -/
def commonRadius (N : ℕ) (i j : ↥(shifts A)) : ℕ :=
  2*Nat.sqrt ((1+max (offset (dilation A) i.val).natAbs (offset (dilation A) j.val).natAbs)*N)

theorem radius_le {N v : ℕ} (vsmall : v^2≤N) (i j : ↥(shifts A)) :
    radius N v i j ≤ commonRadius N i j := by
  unfold radius commonRadius
  apply Nat.mul_le_mul_left
  apply Nat.sqrt_le_sqrt
  rw [Nat.add_mul,one_mul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ vsmall) _

theorem harmonic_mono {a b : ℕ} (le : a≤b) : harmonic a≤harmonic b := by
  rw [harmonic_eq_sum_Icc,harmonic_eq_sum_Icc]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (le_refl _) le) (by intros;positivity)

/-- An upper bound independent of v with an arbitrary degree of divisor loss.
Only the primarity ray, the polynomial norm, and one chosen record per (u,v)
are used in this bound. -/
theorem offdiag_uniform {N V R : ℕ} (boxes : CountingBoxes A d H Y) (rp : 0 < R)
    (i j : ↥(shifts A)) (ij : i≠j) (vs : V^2≤N) (k : ℕ) (kp : 0 < k) :
    let B := commonRadius N i j
    let L := 2*(B:ℝ)+1
    let c := (gap i j).natAbs
    ((pairRecords boxes N V R i j).card:ℝ) ≤
      ((divisorConstant k*c:ℕ):ℝ)^((k:ℝ)⁻¹)*(N:ℝ)^((k:ℝ)⁻¹)*
        (8*(Nat.log 2 (c*N+2*B):ℝ)*(L/R+1))*(L*(harmonic B:ℝ)+B) := by
  let b := radius N V i j
  let B := commonRadius N i j
  let K := gap i j*(V:ℤ)^2
  let c := (gap i j).natAbs
  have bB : b≤B := radius_le vs i j
  have kN : K.natAbs≤c*N := by
    dsimp only [K,c]
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using Nat.mul_le_mul_left (gap i j).natAbs vs
  have low : Nat.log 2 (K.natAbs+2*b)≤Nat.log 2 (c*N+2*B) := Nat.log_mono_right (by omega)
  have tau := divisor_uniform (κ:=gap i j) k kp vs
  change ((K.natAbs.divisors.card:ℕ):ℝ)≤_ at tau
  have hrat := offdiag_records (N:=N) (V:=V) boxes rp i j ij
  dsimp only at hrat ⊢
  have h : ((pairRecords boxes N V R i j).card:ℝ) ≤ (K.natAbs.divisors.card:ℝ)*
      (8*(Nat.log 2 (K.natAbs+2*b):ℝ)*((2*(b:ℝ)+1)/R+1))*((2*(b:ℝ)+1)*(harmonic b:ℝ)+b) := by
    have lifted := (Rat.cast_le (K:=ℝ)).mpr hrat
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div,Rat.cast_add,Rat.cast_one,b,K] using lifted
  apply h.trans
  have harm : (harmonic b:ℝ)≤harmonic B := by exact_mod_cast harmonic_mono bB
  have br : (b:ℝ)≤B := by exact_mod_cast bB
  have logle : (Nat.log 2 (K.natAbs+2*b):ℝ)≤Nat.log 2 (c*N+2*B) := by exact_mod_cast low
  have hp : 0≤(harmonic b:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hP : 0≤(harmonic B:ℝ) := hp.trans harm
  change _ ≤ _*(_*(Nat.log 2 (c*N+2*B):ℝ)*((2*(B:ℝ)+1)/R+1))*((2*(B:ℝ)+1)*(harmonic B:ℝ)+B)
  gcongr

end
end Sun28.SieveTail.Uniform
#print axioms Sun28.SieveTail.Uniform.divisor_uniform
#print axioms Sun28.SieveTail.Uniform.radius_le
#print axioms Sun28.SieveTail.Uniform.harmonic_mono
#print axioms Sun28.SieveTail.Uniform.offdiag_uniform
