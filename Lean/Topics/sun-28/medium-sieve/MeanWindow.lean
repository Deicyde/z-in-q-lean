import FlexiblePair
import AverageBound
import LargeWindow

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Finset
open scoped Classical
noncomputable section

def gapConstant (A : Fin 3→ℚ) : ℕ :=
  univ.sup (fun z : ↥(shifts A)×↥(shifts A)=>(gap z.1 z.2).natAbs.divisors.card)+1

def growthBound (A : Fin 3→ℚ) (t : ℕ) := growth (envelope A) t+1

def meanConstant (A : Fin 3→ℚ) : ℝ :=
  (shifts A).card^2*(32*(envelope A+1:ℕ)^2:ℝ)*gapConstant A

private theorem harmonic_nonneg (W : ℕ) : 0≤(harmonic W:ℝ) := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum];exact sum_nonneg fun _ _=>by positivity

theorem average_pair (A : Fin 3→ℚ) (t W R : ℕ) (w : W≤ side t)
    (positive : 0<R) (within : R≤ side t) (i j : ↥(shifts A)) :
    (∑ v∈Icc 1 W,(pairBound (lengthAt t) v R i j:ℝ)) ≤
    32*(envelope A+1:ℕ)^2*(gapConstant A:ℝ)*W*(growthBound A t:ℝ)^4*((lengthAt t:ℝ)/R) := by
  let G:ℝ:=growthBound A t
  let D:ℝ:=(gap i j).natAbs.divisors.card
  let C:ℝ:=32*(envelope A+1:ℕ)^2*G^2*((lengthAt t:ℝ)/R)
  let f:=fun v:ℕ=>(((gap i j*(v:ℤ)^2).natAbs.divisors.card:ℕ):ℝ)
  have cap : W≤envelope A*lengthAt t := by
    have a : side t≤lengthAt t := by dsimp [lengthAt];nlinarith only [side_pos t,Nat.mul_le_mul_left (side t) (side_pos t)]
    exact (w.trans a).trans (Nat.le_mul_of_pos_left _ (by dsimp [envelope];positivity))
  have h : (harmonic W:ℝ)≤G := by
    apply (harmonic_le_one_add_log W).trans
    dsimp only [G,growthBound];push_cast;linarith only [(small_log _ t _ cap).2]
  have g1 : 1≤G := by dsimp [G,growthBound];exact_mod_cast Nat.le_add_left 1 _
  have sq := pow_le_pow_left₀ (harmonic_nonneg W) h 2
  have main := mean_gap (gap i j) W
  have count : (∑ v∈Icc 1 W,(f v+1)) ≤ (D+1)*W*G^2 := by
    rw [sum_add_distrib];simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    change (∑ v∈Icc 1 W,f v)+(W:ℝ)≤_
    have weighted:=mul_le_mul_of_nonneg_left sq (show 0≤D*(W:ℝ) by dsimp [D];positivity)
    have extra:=mul_le_mul_of_nonneg_left (one_le_pow₀ g1 (n:=2)) (Nat.cast_nonneg (α:=ℝ) W)
    change (∑ v∈Icc 1 W,f v)≤D*W*(harmonic W:ℝ)^2 at main
    nlinarith only [main,weighted,extra]
  have Dle : D+1≤(gapConstant A:ℝ) := by
    dsimp only [D,gapConstant];push_cast
    exact_mod_cast Nat.add_le_add_right (Finset.le_sup (f:=fun z : ↥(shifts A)×↥(shifts A)=>(gap z.1 z.2).natAbs.divisors.card) (Finset.mem_univ (i,j))) 1
  have non : 0≤C := by dsimp [C];positivity
  calc
    _ ≤ ∑ v∈Icc 1 W,(f v+1)*C := by
      apply sum_le_sum;intro v hv
      obtain hv' := (mem_Icc.mp hv).2.trans w
      apply (flexible_pair A t v R positive within hv' i j).trans_eq
      dsimp only [f,C,G,growthBound];ring
    _ ≤ (D+1)*W*G^2*C := by rw [←sum_mul];exact mul_le_mul_of_nonneg_right count non
    _ ≤ (gapConstant A:ℝ)*W*G^2*C := by gcongr
    _ = _ := by dsimp only [C,G];ring

theorem mean_window {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ t W R : ℕ)
    (w : W ≤ side t) (two : 2≤R) (within : R≤ side t)
    (hT : ∀ p∈T,p≤R) (hκ : ∀ p∈κ.primeFactors,p≤R) :
    removedMass T κ R (box (A:=A) (d:=d) (H:=H) (Y:=Y) (lengthAt t) W) ≤
      (meanConstant A*(growthBound A t:ℝ)^((shifts A).card+4)/(R:ℝ))*((lengthAt t:ℝ)*W) := by
  let G:ℝ:=growthBound A t
  let N:=lengthAt t
  let k:=(shifts A).card
  let C:ℝ:=32*(envelope A+1:ℕ)^2*(gapConstant A:ℝ)*W*G^4*((N:ℝ)/R)
  have upper : (∑ z∈indices A W,(pairBound N z.1 R z.2.1 z.2.2:ℝ)) ≤ (k^2:ℕ)*C := by
    rw [indices,sum_product,sum_comm]
    calc _ ≤ ∑ _ : ↥(shifts A)×↥(shifts A), C := by
           apply sum_le_sum;intro z _
           exact average_pair A t W R w (by omega) within z.1 z.2
         _ = _ := by simp [k,pow_two,Fintype.card_prod]
  have pos := side_pos t
  have vs : W^2≤N := Nat.pow_le_pow_left w 2
  have coeff:=Nat.mul_le_mul_left (maxCoefficient A) vs
  have bound : N+maxCoefficient A*W^2+1≤envelope A*N := by
    dsimp only [envelope];nlinarith only [coeff,show 1≤N from Nat.one_le_pow _ _ pos,Nat.zero_le (maxCoefficient A*N)]
  have weightLim : weightBound A N W≤G^k := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _))
    apply (small_log _ t _ bound).2.trans
    dsimp [G,growthBound];exact_mod_cast Nat.le_succ _
  have wn : 0≤weightBound A N W := pow_nonneg (Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)) _
  have non : (0:ℝ)≤(k^2:ℕ)*C := by dsimp [C,G];positivity
  have tail:=numerical_tail (A:=A) (d:=d) (H:=H) (Y:=Y) N W R two T κ hT hκ
  rw [Rat.cast_sum] at tail
  apply tail.trans
  apply (mul_le_mul_of_nonneg_left upper wn).trans
  apply (mul_le_mul_of_nonneg_right weightLim non).trans_eq
  dsimp only [C,G,k,meanConstant,N];rw [pow_add];push_cast;ring
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.average_pair
#print axioms Sun28.MediumSieve.mean_window
