import LocalFactors
import PrimeTrace

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult NumberField IsDedekindDomain Sun28.ScalarTrace
open scoped NumberField
noncomputable section

private theorem val_order_iff {w : FinitePlace K0} {x y : K0} (xn : x≠0) (yn : y≠0) :
    discreteOrder (w.maximalIdeal.valuation K0) x ≤ discreteOrder (w.maximalIdeal.valuation K0) y ↔ w y ≤ w x := by
  have vx := (w.maximalIdeal.valuation K0).ne_zero_iff.mpr xn
  have vy := (w.maximalIdeal.valuation K0).ne_zero_iff.mpr yn
  change ((if w.maximalIdeal.valuation K0 x=0 then ⊤ else ((-WithZero.log (w.maximalIdeal.valuation K0 x):ℤ):WithTop ℤ)) ≤
    (if w.maximalIdeal.valuation K0 y=0 then ⊤ else ((-WithZero.log (w.maximalIdeal.valuation K0 y):ℤ):WithTop ℤ))) ↔ _
  rw [ite_eq_right vx,ite_eq_right vy,WithTop.coe_le_coe,neg_le_neg_iff,WithZero.log_le_log vy vx]
  rw [←FinitePlace.norm_embedding_eq w y,←FinitePlace.norm_embedding_eq w x,
      FinitePlace.norm_embedding',FinitePlace.norm_embedding']
  exact (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal _)).le_iff_le.symm

private theorem delta_order_nonneg (u : AddValuation K0 (WithTop ℤ)) :
    0 ≤ u delta := by
  have natInt (k : ℕ) : 0 ≤ u (k:K0) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ]; exact u.map_le_add ih (by simp)
  have sqrt : 0 ≤ u sqrt2 := by
    obtain ⟨a,ha⟩ := Scalar.finite_order u sqrt2_ne_zero
    have two : 0 ≤ u (2:K0) := natInt 2
    rw [←sqrt2_sq,u.map_pow,ha] at two
    have ci : 0≤2*a := by exact_mod_cast two
    rw [ha]; exact WithTop.coe_le_coe.mpr (by omega)
  rw [delta_eq]
  exact u.map_le_sub (natInt 3) sqrt

/-- On a finite place with a pole in an odd coordinate, every companion has
absolute value at least |δ|². This avoids classifying the exceptional prime. -/
theorem finite_pole_companion (w : FinitePlace K0) {m k : ℤ} (odd : Odd m) (nk : k≠0)
    (pole : 1 < w (indexX m)) : w delta^2 ≤ w (indexX k) := by
  let u := discreteOrder (w.maximalIdeal.valuation K0)
  have nm : m≠0 := by obtain ⟨l,el⟩ := odd; omega
  have low : u (indexX m) < 0 := by
    rw [← u.map_one,lt_iff_not_ge]
    intro h
    have ab := (val_order_iff (w:=w) one_ne_zero (indexX_nonzero nm)).mp h
    rw [map_one] at ab
    exact (not_le.mpr pole) ab
  have d0 := delta_order_nonneg u
  have d : 0 ≤ u (-delta^2) := by
    rw [u.map_neg,u.map_pow]; exact nsmul_nonneg d0 2
  have v := local_order_separation u d m k odd nk low
  have ab := (val_order_iff (w:=w) (indexX_nonzero nk) (neg_ne_zero.mpr (pow_ne_zero 2 delta_ne_zero))).mp v
  simpa only [map_neg_eq_map,map_pow] using ab

end
end Sun28.Ordinary
#print axioms Sun28.Ordinary.finite_pole_companion
