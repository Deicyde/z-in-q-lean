import ScalarOctic

/-! A scalar height bound using the whole power in the signed Lucas sequence. -/
namespace Sun28.ScalarLucas
open Height Sun28.Ordinary Sun28.FixedPreparation Sun28.WitnessIndices
open Sun28.Forward Sun28.WitnessHeight Sun28.ScalarHeight Sun28.FiveMarkUnits
noncomputable section

/-- For c=|s-1| the power lower bound gives log B ≥ (c/4)log c. -/
theorem lucas_coordinate_growth (n : Fin 4 → ℤ) (zn : n 3 ≠ 0)
    (big : 12 ≤ scalarStep n) (zero : lucas (n 1) (n 2) (n 3) = 0) :
    ((scalarStep n:ℝ)/4)*Real.log (scalarStep n:ℝ) ≤ Real.log |(n 2:ℝ)| := by
  let s := (n 1).natAbs
  let c := scalarStep n
  have diff : c ≤ s+1 := by
    simpa [c,s,scalarStep,sub_eq_add_neg] using Int.natAbs_add_le (n 1) (-1:ℤ)
  have bigc : 12 ≤ c := big
  have seven : 7 ≤ (n 1).natAbs := by change 7 ≤ s; omega
  have h₁ : c ≤ 2*(s-4) := by omega
  have h₂ : c ≤ (s-1)^2 := by
    have h : 3 ≤ s-1 := by omega
    have e : c ≤ s-1+2 := by omega
    have prod := Nat.mul_le_mul_left (s-1) h
    rw [pow_two]
    omega
  have basePos : 0 < s-1 := by omega
  have baseOne : 1 ≤ s-1 := basePos
  have bpos : (0:ℝ) < (s-1:ℕ) := by exact_mod_cast basePos
  have lpos : 0 ≤ Real.log (s-1:ℕ) := Real.log_nonneg (by exact_mod_cast baseOne)
  have cmp := Real.log_le_log (show 0<(c:ℝ) by exact_mod_cast (show 0<c by omega))
    (show (c:ℝ)≤((s-1:ℕ):ℝ)^2 by exact_mod_cast h₂)
  rw [Real.log_pow] at cmp
  have e₁ : (c:ℝ)≤2*((s-4:ℕ):ℝ) := by exact_mod_cast h₁
  have pair : ((c:ℝ)/4)*Real.log (c:ℝ)≤((s-4:ℕ):ℝ)*Real.log (s-1:ℕ) := by
    calc
      _ ≤ ((c:ℝ)/4)*(2*Real.log (s-1:ℕ)) := mul_le_mul_of_nonneg_left (by simpa using cmp) (by positivity)
      _ = ((c:ℝ)/2)*Real.log (s-1:ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) lpos
  have power := signed_lucas_power (n 1) (n 2) (n 3) zn seven zero
  have realPower : ((s-1:ℕ):ℝ)^(s-4) ≤ ((n 2).natAbs:ℝ) := by exact_mod_cast power
  have logs := Real.log_le_log (pow_pos bpos _) realPower
  rw [Real.log_pow] at logs
  rw [←Int.cast_abs,←Nat.cast_natAbs]
  exact pair.trans logs

theorem scalar_lucas_growth (n : Fin 4 → ℤ) (zn : n 3 ≠ 0)
    (big : 12 ≤ scalarStep n) (zero : lucas (n 1) (n 2) (n 3) = 0) :
    ((scalarStep n:ℝ)/4)*Real.log (scalarStep n:ℝ) ≤ Real.log (indexSize n) := by
  have seven : 7≤(n 1).natAbs := by
    have h : scalarStep n≤(n 1).natAbs+1 := by
      simpa [scalarStep,sub_eq_add_neg] using Int.natAbs_add_le (n 1) (-1:ℤ)
    omega
  have powBound := signed_lucas_power (n 1) (n 2) (n 3) zn seven zero
  have positive : (0:ℝ) < |(n 2:ℝ)| := by
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast (pow_pos (show 0<(n 1).natAbs-1 by omega) _).trans_le powBound
  exact (lucas_coordinate_growth n zn big zero).trans
    (Real.log_le_log positive (by simp [indexSize]))

/-- The multiplier leaves enough room for the fixed additive logarithmic constant. -/
theorem multiplier_reserve (D K S : ℝ) : 12 ≤ Sun28.multiplier D K S ∧
    8*|K| < (Sun28.multiplier D K S:ℝ) ∧
    36*S^2*6 < (Sun28.multiplier D K S:ℝ) := by
  let y := (9*D)^2+2*(|K|+4)+(6*S)^2
  have ceil : y ≤ (⌈y⌉₊:ℝ) := Nat.le_ceil y
  have m : (Sun28.multiplier D K S:ℝ)=6*(2+(⌈y⌉₊:ℝ)) := by simp [Sun28.multiplier,y]
  refine ⟨by unfold Sun28.multiplier; omega,?_,?_⟩ <;>
    dsimp [y] at ceil <;> nlinarith only [m,ceil,sq_nonneg (9*D),sq_nonneg (6*S),abs_nonneg K]

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.lucas_coordinate_growth
#print axioms Sun28.ScalarLucas.scalar_lucas_growth
#print axioms Sun28.ScalarLucas.multiplier_reserve
