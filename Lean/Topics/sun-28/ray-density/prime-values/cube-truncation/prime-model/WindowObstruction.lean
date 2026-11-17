import IntervalSquares

namespace Sun28.PrimeModel
open Finset Sun28.AffinePullback Sun28.PrimeTransfer Sun28.CubeTruncation
noncomputable section
variable {n : ℕ} [NeZero n]

/-- The left quarter lies outside the two simultaneous window conditions. -/
theorem left_quarter (μ : ℝ) (K b V N a : ℕ) (ha : 4*a < n) :
    centeredWindow (n:=n) μ K b V N (a:ZMod n) = -μ := by
  have lt : a < n := by omega
  have out : ¬ n ≤ 4*(a:ZMod n).val := by
    rw [ZMod.val_natCast_of_lt lt]
    omega
  unfold centeredWindow window
  rw [ite_eq_right (fun h => out h.2.2.1)]
  simp

/-- At least m base points contribute a common positive square to every pair of directions. -/
theorem constant_block {m J : ℕ} (fit : 16 * m ≤ n) (width : J ≤ m)
    (f : ZMod n → ℝ) (c : ℝ) (left : ∀ a : ℕ, 4*a < n → f (a:ZMod n)=c) :
    (m:ℝ)*((J:ℝ)*c^2)^2*(J:ℝ)^2 ≤ boxSum n 1 [J,J] f := by
  classical
  let start (k : ℕ) : ZMod n := m+k
  have inj : Set.InjOn start (range m : Set ℕ) := by
    intro k hk l hl eq
    have hk' : k < m := mem_range.mp hk
    have hl' : l < m := mem_range.mp hl
    change (m:ZMod n)+(k:ZMod n)=(m:ZMod n)+(l:ZMod n) at eq
    have e := congrArg ZMod.val (add_left_cancel eq)
    simp only [ZMod.val_natCast_of_lt (show k < n by omega),
      ZMod.val_natCast_of_lt (show l < n by omega)] at e
    exact e
  let total (i j : ℕ) (x : ZMod n) :=
    (∑ v ∈ range J, f (x+v)*f (x+v+((i:ℤ)-j:ℤ)))^2
  have block (i j : ℕ) (hi : i < J) (hj : j < J) (k : ℕ) (hk : k < m) :
      total i j (start k) = ((J:ℝ)*c^2)^2 := by
    have cell (v : ℕ) (hv : v∈range J) :
        f (start k+v)*f (start k+v+((i:ℤ)-j:ℤ))=c^2 := by
      have hv' := mem_range.mp hv
      have sub : j ≤ m+k+v+i := by omega
      have first : start k+(v:ZMod n)=((m+k+v:ℕ):ZMod n) := by simp [start]
      have second : start k+(v:ZMod n)+((i:ℤ)-j:ℤ)=((m+k+v+i-j:ℕ):ZMod n) := by
        rw [Nat.cast_sub sub]
        simp only [start, Nat.cast_add, Int.cast_sub, Int.cast_natCast]
        ring
      rw [second, first, left _ (by omega), left _ (by omega), pow_two]
    dsimp only [total]
    congr 1
    calc _ = ∑ _v ∈ range J, c^2 := sum_congr rfl cell
         _ = _ := by simp
  have lower (i j : ℕ) (hi : i < J) (hj : j < J) :
      (m:ℝ)*((J:ℝ)*c^2)^2 ≤ ∑ x : ZMod n, total i j x := by
    calc
      _ = ∑ k ∈ range m, total i j (start k) := by
        rw [sum_congr rfl (fun k hk => block i j hi hj k (mem_range.mp hk))]
        simp
      _ = ∑ x ∈ (range m).image start, total i j x := (sum_image inj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => sq_nonneg _)
  rw [two_squares]
  change _ ≤ ∑ i ∈ range J, ∑ j ∈ range J, ∑ x : ZMod n, total i j x
  calc
    _ = ∑ _i ∈ range J, ∑ _j ∈ range J, (m:ℝ)*((J:ℝ)*c^2)^2 := by simp; ring
    _ ≤ _ := sum_le_sum (fun i hi => sum_le_sum (fun j hj => lower i j (mem_range.mp hi) (mem_range.mp hj)))

/-- Uniform obstruction to a small order-two cube for the literal central prime window. -/
theorem centered_window_lower {J : ℕ} (large : 16 ≤ n) (width : 16*J ≤ n) (pos : 0 < J)
    (μ : ℝ) (K b V N : ℕ) :
    μ^4/32 ≤ boxAverage n 1 [J,J] (centeredWindow μ K b V N) := by
  have hm : J ≤ n/16 := by omega
  have lower := constant_block (n:=n) (m:=n/16) (J:=J) (by omega) hm
    (centeredWindow μ K b V N) (-μ) (left_quarter μ K b V N)
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hj : (0:ℝ) < J := by exact_mod_cast pos
  have cut : (n:ℝ) ≤ 32*((n/16:ℕ):ℝ) := by exact_mod_cast (show n ≤ 32*(n/16) by omega)
  have mass := mul_le_mul_of_nonneg_right cut (by positivity : 0 ≤ μ^4*(J:ℝ)^4)
  unfold boxAverage intervalMass
  simp only [List.prod_cons, List.prod_nil, Nat.mul_one, Nat.cast_mul]
  apply (le_div_iff₀ (by positivity)).2
  nlinarith only [lower,mass]

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.left_quarter
#print axioms Sun28.PrimeModel.constant_block
#print axioms Sun28.PrimeModel.centered_window_lower
