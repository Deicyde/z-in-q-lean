import LocalizedError
import PrimeWindow

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Sun28.PrimeTransfer Finset
noncomputable section

/-- The central no-wrap window takes the value zero at the group identity. -/
theorem window_zero (n : ℕ) [NeZero n] (K b V N : ℕ) :
    window K b V N (0 : ZMod n) = 0 := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp [window, hn.ne']

/-- The actual totient-normalized, centered one-class input used in the lower row. -/
def centeredWindow {n : ℕ} [NeZero n] (μ : ℝ) (K b V N : ℕ) (x : ZMod n) :=
 (V.totient:ℝ)/V * window K b V N x - μ

theorem window_bounds {n : ℕ} [NeZero n] (K b V N : ℕ) (hN : 0<N) (x : ZMod n) :
    0≤window K b V N x ∧ window K b V N x ≤ Real.log N := by
  have logN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  unfold window
  split
  next row =>
    let u:=b+V*x.val
    have lu : u≤N := row.2.1
    unfold classWeight
    split
    next ideal =>
      have prime : u.Prime := ideal.1
      have p : (0:ℝ)<u := by exact_mod_cast prime.pos
      exact ⟨Real.log_nonneg (by exact_mod_cast prime.one_le),Real.log_le_log p (by exact_mod_cast lu)⟩
    next => exact ⟨le_rfl,logN⟩
  next => exact ⟨le_rfl,logN⟩

/-- Exact zero-frequency criterion in the first moments. -/
theorem centered_mean_zero {n : ℕ} [NeZero n] (μ : ℝ) (K b V N : ℕ) :
    (∑ x : ZMod n, centeredWindow μ K b V N x) = 0 ↔
      (V.totient:ℝ)/V * (∑ x : ZMod n, window K b V N x) = (n:ℝ)*μ := by
  simp only [centeredWindow, Finset.sum_sub_distrib, ←Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul, sub_eq_zero]

theorem centered_bound {n : ℕ} [NeZero n] (μ : ℝ) (mu : μ∈Set.Icc (0:ℝ) 1)
    (K b V N : ℕ) (vp : 0<V) (hN : 0<N) (x : ZMod n) :
    |centeredWindow μ K b V N x| ≤ max 1 (Real.log N) := by
  obtain ⟨nonneg,upper⟩ := window_bounds K b V N hN x
  have vpos : (0:ℝ)<V := by exact_mod_cast vp
  have rate : (V.totient:ℝ)/V ≤ 1 := (div_le_one vpos).2 (by exact_mod_cast Nat.totient_le V)
  have rpos : (0:ℝ)≤V.totient/V := by positivity
  unfold centeredWindow
  apply abs_le.mpr
  constructor
  · have := mul_nonneg rpos nonneg
    have l := le_max_left (1:ℝ) (Real.log N)
    linarith [mu.2]
  · calc
      _ ≤ (V.totient:ℝ)/V * window K b V N x := sub_le_self _ mu.1
      _ ≤ window K b V N x := mul_le_of_le_one_left nonneg rate
      _ ≤ _ := upper.trans (le_max_right 1 _)

/-- Full explicit norm loss on the single Gaussian ray used in the lower-bound route.
All row and residue data are arbitrary. The function and the sup bound are the literal ones. -/
theorem centered_window_error {E n : ℕ} [NeZero n] [NeZero (E*n)]
    (hE:0<E) (q J a:ℕ) (large:E/E.gcd q≤J) (t:ZMod (E*n))
    (μ:ℝ) (mu:μ∈Set.Icc (0:ℝ) 1) (K b V N:ℕ) (vp:0<V) (hN:0<N) :
    let h:=E/E.gcd q
    let f:=centeredWindow (n:=n) μ K b V N
    |boxAverage (E*n) q (List.replicate a J) (extend E n t f) -
      (1/(h:ℝ))^a*boxAverage n (q/E.gcd q) (List.replicate a (J/h)) f/E|
      ≤ 4*a*(max 1 (Real.log N))^(2^a)/(E*J) :=
  localized_error hE q J a large t _ _ (le_max_of_le_left zero_le_one)
    (centered_bound μ mu K b V N vp hN)

theorem centered_window_transfer {E n : ℕ} [NeZero n] [NeZero (E*n)]
    (hE:0<E) (q J a:ℕ) (large:E/E.gcd q≤J) (t:ZMod (E*n))
    (μ:ℝ) (mu:μ∈Set.Icc (0:ℝ) 1) (K b V N:ℕ) (vp:0<V) (hN:0<N) (δ:ℝ)
    (downstairs: |boxAverage n (q/E.gcd q) (List.replicate a (J/(E/E.gcd q)))
      (centeredWindow μ K b V N)| ≤ δ) :
    |boxAverage (E*n) q (List.replicate a J) (extend E n t (centeredWindow μ K b V N))| ≤
      (1/(E:ℝ))*(1/(E/E.gcd q:ℕ):ℝ)^a*δ+4*a*(max 1 (Real.log N))^(2^a)/(E*J) := by
  let h:=E/E.gcd q
  let A:=boxAverage (E*n) q (List.replicate a J) (extend E n t (centeredWindow μ K b V N))
  let B:=boxAverage n (q/E.gcd q) (List.replicate a (J/h)) (centeredWindow μ K b V N)
  let C:=(1/(h:ℝ))^a/(E:ℝ)
  let Δ:=4*(a:ℝ)*(max 1 (Real.log N))^(2^a)/(E*J)
  have e:=centered_window_error hE q J a large t μ mu K b V N vp hN
  change |A-(1/(h:ℝ))^a*B/E|≤Δ at e
  have eq : (1/(h:ℝ))^a*B/E=C*B := by dsimp only [C]; ring
  rw [eq] at e
  have cpos : 0≤C := by dsimp only [C]; positivity
  have est : |C*B|≤C*δ := by rw [abs_mul,abs_of_nonneg cpos]; exact mul_le_mul_of_nonneg_left downstairs cpos
  have triangle := abs_add_le (A-C*B) (C*B)
  have total : |A|≤C*δ+Δ := by rw [sub_add_cancel] at triangle; linarith
  convert total using 1
  dsimp only [C]
  ring

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.window_bounds
#print axioms Sun28.CubeTruncation.centered_bound
#print axioms Sun28.CubeTruncation.centered_window_error
#print axioms Sun28.CubeTruncation.centered_window_transfer

#print axioms Sun28.CubeTruncation.window_zero
#print axioms Sun28.CubeTruncation.centered_mean_zero
