import PatternSelection

namespace Sun28.PrimeMass
open Filter Finset Topology Sun28.ContactFactors Sun28.SinglePrime Sun28.FinitePattern
open Sun28.WeightedSelection Sun28.MediumSieve
noncomputable section
open scoped Classical

/-- A failure on arbitrarily narrow fixed rows would give a single short width of counterexamples. -/
theorem fixed_rows {P : ℕ → ℕ → Prop}
    (every : ∀ w : ℕ → ℕ, (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (w N : ℝ)^2 ≤ ε*N) →
      ∀ᶠ N : ℕ in atTop, P N (w N)) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ N : ℕ in atTop, P N (rowWidth j N) := by
  classical
  by_contra! fail
  have pick (k : ℕ) : ∃ j ≥ k, ∀ B : ℕ, ∃ N ≥ B, ¬ P N (rowWidth j N) := by
    obtain ⟨j,large,h⟩ := fail k
    exact ⟨j,large,frequently_atTop.mp h⟩
  choose j stage bad using pick
  choose counter large wrong using bad
  let N : ℕ → ℕ := Nat.rec (counter 0 0) fun k prev => counter (k+1) (prev+1)
  have incr : StrictMono N := strictMono_nat_of_lt_succ fun k => large (k+1) (N k+1)
  have fails (k : ℕ) : ¬ P (N k) (rowWidth (j k) (N k)) := by
    cases k with
    | zero => exact wrong 0 0
    | succ k => exact wrong (k+1) (N k+1)
  let level (b : ℕ) : ℕ := @Nat.findGreatest (fun (i : ℕ) => N i ≤ b) (fun i => Nat.decLe (N i) b) b
  let w (b : ℕ) := rowWidth (j (level b)) b
  have agrees (k : ℕ) : w (N k) = rowWidth (j k) (N k) := by
    have eq : level (N k) = k := (@Nat.findGreatest_eq_iff k (N k) (fun i => N i ≤ N k) (fun i => Nat.decLe (N i) (N k))).mpr
      ⟨incr.id_le k, fun _ => le_rfl, fun i hi _ => (incr hi).not_ge⟩
    simp only [w,eq]
  have short (ε : ℝ) (ep : 0 < ε) : ∀ᶠ b : ℕ in atTop, (w b : ℝ)^2 ≤ ε*b := by
    obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
    apply eventually_atTop.mpr
    refine ⟨N k,fun b hb => ?_⟩
    have ki : k ≤ level b := @Nat.le_findGreatest k (fun i => N i ≤ b) (fun i => Nat.decLe (N i) b) b ((incr.id_le k).trans hb) hb
    have jj : (k:ℝ) ≤ j (level b) := by exact_mod_cast ki.trans (stage _)
    have low : 1 ≤ ε*((j (level b):ℝ)+1) := by
      nlinarith only [(div_lt_iff₀ ep).mp hk, mul_le_mul_of_nonneg_left jj ep.le,ep]
    have area := row_area (j (level b)) b
    dsimp only [w]
    nlinarith only [mul_le_mul_of_nonneg_left area ep.le,
      mul_le_mul_of_nonneg_right low (sq_nonneg (rowWidth (j (level b)) b : ℝ))]
  obtain ⟨B,hB⟩ := eventually_atTop.mp (every w short)
  exact fails B ((agrees B) ▸ hB (N B) (incr.id_le B))

theorem fixed_pattern {A : Fin 3 → ℚ} {K L d κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (hT : ∀ p ∈ T,p ≤ K) (hκ : ∀ p ∈ κ.primeFactors,p ≤ K) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ᶠ t : ℕ in atTop,
      let N := lengthAt t
      let W := rowWidth j N
      patternMass A d K L N W ≤
        mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W) := by
  obtain ⟨J,rows⟩ := fixed_rows (P:=fun N W => patternMass A d K L N W ≤ mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W)) (fun w short =>
    eventually_pattern_le_main (A:=A) (L:=L) (d:=d) (H:=H) (Y:=Y) hT hκ w short)
  exact ⟨J,fun j hj => length_grows.eventually (rows j hj)⟩
end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.fixed_rows
#print axioms Sun28.PrimeMass.fixed_pattern
