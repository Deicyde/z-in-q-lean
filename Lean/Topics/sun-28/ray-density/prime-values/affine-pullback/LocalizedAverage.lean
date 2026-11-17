import AffineCubes

namespace Sun28.AffinePullback
open Finset
noncomputable section

/-- Number of choices of the two ordered interval indices in every direction. -/
def intervalMass (Js : List ℕ) : ℝ := (Js.prod:ℝ)^2

/-- The real cube average, equal to the 2^a-th power for a nonempty order-a box. -/
def boxAverage (n : ℕ) [NeZero n] (q : ℕ) (Js : List ℕ) (F : ZMod n → ℝ) : ℝ :=
  boxSum n q Js F / ((n:ℝ)*intervalMass Js)

theorem zero_interval {n : ℕ} [NeZero n] (q : ℕ) (Js : List ℕ) (F : ZMod n → ℝ)
    (hz : Js.prod = 0) : boxSum n q Js F = 0 := by
  induction Js generalizing F with
  | nil => simp at hz
  | cons J Js ih =>
    rw [List.prod_cons, Nat.mul_eq_zero] at hz
    rcases hz with head | tail
    · simp [boxSum, head]
    · simp [boxSum, fun G => ih G tail]

theorem recover_sum {n : ℕ} [NeZero n] (q : ℕ) (Js : List ℕ) (F : ZMod n → ℝ) :
    boxSum n q Js F = (n:ℝ)*intervalMass Js*boxAverage n q Js F := by
  by_cases hz : Js.prod=0
  · simp [zero_interval q Js F hz, intervalMass,hz]
  · have hn : (n:ℝ)≠0 := by exact_mod_cast NeZero.ne n
    have hM : intervalMass Js ≠ 0 := by simpa [intervalMass] using hz
    unfold boxAverage
    field_simp

theorem branch_factor (E n J a : ℕ) (hE : E ≠ 0) (hn : n≠0) (hJ : J ≠ 0)
    (k : Fin a→ℕ) (x : ℝ) :
    ((n:ℝ)*intervalMass (List.ofFn k)*x)/(((E*n:ℕ):ℝ)*intervalMass (List.replicate a J)) =
      (1/(E:ℝ)) * (∏ i : Fin a, ((k i:ℝ)/J)^2) * x := by
  have pr : (∏ i : Fin a, ((k i:ℝ)/J)^2) =
      (((∏ i : Fin a, k i:ℕ):ℝ)/(J:ℝ)^a)^2 := by
    rw [Finset.prod_pow, Finset.prod_div_distrib]
    simp
  rw [pr]
  simp only [intervalMass, List.prod_ofFn, List.prod_replicate, Nat.cast_pow, Nat.cast_mul]
  have e : (E:ℝ)≠0 := by exact_mod_cast hE
  have m : (n:ℝ)≠0 := by exact_mod_cast hn
  have j : (J:ℝ)≠0 := by exact_mod_cast hJ
  field_simp

/-- Glazer, v18, Lemma v18tz:lem:norm, displayed exact equality before (v18tz:eq:norm).
The zero-extension is literal. Each nonempty branch has its exact probability weight.
The zero weights for empty intervals have zero contribution by the chosen convention. -/
theorem localized_average {E n : ℕ} [NeZero n] [NeZero (E*n)] (hE : 0<E)
    (q J a : ℕ) (hJ : 0<J) (t : ZMod (E*n)) (F : ZMod n → ℝ) :
    boxAverage (E*n) q (List.replicate a J) (extend E n t F) =
      (1/(E:ℝ))*∑ rs : Fin a → Fin (E/E.gcd q),
        (∏ i : Fin a, ((lengthAt J (E/E.gcd q) (rs i):ℝ)/J)^2) *
          boxAverage n (q/E.gcd q) (List.ofFn (fun i => lengthAt J (E/E.gcd q) (rs i))) F := by
  unfold boxAverage
  rw [localized_sum hE, branches_sum, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rs _
  let k : Fin a→ℕ := fun i => lengthAt J (E/E.gcd q) (rs i)
  change boxSum n _ (List.ofFn k) F / _ = (1/(E:ℝ)) * ((∏ i : Fin a, ((k i:ℝ)/J)^2)*boxAverage n _ (List.ofFn k) F)
  rw [recover_sum (q/E.gcd q) (List.ofFn k) F]
  simpa only [mul_assoc] using
    branch_factor E n J a hE.ne' (NeZero.ne n) hJ.ne' k
      (boxAverage n (q/E.gcd q) (List.ofFn k) F)

end
end Sun28.AffinePullback
#print axioms Sun28.AffinePullback.zero_interval
#print axioms Sun28.AffinePullback.recover_sum
#print axioms Sun28.AffinePullback.localized_average
