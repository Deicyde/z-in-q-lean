import SampleBoxes

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Finset
noncomputable section

/-- The same cube integrand is used at every interval length. -/
def cubeKernel (n q : ℕ) : (a : ℕ) → (ZMod n → ℝ) → (Fin a→ℕ×ℕ) → ZMod n → ℝ
  | 0, F, _, x => F x
  | a+1, F, s, x => cubeKernel n q a
      (fun y => F y * F (y+((q:ℤ)*(((s 0).1:ℤ)-(s 0).2):ℤ)))
      (fun i => s i.succ) x

theorem kernel_bound (n q a : ℕ) (F : ZMod n → ℝ) (M : ℝ) (pos:0≤M)
    (bound : ∀x, |F x| ≤ M) (s : Fin a→ℕ×ℕ) (x : ZMod n) :
    |cubeKernel n q a F s x| ≤ M^(2^a) := by
  induction a generalizing F M with
  | zero => simpa [cubeKernel] using bound x
  | succ a ih =>
    have hh := ih (fun y => F y * F (y+((q:ℤ)*(((s 0).1:ℤ)-(s 0).2):ℤ)))
      (M^2) (sq_nonneg M) (fun y => by
        rw [abs_mul, pow_two]
        exact mul_le_mul (bound _) (bound _) (abs_nonneg _) pos)
      (fun i => s i.succ)
    rw [←pow_mul, Nat.mul_comm 2, ←pow_succ] at hh
    exact hh

theorem sample_eq_box (n : ℕ) [NeZero n] (q a : ℕ) (m : Fin a→ℕ) (F : ZMod n→ℝ) :
    sampleSum n a m (cubeKernel n q a F) = boxSum n q (List.ofFn m) F := by
  induction a generalizing F with
  | zero => simp [sampleSum,cubeKernel,boxSum]
  | succ a ih =>
    simp only [sampleSum,List.ofFn_succ,boxSum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simpa only [cubeKernel,Fin.cons_zero,Fin.cons_succ] using
      ih (fun i => m i.succ) (fun y => F y * F (y+((q:ℤ)*((u:ℤ)-v):ℤ)))

theorem box_discard (n : ℕ) [NeZero n] (q a : ℕ) (k m : Fin a→ℕ) (inc : ∀i,k i≤m i)
    (F : ZMod n→ℝ) (M : ℝ) (pos : 0≤M) (bound : ∀ x, |F x|≤M) :
    |boxSum n q (List.ofFn m) F-boxSum n q (List.ofFn k) F| ≤
      ((n:ℝ)*(∏ i :Fin a,(m i:ℝ)^2)-n*(∏ i :Fin a,(k i:ℝ)^2))*M^(2^a) := by
  simpa only [sample_eq_box] using sample_discard n a k m inc _ _ (kernel_bound n q a F M pos bound)

theorem box_abs (n : ℕ) [NeZero n] (q a : ℕ) (k : Fin a→ℕ) (F : ZMod n→ℝ)
    (M : ℝ) (pos : 0≤M) (bound : ∀ x, |F x|≤M) :
    |boxSum n q (List.ofFn k) F| ≤ (n:ℝ)*(∏ i :Fin a,(k i:ℝ)^2)*M^(2^a) := by
  let K := cubeKernel n q a F
  let C := M^(2^a)
  have ub (s x) : |K s x|≤C := kernel_bound n q a F M pos bound s x
  have p1:=sample_nonneg n a k (fun s x=>C+K s x) (fun s x=>by have :=(abs_le.mp (ub s x)).1; linarith)
  have p2:=sample_nonneg n a k (fun s x=>C-K s x) (fun s x=>by have :=(abs_le.mp (ub s x)).2; linarith)
  have eq2 : sampleSum n a k (fun s x=>C-K s x)+sampleSum n a k K =
    sampleSum n a k (fun _ _=>C) := by
    rw [←sample_add]
    simp
  have eq1:= sample_add n a k (fun _ _=>C) K
  rw [sample_const] at eq1 eq2
  rw [←sample_eq_box]
  change |sampleSum n a k K| ≤ _*C
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.kernel_bound
#print axioms Sun28.CubeTruncation.sample_eq_box
#print axioms Sun28.CubeTruncation.box_discard
#print axioms Sun28.CubeTruncation.box_abs
