import IntervalFibres

namespace Sun28.AffinePullback
open Finset
noncomputable section

/-- Unnormalized base sum of the iterated difference product. The order is the
length of the list and every interval is counted with both independent copies. -/
def boxSum (n : ℕ) [NeZero n] (q : ℕ) : List ℕ → (ZMod n → ℝ) → ℝ
  | [], F => ∑ x : ZMod n, F x
  | J::Js, F => ∑ i ∈ range J, ∑ j ∈ range J, boxSum n q Js
      (fun x => F x * F (x+((q:ℤ)*((i:ℤ)-j):ℤ)))

theorem boxSum_zero (n : ℕ) [NeZero n] (q : ℕ) (Js : List ℕ) :
    boxSum n q Js 0 = 0 := by
  induction Js with
  | nil => simp [boxSum]
  | cons J Js ih =>
    have hz : boxSum n q Js (fun _ => 0) = 0 := ih
    simp [boxSum, hz]

theorem sum_extend {E n : ℕ} [NeZero n] [NeZero (E*n)] (hE : 0<E)
    (t : ZMod (E*n)) (F : ZMod n → ℝ) :
    ∑ y : ZMod (E*n), extend E n t F y = ∑ x : ZMod n, F x := by
  classical
  let s := (univ : Finset (ZMod n)).image (affine E n t)
  have hs : ∑ y ∈ s, extend E n t F y = ∑ y : ZMod (E*n), extend E n t F y := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    apply extend_eq_zero
    rintro ⟨x,rfl⟩
    exact hy (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  rw [←hs, show s = _ from rfl, Finset.sum_image (affine_injective hE n t).injOn]
  simp only [extend_affine hE]

/-- Sum over all choices of a residue in each successive coordinate. -/
def branches (h : ℕ) : (a : ℕ) → ((Fin a → Fin h) → ℝ) → ℝ
  | 0, K => K Fin.elim0
  | a+1, K => ∑ r : Fin h, branches h a (fun rs => K (Fin.cons r rs))

theorem branches_sum (h a : ℕ) (K : (Fin a → Fin h) → ℝ) :
    branches h a K = ∑ rs : Fin a → Fin h, K rs := by
  induction a with
  | zero => simp [branches, Unique.eq_default (Fin.elim0 : Fin 0 → Fin h)]
  | succ a ih =>
    simp only [branches, ih]
    rw [← Fintype.sum_prod_type']
    exact (Fin.consEquiv (fun _ : Fin (a+1) => Fin h)).sum_comp K

theorem branches_comm (h a J : ℕ) (K : ℕ → (Fin a → Fin h) → ℝ) :
    (∑ i ∈ range J, branches h a (K i)) =
      branches h a (fun rs => ∑ i ∈ range J, K i rs) := by
  simp only [branches_sum]
  rw [Finset.sum_comm]

theorem localized_sum {E n : ℕ} [NeZero n] [NeZero (E*n)]
    (hE : 0<E) (q J a : ℕ) (t : ZMod (E*n)) (F : ZMod n → ℝ) :
    boxSum (E*n) q (List.replicate a J) (extend E n t F) =
      branches (E/E.gcd q) a (fun rs => boxSum n (q/E.gcd q)
        (List.ofFn (fun i => lengthAt J (E/E.gcd q) (rs i))) F) := by
  classical
  let h := E/E.gcd q
  have hh : 0<h := Nat.div_pos (Nat.le_of_dvd hE (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_left _ hE)
  induction a generalizing F with
  | zero => simpa [boxSum,branches] using sum_extend hE t F
  | succ a ih =>
    simp only [List.replicate_succ, boxSum]
    have term (i j : ℕ) :
        boxSum (E*n) q (List.replicate a J) (fun y => extend E n t F y *
          extend E n t F (y+((q:ℤ)*((i:ℤ)-j):ℤ))) =
        if i%h=j%h then boxSum (E*n) q (List.replicate a J)
          (extend E n t (fun x => F x * F (x+((q/E.gcd q:ℕ)*((i/h:ℕ)-(j/h:ℕ):ℤ):ℤ)))) else 0 := by
      by_cases hij : i%h=j%h
      · rw [ite_eq_left hij]
        congr 1
        funext y
        simpa only [ite_eq_left (show i%(E/E.gcd q)=j%(E/E.gcd q) from hij)]
          using derivative hE n q i j t F y
      · rw [ite_eq_right hij, ← boxSum_zero (E*n) q (List.replicate a J)]
        congr 1
        funext y
        change _ = (0 : ℝ)
        simpa only [ite_eq_right (show ¬i%(E/E.gcd q)=j%(E/E.gcd q) from hij)]
          using derivative hE n q i j t F y
    simp_rw [term]
    rw [pair_fibre_sum J h hh (fun u v => boxSum (E*n) q (List.replicate a J)
      (extend E n t (fun x => F x * F (x+((q/E.gcd q:ℕ)*((u:ℤ)-v):ℤ))))), ← Fin.sum_univ_eq_sum_range]
    simp only [branches]
    apply Finset.sum_congr rfl
    intro r _
    simp_rw [ih]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, boxSum]
    rw [← branches_comm h a (lengthAt J h r)]
    apply Finset.sum_congr rfl
    intro u _
    exact branches_comm h a _ _

end
end Sun28.AffinePullback
#print axioms Sun28.AffinePullback.sum_extend
#print axioms Sun28.AffinePullback.branches_sum
#print axioms Sun28.AffinePullback.localized_sum
