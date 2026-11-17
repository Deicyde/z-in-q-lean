import CubeBounds

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Finset
noncomputable section

theorem squares_by_residue (h J : ℕ) (hh : 0<h) :
    ∑ r : Fin h, (lengthAt J h r : ℝ)^2 =
      (h:ℝ)*(J/h:ℕ)^2+(2*(J/h:ℕ)+1)*(J%h:ℕ) := by
  let k:=J/h
  let b:=J%h
  have hb : b<h := Nat.mod_lt _ hh
  change (∑ r:Fin h, (lengthAt J h r:ℝ)^2)=(h:ℝ)*(k:ℝ)^2+(2*(k:ℝ)+1)*(b:ℝ)
  rw [Fin.sum_univ_eq_sum_range (fun x => (lengthAt J h x:ℝ)^2)]
  have decomp {x : ℕ} : x≥b → lengthAt J h x = k := by
    intro hx
    exact by simp [lengthAt,k,show ¬x<J%h from by omega]
  have below {x : ℕ} : x<b → lengthAt J h x = k+1 := by
    intro hx
    exact by simp [lengthAt,k,show x<J%h from hx]
  have he : h=b+(h-b) := by omega
  rw [show range h=range (b+(h-b)) from congrArg range he, Finset.sum_range_add]
  have low : (∑ x∈range b, (lengthAt J h x:ℝ)^2)= b*((k:ℝ)+1)^2 := by
    calc
      _=∑ _x∈range b, ((k:ℝ)+1)^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [below (Finset.mem_range.mp hx),Nat.cast_add,Nat.cast_one]
      _=_ := by simp [nsmul_eq_mul]
  have high : (∑ x∈range (h-b), (lengthAt J h (b+x):ℝ)^2)=(h-b:ℕ)*(k:ℝ)^2 := by
    calc
      _=∑ _x∈range (h-b), (k:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [decomp (by omega)]
      _=_ := by simp [nsmul_eq_mul]
  rw [low, high, Nat.cast_sub hb.le]
  ring

theorem product_branch_count (a h : ℕ) (G : Fin h → ℝ) :
    ∑ rs : Fin a→Fin h, ∏ i : Fin a, G (rs i) = (∑ r : Fin h, G r)^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← (Fin.consEquiv (fun _ :Fin (a+1)=>Fin h)).sum_comp (fun rs=>∏ i:Fin (a+1),G (rs i))]
    rw [Fintype.sum_prod_type]
    change (∑ r : Fin h, ∑ rs : Fin a→Fin h, ∏ i : Fin (a+1), G ((Fin.cons r rs : Fin (a+1) → Fin h) i)) = _
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ←Finset.mul_sum, ih]
    rw [←Finset.sum_mul, pow_succ']
  
theorem interval_sum (J h a : ℕ) (hh : 0<h) :
    (∑ rs : Fin a→Fin h, ∏ i:Fin a, (lengthAt J h (rs i):ℝ)^2) =
      ((h:ℝ)*(J/h:ℕ)^2+(2*(J/h:ℕ)+1)*(J%h:ℕ))^a :=
  (product_branch_count a h (fun r=>(lengthAt J h r:ℝ)^2)).trans (by rw [squares_by_residue h J hh])

theorem interval_ge (J h : ℕ) (r : Fin h) : J/h≤lengthAt J h r := by
  simp [lengthAt]

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.squares_by_residue
#print axioms Sun28.CubeTruncation.product_branch_count
#print axioms Sun28.CubeTruncation.interval_sum
