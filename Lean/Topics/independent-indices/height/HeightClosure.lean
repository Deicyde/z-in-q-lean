import Std

namespace IndependentIndices.HeightClosure

theorem vanish {d : Int} {q : Nat} (dvd : (q : Int) ∣ d) (small : d.natAbs < q) : d = 0 := by
  by_cases h : d = 0
  · exact h
  · have := Nat.le_of_dvd (Int.natAbs_pos.mpr h) (Int.ofNat_dvd_left.mp dvd)
    omega

set_option exponentiation.threshold 1024 in
theorem lucas_size {l c m : Nat} (root : l^2 < c*m^17)
    (anchor : 5^17*c^40 < l^12) : 5*l^4 < m^40 := by
  have hl : 0 < l := by cases l <;> simp_all
  have a : (5*l^4)^17*c^40 < (l^2)^40 := by
    calc
      (5*l^4)^17*c^40 = (5^17*c^40)*l^68 := by rw [Nat.mul_pow, ← Nat.pow_mul]; ac_rfl
      _ < l^12*l^68 := Nat.mul_lt_mul_of_pos_right anchor (Nat.pow_pos hl)
      _ = (l^2)^40 := by rw [← Nat.pow_add, ← Nat.pow_mul]
  have b : (l^2)^40 < c^40*(m^40)^17 := by
    calc
      _ < (c*m^17)^40 := Nat.pow_lt_pow_left root (by decide)
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  apply Nat.lt_of_not_ge
  intro contrary
  have bound := Nat.mul_le_mul_right (c^40) (Nat.pow_le_pow_left contrary 17)
  rw [Nat.mul_comm ((m^40)^17)] at bound
  omega

theorem numerator_size {l c m height : Nat} (root : l^2 < c*m^17)
    (separation : 2^17*c^10 < l^2) (scalar : height^17 ≤ l) :
    2*l*height < m^10 := by
  have hl : 0 < l := by cases l <;> simp_all
  have a : (2*l*height)^17*c^10 < (l^2)^10 := by
    calc
      _ = (2^17*c^10*height^17)*l^17 := by rw [Nat.mul_pow,Nat.mul_pow]; ac_rfl
      _ ≤ (2^17*c^10*l)*l^17 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ scalar)
      _ < (l^2*l)*l^17 := Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right separation hl) (Nat.pow_pos hl)
      _ = (l^2)^10 := by rw [← Nat.pow_succ, ← Nat.pow_add, ← Nat.pow_mul]
  have b : (l^2)^10 < c^10*(m^10)^17 := by
    calc
      _ < (c*m^17)^10 := Nat.pow_lt_pow_left root (by decide)
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  apply Nat.lt_of_not_ge
  intro contrary
  have bound := Nat.mul_le_mul_right (c^10) (Nat.pow_le_pow_left contrary 17)
  rw [Nat.mul_comm ((m^10)^17)] at bound
  omega

theorem two_defects {l c m height : Nat} {f n : Int} (root : l^2 < c*m^17)
    (anchor : 5^17*c^40 < l^12) (fbound : f.natAbs ≤ 5*l^4)
    (fdiv : ((m^40 : Nat) : Int) ∣ f) (ndiv : ((m^10 : Nat) : Int) ∣ n)
    (nbound : n.natAbs ≤ 2*l*height)
    (growth : f=0 → 2^17*c^10 < l^2 ∧ height^17 ≤ l) : f=0 ∧ n=0 := by
  have hf := vanish fdiv (Nat.lt_of_le_of_lt fbound (lucas_size root anchor))
  exact ⟨hf, vanish ndiv (Nat.lt_of_le_of_lt nbound (numerator_size root (growth hf).1 (growth hf).2))⟩

def constant (primes : List Nat) : Nat :=
  2^24 * (2^16 * primes.foldl (fun acc p => acc * (p*(p+1))) 1)^6 * 16^5 + 128

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 8192 in
theorem numerical_bounds :
    let a := 2*3^1474
    let j := constant [2,3,5,7,17]
    let c := 2 * constant [2,3,5,7,11,13,17,29,37,41,2399]
    5^17*c^40 < (a-1)^12 ∧ 80*j*19^17 < a ∧ 10000 < a-1 ∧
    2^17*c^10 < (2^4000)^2 := by decide

#print axioms lucas_size
#print axioms numerator_size
#print axioms two_defects
#print axioms numerical_bounds
end IndependentIndices.HeightClosure
