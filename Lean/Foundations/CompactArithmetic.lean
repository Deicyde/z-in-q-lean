module

public import Std

@[expose] public section

namespace CompactArithmetic

/-- Removing the guaranteed dyadic and triadic factor from the scalar estimate. -/
theorem scalar_radical_dvd_cofactor {M A₀ A : Nat}
    (coprime : Nat.Coprime M A₀) (anchor : A₀ ∣ A) (scalar : M^32 ∣ A) :
    M^32 ∣ A / A₀ :=
  Nat.dvd_div_of_mul_dvd ((coprime.pow_left 32).symm.mul_dvd_of_dvd_of_dvd anchor scalar)

set_option exponentiation.threshold 512 in
/-- Eliminate all fractional powers from the first integer separation. -/
theorem lucas_size {B D M : Nat} (height : B^2 < D*M^18)
    (anchor : 5^9 * D^26 < B^16) : 5*B^4 < M^52 := by
  have hb : 0 < B := by
    cases B with
    | zero => simp at anchor
    | succ n => exact Nat.zero_lt_succ n
  have low : (5*B^4)^9 * D^26 < (B^2)^26 := by
    calc (5*B^4)^9 * D^26 = (5^9 * D^26) * B^36 := by
           rw [Nat.mul_pow, ← Nat.pow_mul]; ac_rfl
         _ < B^16 * B^36 := Nat.mul_lt_mul_of_pos_right anchor (Nat.pow_pos hb)
         _ = (B^2)^26 := by rw [← Nat.pow_add, ← Nat.pow_mul]
  have high : (B^2)^26 < D^26*(M^52)^9 := by
    calc (B^2)^26 < (D*M^18)^26 := Nat.pow_lt_pow_left height (by decide)
         _ = D^26*(M^52)^9 := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  apply Nat.lt_of_not_ge
  intro contrary
  have rev := Nat.mul_le_mul_right (D^26) (Nat.pow_le_pow_left contrary 9)
  rw [Nat.mul_comm ((M^52)^9)] at rev
  omega

def heightBound (k : Nat) (exceptions : List Nat) : Nat :=
  2^26 * (2304 * (2^32*3^12) * k *
    exceptions.foldl (fun acc p => acc * (p*(p+1))) 1)^6 + 128

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 8192 in
/-- Exact checks in Lean's kernel of the two size comparisons for S=3^4096. -/
theorem anchor_thresholds :
    let A₀ := 2*3^1023
    let D := heightBound 16 [2,3,5,7,11,13,17,29,37,41,2399]
    let J := heightBound 64 [2,3,5,7,11,13,17,4801]
    2^383*5^9*(2*D)^26 < A₀^16 ∧ 2^800*(4*J) < A₀ := by decide

end CompactArithmetic

#print axioms CompactArithmetic.scalar_radical_dvd_cofactor
#print axioms CompactArithmetic.lucas_size
#print axioms CompactArithmetic.anchor_thresholds
