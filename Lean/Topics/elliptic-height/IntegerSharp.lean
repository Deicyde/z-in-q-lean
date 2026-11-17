import IntegerOrbit

namespace EllipticHeight.IntegerSharp

private abbrev q : Nat := 50*41^3

private theorem calibration {m : Nat} (hm : 16≤m) :
    16*(41^4)^m≤q^m := by
  have split : 16+(m-16)=m := by omega
  calc
    16*(41^4)^m = (16*(41^4)^16)*(41^4)^(m-16) := by
      rw [Nat.mul_assoc,←Nat.pow_add,split]
    _ ≤ q^16*q^(m-16) :=
      Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (by decide : 41^4≤q) _)
    _ = q^m := by rw [←Nat.pow_add,split]

theorem sharp (W : Nat → Nat) (n : Nat) (positive : ∀ i, 0<W i)
    (origin : W 0=1) (base : W 1=41^2) (second : W 2=4905889^2)
    (baseDouble : W 2^4≤W 4)
    (lower : ∀ j, j+2≤n → W (2*(j+1))^4≤W (4*(j+1)))
    (pair : ∀ j, j+2≤n → W (4*(j+1))*W 4≤16*(W (2*(j+2))*W (2*j))^2)
    (upper : W (2*n)≤16*W n^4) : (41^(n^2))^2≤W n := by
  by_cases small : n≤2
  · have cases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases cases with rfl|rfl|rfl
    · rw [origin]; decide
    · rw [base]; decide
    · rw [second]; decide
  have eb := IntegerOrbit.numerator_growth (fun i=>W (2*i)) q n (fun i=>positive _)
    (by simpa using origin) (by change q^2≤W 2; rw [second]; decide)
    (by change 16*q^8≤W 2^4; rw [second]; decide)
    (by simpa using baseDouble)
    (fun j hj=>by simpa only [←Nat.mul_assoc,show 2*2=4 by decide] using lower j hj)
    (fun j hj=>by simpa only [←Nat.mul_assoc,show 2*2=4 by decide] using pair j hj)
  change (q^(n^2))^2≤W (2*n) at eb
  rw [←Nat.pow_mul] at eb
  have s := Nat.pow_le_pow_left (by omega : 3≤n) 2
  have all := Nat.le_trans (calibration (m:=n^2*2) (by omega)) (Nat.le_trans eb upper)
  have expo : (41^4)^(n^2*2)=((41^(n^2))^2)^4 := by
    simp only [←Nat.pow_mul]
    congr 1
    grobner
  rw [expo] at all
  exact (Nat.pow_le_pow_iff_left (by decide : 4≠0)).mp
    (Nat.le_of_mul_le_mul_left all (by decide : 0<16))

end EllipticHeight.IntegerSharp
#print axioms EllipticHeight.IntegerSharp.sharp
