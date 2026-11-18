module

public import CompactArithmetic
public import BlueprintReduction

/-! Arithmetic used to exclude an incorrect multiplication certificate.
The first inequality removes the auxiliary height denominator. The second
statement uses two divisibilities in succession to force both errors to vanish. -/

public section
namespace ZOverQ.ArithmeticComparison

/-- An integral height bound and a lower bound for the anchor give the required strict size bound. -/
theorem power_separation {B D M : Nat} (height : B ^ 2 < D * M ^ 18)
    (anchor : 5 ^ 9 * D ^ 26 < B ^ 16) : 5 * B ^ 4 < M ^ 52 := by
  exact CompactArithmetic.lucas_size height anchor

/-- Two divisible errors vanish when each is strictly smaller than its modulus,
with the second estimate required only after the first error vanishes. -/
theorem successive_separation (M : Nat) (u v : Int)
    (hu : ((M ^ 52 : Nat) : Int) ∣ u) (hv : ((M ^ 16 : Nat) : Int) ∣ v)
    (su : u.natAbs < M ^ 52) (sv : u = 0 → v.natAbs < M ^ 16) : u = 0 ∧ v = 0 := by
  exact BlueprintReduction.successive_separation M u v hu hv su sv

end ZOverQ.ArithmeticComparison
