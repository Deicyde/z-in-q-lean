import Std

namespace BinaryDivisionDegree

/-- Twice the z-degree of the even and odd slot polynomials, with the x-power
that remains in the inverse-denominator slot. The index-zero denominator vanishes. -/
def Fits (n a b : Nat) : Prop := 2*a ≤ n^2 ∧ 2*b+1 ≤ n^2

theorem one : Fits 1 0 0 := by unfold Fits; decide

/-- Bounds for ((A²+zB²)²,4AB(A²−zB²)). -/
theorem doubling (n a b : Nat) (H : Fits n a b) :
    let d := max (2*a) (1+2*b)
    Fits (2*n) (2*d) (a+b+d) := by
  intro d
  obtain ⟨hA,hB⟩:=H
  have hd : d≤n^2 := by dsimp [d]; omega
  have eq : (2*n)^2=4*n^2 := by grind
  unfold Fits; rw [eq]
  constructor <;> omega

/-- Bounds for ((AC+zBE)²,(AE−BC)²) from consecutive inputs. The unit saved
by the odd sum n²+(n+1)² is essential. -/
theorem odd (n a b c e : Nat) (H : Fits n a b) (J : Fits (n+1) c e) :
    Fits (2*n+1) (2*max (a+c) (1+b+e)) (2*max (a+e) (b+c)) := by
  obtain ⟨hA,hB⟩:=H
  obtain ⟨hC,hE⟩:=J
  have total : n^2+(n+1)^2=2*(n^2+n)+1 := by grind
  have rowA : max (a+c) (1+b+e) ≤ n^2+n := by omega
  have rowB : max (a+e) (b+c) ≤ n^2+n := by omega
  have eq : (2*n+1)^2=4*(n^2+n)+1 := by grind
  unfold Fits; rw [eq]
  constructor <;> omega

/-- Reversal therefore has no negative powers of x. -/
theorem reversal (n a b i j : Nat) (H : Fits n a b) (hi : i≤a) (hj : j≤b) :
    2*i ≤ n^2 ∧ 2*j ≤ n^2-1 := by
  obtain ⟨hA,hB⟩:=H
  omega

/-- The value at z=0 of the denominator slot of each recursion. -/
theorem leading_constants (n : Int) :
    4*n^2=(2*n)^2 ∧ (((n+1)^2-n^2)^2)=(2*n+1)^2 := by
  constructor <;> grobner

#print axioms doubling
#print axioms odd
#print axioms reversal
#print axioms leading_constants
end BinaryDivisionDegree
