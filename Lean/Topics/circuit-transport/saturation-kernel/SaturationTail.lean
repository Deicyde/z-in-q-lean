import Std

namespace CircuitTransport.Saturation

/-- The norm of c + d√2 written in the integral basis 1, √2. -/
def norm (c d : Int) : Int := c^2 - 2*d^2

/-- δ = 3 - √2, so x - δ = (c-3) + (d+1)√2. -/
def minusNorm (c d : Int) : Int := norm (c-3) (d+1)

/-- x + δ = (c+3) + (d-1)√2. -/
def plusNorm (c d : Int) : Int := norm (c+3) (d-1)

theorem norm_sum (c d : Int) :
    plusNorm c d + minusNorm c d = 2*norm c d + 14 := by
  unfold plusNorm minusNorm norm
  grobner

theorem norm_difference (c d : Int) :
    plusNorm c d - minusNorm c d = 4*(3*c+2*d) := by
  unfold plusNorm minusNorm norm
  grobner

/-- The positive magnitudes allowed for an integer square dividing each of the three bounds. -/
def SquareDivisors (q : Int) : Prop :=
  (q ∣ 49 → q ∈ [1,49]) ∧ (q ∣ 196 → q ∈ [1,4,49,196]) ∧
  (q ∣ 784 → q ∈ [1,4,16,49,196,784])

private theorem abs_square (r : Int) : ((r.natAbs*r.natAbs : Nat) : Int) = r^2 := by
  rw [Int.natAbs_mul_self]
  grobner

private theorem bounded_root {r : Int} {n : Nat} (hn : 0 < n) (upper : n ≤ 784)
    (divides : r^2 ∣ (n : Int)) : r.natAbs < 29 := by
  rw [← abs_square] at divides
  have bound := Nat.le_of_dvd hn (Int.ofNat_dvd.mp divides)
  by_cases h : 29 ≤ r.natAbs
  · have large := Nat.mul_le_mul h h
    omega
  · omega

theorem square_divisor_lists (r : Int) : SquareDivisors (r^2) := by
  by_cases small : r.natAbs < 29
  · have table : ∀ k : Fin 29, SquareDivisors ((k.val*k.val : Nat) : Int) := by
      unfold SquareDivisors
      decide
    rw [← abs_square]
    exact table ⟨r.natAbs,small⟩
  · exact ⟨fun h => (small (bounded_root (n:=49) (by decide) (by decide) h)).elim,
           fun h => (small (bounded_root (n:=196) (by decide) (by decide) h)).elim,
           fun h => (small (bounded_root (n:=784) (by decide) (by decide) h)).elim⟩

/-- The three signed divisor lists in the order N(x), N(x-δ), N(x+δ). -/
def Admissible (x y z : Int) : Prop :=
  x ∈ [-1,-49] ∧ y ∈ [-1,-4,-49,-196] ∧ z ∈ [1,4,16,49,196,784]

theorem unique_norms {x y z : Int} (allowed : Admissible x y z)
    (sum : z+y=2*x+14) : x= -1 ∧ y= -4 ∧ z=16 := by
  simp only [Admissible, List.mem_cons, List.not_mem_nil, or_false] at allowed
  omega

theorem unique_coordinates {c d : Int} (unitNorm : c^2-2*d^2= -1)
    (linear : 3*c+2*d=5) : c=1 ∧ d=1 := by
  have factored : (c-1)*(7*c-23)=0 := by grobner
  rcases Int.mul_eq_zero.mp factored with h | h <;> omega

/-- The integral abscissa is 1 + √2 once the geometric argument gives the signed norm lists. -/
theorem saturation_tail {c d : Int}
    (allowed : Admissible (norm c d) (minusNorm c d) (plusNorm c d)) : c=1 ∧ d=1 := by
  obtain ⟨hx,hm,hp⟩ := unique_norms allowed (norm_sum c d)
  have diff := norm_difference c d
  rw [hp,hm] at diff
  exact unique_coordinates hx (by omega)

/-- The same conclusion directly from the signed integer squares and the three norm divisibilities. -/
theorem saturation_from_signed_squares {c d u v w : Int}
    (hx : norm c d= -(u^2)) (hm : minusNorm c d= -(v^2)) (hp : plusNorm c d=w^2)
    (du : u^2 ∣ 49) (dv : v^2 ∣ 196) (dw : w^2 ∣ 784) : c=1 ∧ d=1 := by
  have hu := (square_divisor_lists u).1 du
  have hv := (square_divisor_lists v).2.1 dv
  have hw := (square_divisor_lists w).2.2 dw
  apply saturation_tail
  rw [hx,hm,hp]
  simp only [Admissible, List.mem_cons, List.not_mem_nil, or_false] at *
  omega

#print axioms norm_sum
#print axioms norm_difference
#print axioms square_divisor_lists
#print axioms unique_norms
#print axioms unique_coordinates
#print axioms saturation_tail
#print axioms saturation_from_signed_squares

end CircuitTransport.Saturation
