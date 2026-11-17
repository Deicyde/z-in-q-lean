import Std

namespace EllipticHeight.IntegerOrbit

/-- Induction on successive ratios proves the quadratic barrier. -/
private theorem induction_bound (W : Nat → Nat) (b n : Nat) (positive : ∀ i, 0<W i)
    (origin : W 0=1) (base : b≤W 1)
    (convex : ∀ j, j+2≤n → b^2*W (j+1)^2≤W (j+2)*W j) :
    ∀ k, k≤n → b^(k^2)≤W k ∧ (k+1≤n → b^(2*k+1)*W k≤W (k+1)) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.zero_pow (by decide : 0<2),Nat.pow_zero,Nat.mul_zero,Nat.zero_add,Nat.pow_one,origin,Nat.mul_one]
    exact ⟨Nat.le_refl 1,fun _=>base⟩
  | succ k ih =>
    intro inRange
    obtain ⟨size,step⟩:=ih (by omega)
    have inc:=step inRange
    have ex : (k+1)^2=(2*k+1)+k^2 := by grobner
    constructor
    · rw [ex,Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_left _ size) inc
    · intro next
      refine Nat.le_of_mul_le_mul_right ?_ (positive k)
      calc
          (b^(2*(k+1)+1)*W (k+1))*W k = (b^2*W (k+1))*(b^(2*k+1)*W k) := by
              rw [show 2*(k+1)+1=2+(2*k+1) by omega,Nat.pow_add]
              grobner
          _ ≤ (b^2*W (k+1))*W (k+1) := Nat.mul_le_mul_left _ inc
          _ = b^2*W (k+1)^2 := by grobner
          _ ≤ W (k+2)*W k := convex k next

/-- The lower doubling and addition inequalities at (j+2)P and jP
suffice. Only the first numerator norm is required. -/
theorem numerator_growth (W : Nat → Nat) (q n : Nat) (positive : ∀ i,0<W i)
    (origin : W 0=1) (base : q^2≤W 1) (calibration : 16*q^8≤(W 1)^4)
    (firstDouble : W 1^4≤W 2)
    (lower : ∀ j, j+2≤n → W (j+1)^4≤W (2*(j+1)))
    (pair : ∀ j, j+2≤n → W (2*(j+1))*W 2≤16*(W (j+2)*W j)^2) :
    (q^(n^2))^2≤W n := by
  have convex (j : Nat) (hj : j+2≤n) : (q^2)^2*W (j+1)^2≤W (j+2)*W j := by
    have both:=Nat.mul_le_mul (lower j hj) (Nat.le_trans calibration firstDouble)
    have bound:=Nat.le_trans both (pair j hj)
    have rewrite : W (j+1)^4*(16*q^8)=16*((q^2)^2*W (j+1)^2)^2 := by grobner
    rw [rewrite] at bound
    exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (Nat.le_of_mul_le_mul_left bound (by decide))
  have h:=(induction_bound W (q^2) n positive origin base convex n (Nat.le_refl _)).1
  rw [←Nat.pow_mul] at h ⊢
  rwa [Nat.mul_comm] at h

/-- Base 28 follows from H(P)=41 before evaluating the second multiple. -/
theorem physical_growth (W : Nat → Nat) (n : Nat) (positive : ∀ i,0<W i)
    (origin : W 0=1) (base : W 1=41^2) (firstDouble : W 1^4≤W 2)
    (lower : ∀ j, j+2≤n → W (j+1)^4≤W (2*(j+1)))
    (pair : ∀ j, j+2≤n → W (2*(j+1))*W 2≤16*(W (j+2)*W j)^2) :
    (28^(n^2))^2≤W n :=
  numerator_growth W 28 n positive origin (by rw [base];decide) (by rw [base];decide)
    firstDouble lower pair

end EllipticHeight.IntegerOrbit
#print axioms EllipticHeight.IntegerOrbit.numerator_growth
#print axioms EllipticHeight.IntegerOrbit.physical_growth
