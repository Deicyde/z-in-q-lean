import Std

namespace IndependentIndices.DoublingJets
open Lean.Grind

/-- Sum of the terms indexed from zero to n−1. -/
def sumBefore {R : Type} [CommRing R] (f : Nat → R) : Nat → R
  | 0 => 0
  | n+1 => sumBefore f n + f n

private theorem sum_of_zero {R : Type} [CommRing R] {f : Nat → R} (n : Nat)
    (h : ∀ i, i<n → f i=0) : sumBefore f n=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBefore, ih (fun i hi => h i (by omega)), h n (by omega)]
    grobner

/-- Coefficient of z^k in U(z)^i, by finite convolution. -/
def powCoeff {R : Type} [CommRing R] (u : Nat → R) : Nat → Nat → R
  | 0, k => if k=0 then 1 else 0
  | i+1, k => sumBefore (fun l => powCoeff u i l * u (k-l)) (k+1)

theorem power_constant {R : Type} [CommRing R] (u : Nat → R) (i : Nat) :
    powCoeff u i 0 = (u 0)^i := by
  induction i with
  | zero => simp [powCoeff,Semiring.pow_zero]
  | succ i ih =>
    simp only [powCoeff,sumBefore,Nat.sub_self,ih,Semiring.pow_succ]
    grobner

/-- Coefficient of z^j in B(zU(z)), with B given by the coefficient function b. -/
def composeCoeff {R : Type} [CommRing R] (b u : Nat → R) (j : Nat) : R :=
  sumBefore (fun i => b i * powCoeff u i (j-i)) (j+1)

/-- Over a characteristic-zero coefficient ring the displayed scalar cancellation
holds for every j≥2. Equality with the doubling action forces each error coefficient to vanish. -/
theorem vanishing_jet {R : Type} [CommRing R] (b u : Nat → R) (order : Nat)
    (linear : u 0=2) (b0 : b 0=0) (b1 : b 1=0)
    (cancel : ∀ j, 2≤j → ∀ c : R, c*2^j=2*c → c=0)
    (commutes : ∀ j, j<order → composeCoeff b u j = 2*b j) :
    ∀ j, j<order → b j=0 := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro bound
    by_cases zero : j=0
    · simpa [zero] using b0
    by_cases one : j=1
    · simpa [one] using b1
    apply cancel j (by omega)
    have eq := commutes j bound
    have previous : sumBefore (fun i => b i * powCoeff u i (j-i)) j=0 :=
      sum_of_zero j (fun i hi => by rw [ih i hi (by omega)]; grobner)
    have short : 0+b j*2^j=2*b j := by
      simpa only [composeCoeff,sumBefore,previous,Nat.sub_self,power_constant,linear] using eq
    grobner

attribute [local instance] Semiring.natCast

theorem field_vanishing {R : Type} [Field R] [IsCharP R 0] (b u : Nat → R) (order : Nat)
    (linear : u 0=2) (b0 : b 0=0) (b1 : b 1=0)
    (commutes : ∀ j, j<order → composeCoeff b u j=2*b j) :
    ∀ j, j<order → b j=0 := by
  apply vanishing_jet b u order linear b0 b1 _ commutes
  intro j large c eq
  have gt : 2^1 < (2:Nat)^j := Nat.pow_lt_pow_right (by decide) (by omega)
  have ne : (2:R)^j ≠ 2 := by
    intro same
    have h : (((2:Nat)^j : Nat):R)=((2:Nat):R) := by
      rw [Semiring.natCast_pow, ← Semiring.ofNat_eq_natCast (α:=R) 2]; exact same
    have eqnat := (IsCharP.natCast_ext_iff (α:=R) 0).mp h
    simp only [Nat.mod_zero] at eqnat
    omega
  have z : c*(2^j-2)=0 := by grobner
  exact (Field.of_mul_eq_zero z).resolve_right (fun h => ne (by grobner))

#print axioms power_constant
#print axioms vanishing_jet
#print axioms field_vanishing
end IndependentIndices.DoublingJets
