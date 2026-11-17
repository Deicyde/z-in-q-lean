import QuadraticChange

/-! Covariance of the binary sextic discriminant on all projective charts.
A factor supported at infinity is allowed. -/
namespace ZInQBlueprint.MinimalDiscriminant
open Polynomial
noncomputable section
abbrev Rows (K : Type*) := Fin 6 → K × K

def bracket {K : Type*} [CommRing K] (v w : K × K) : K := v.1*w.2 - v.2*w.1

def bracketProduct {K : Type*} [CommRing K] (l : Rows K) : K :=
  ∏ i, ∏ j, if i < j then bracket (l i) (l j) else 1

/-- The discriminant of c times six linear factors is the square of the
product of their fifteen brackets, times c to the tenth power. -/
def splitDisc {K : Type*} [CommRing K] (c : K) (l : Rows K) : K :=
  c^10 * (bracketProduct l)^2

def changeRows {K : Type*} [CommRing K] (l : Rows K) (a b c d : K) : Rows K :=
  fun i => ((l i).1*a+(l i).2*c,(l i).1*b+(l i).2*d)

theorem bracket_change {K : Type*} [CommRing K] (l : Rows K) (a b c d : K) (i j : Fin 6) :
    bracket (changeRows l a b c d i) (changeRows l a b c d j) =
    (a*d-b*c)*bracket (l i) (l j) := by
  dsimp [bracket,changeRows]
  ring

private theorem fifteen {K : Type*} [CommMonoid K] (s : K) :
    (∏ i : Fin 6, ∏ j : Fin 6, if i < j then s else 1) = s^15 := by
  have point (i j : Fin 6) : (if i < j then s else 1) = s^(if i < j then 1 else 0 : ℕ) := by
    split <;> simp_all
  simp only [point,Finset.prod_pow_eq_pow_sum]
  congr 1

theorem splitDisc_change {K : Type*} [CommRing K] (l : Rows K) (e s a b c d : K) :
    splitDisc (s*e) (changeRows l a b c d) = s^10*(a*d-b*c)^30*splitDisc e l := by
  have pairs (i j : Fin 6) :
      (if i < j then bracket (changeRows l a b c d i) (changeRows l a b c d j) else 1) =
        (if i < j then a*d-b*c else 1)*(if i < j then bracket (l i) (l j) else 1) := by
    split <;> simp_all [bracket_change]
  simp only [splitDisc,bracketProduct,pairs,Finset.prod_mul_distrib,fifteen,mul_pow]
  ring

/-- It agrees with the native rational polynomial discriminant on the given
degree-six chart, in the same root ordering as the signed sextic. -/
theorem splitDisc_rational {f : ℚ[X]} (hd : f.natDegree=6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0) :
    splitDisc (f.leadingCoeff : ℂ) (fun i => (1,-r i)) = (f.discr : ℂ) := by
  rw [BranchFormula.discriminant_roots f hd r hr hz]
  simp [splitDisc,bracketProduct,bracket,BranchFormula.vandermonde,sub_eq_add_neg,add_comm]

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.bracket_change
#print axioms ZInQBlueprint.MinimalDiscriminant.splitDisc_change
#print axioms ZInQBlueprint.MinimalDiscriminant.splitDisc_rational
