import GuitartDescent
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-! A quadratic subfield in the quaternion algebra after extension of the
coefficient field of degree at most eight. -/
open Polynomial IntermediateField
namespace ZOverQ.Qualitative.QuaternionField
noncomputable section
variable {E : Type} [Field E] [NumberField E]

private theorem primitive_eight_three {a u v : E} (ha : a^2 = -3) (hu : u^2 = 2)
    (hv : v^2 = 6) : ∃ (x y : E), IsPrimitiveRoot x 8 ∧ IsPrimitiveRoot y 3 := by
  let i := a*u/v
  have hi : i^2 = -1 := by
    dsimp [i]; rw [div_pow,mul_pow,ha,hu,hv]; norm_num
  let x := (1+i)/u
  have hx : x^2 = i := by
    dsimp [x]; rw [div_pow,hu]; linear_combination hi/2
  refine ⟨x,(a-1)/2,?_,?_⟩
  · apply (isRoot_cyclotomic_iff_charZero (by decide)).mp
    have pol : cyclotomic 8 E = X^4+1 := by
      have h := cyclotomic_prime_pow_eq_geom_sum (R:=E) (n:=2) Nat.prime_two
      simpa [Finset.sum_range_succ, add_comm] using h
    simp only [pol, IsRoot, eval_add, eval_pow, eval_X, eval_one]
    rw [show x^4=(x^2)^2 by ring,hx,hi]; ring
  · apply (isRoot_cyclotomic_iff_charZero (by decide)).mp
    simp only [cyclotomic_three, IsRoot, eval_add, eval_pow, eval_X, eval_one]
    linear_combination ha/4

private theorem primitive_five {K : Type*} [Field K] [CharZero K] {t w : K}
    (ht : t^2+t-1=0) (hw : w^2+1=t*w) : IsPrimitiveRoot w 5 := by
  have eqn : w^4+w^3+w^2+w+1 = 0 := calc
    _ = (w^2+1)^2 + (w^2+1)*w - w^2 := by ring
    _ = 0 := by rw [hw]; linear_combination w^2*ht
  apply (isRoot_cyclotomic_iff_charZero (by decide)).mp
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime]
  simpa [IsRoot,Finset.sum_range_succ,add_assoc,add_comm,add_left_comm] using eqn

/-- The four quaternion squares cannot all be squares in a number field of
degree at most eight. The first three give primitive eighth and third roots.
A single quadratic extension then supplies a fifth root, which forces degree
at least φ(120)=32 over the rationals. -/
theorem not_all_squares (bound : Module.finrank ℚ E ≤ 8)
    {a u v s : E} (ha : a^2 = -3) (hu : u^2 = 2) (hv : v^2 = 6) (hs : s^2 = 5) : False := by
  obtain ⟨x,y,hx,hy⟩ := primitive_eight_three ha hu hv
  let t := (s-1)/2
  have ht : t^2+t-1 = 0 := by dsimp [t]; linear_combination hs/4
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E (AlgebraicClosure E) (t^2-4)) (n:=2) (by decide)
  let L := E⟮w⟯
  let W : L := AdjoinSimple.gen E w
  have hint := Algebra.IsIntegral.isIntegral (R:=E) w
  let := adjoin.finiteDimensional hint
  have hdeg : Module.finrank E L ≤ 2 := by
    rw [show L = E⟮w⟯ by rfl, adjoin.finrank hint]
    let f : E[X] := X^2-C (t^2-4)
    have h0 : f ≠ 0 := (monic_X_pow_sub_C _ (by decide : (2:ℕ) ≠ 0)).ne_zero
    have he : aeval w f=0 := by simp [f,hw]
    simpa only [f, natDegree_X_pow_sub_C] using Polynomial.natDegree_le_of_dvd (minpoly.dvd E w he) h0
  have hW : W^2 = algebraMap E L (t^2-4) := by
    apply (algebraMap L (AlgebraicClosure E)).injective
    simpa [map_pow,W] using hw
  let T := algebraMap E L t
  have hT : T^2+T-1=0 := by simpa [T] using congrArg (algebraMap E L) ht
  have hw' : ((T+W)/2)^2+1=T*((T+W)/2) := by
    simp only [map_sub,map_pow,map_ofNat] at hW
    change W^2=T^2-4 at hW
    linear_combination hW/4
  have ζ := (hx.map_of_injective (algebraMap E L).injective).pow_mul_pow_lcm
    (hy.map_of_injective (algebraMap E L).injective) (by decide) (by decide)
  have ψ := primitive_five hT hw'
  let : FiniteDimensional ℚ L := Module.Finite.trans E L
  have lb : (Nat.lcm (Nat.lcm 8 3) 5).totient ≤ Module.finrank ℚ L := IsPrimitiveRoot.lcm_totient_le_finrank ζ ψ (cyclotomic.irreducible_rat (by decide))
  have numeric : (Nat.lcm (Nat.lcm 8 3) 5).totient = 32 := by decide
  rw [numeric,← Module.finrank_mul_finrank ℚ E L] at lb
  nlinarith [Nat.mul_le_mul bound hdeg]

/-- A presentation of the discriminant-six quaternion algebra supplies a field
of the degree required for GL₂-type over every coefficient field of degree ≤ 8. -/
theorem field_action {A : Type} [Ring A] [Nontrivial A] [Algebra E A] [Algebra ℚ A]
    [IsScalarTower ℚ E A] (bound : Module.finrank ℚ E ≤ 8)
    (i j : A) (hi : i^2 = -3) (hj : j^2 = 2) (skew : j*i = -(i*j)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L), Module.finrank ℚ L = 2 * Module.finrank ℚ E ∧
      Nonempty (L →ₐ[ℚ] A) := by
  have hk : (i*j)^2 = 6 := calc
    _ = i*(j*i)*j := by noncomm_ring
    _ = -(i^2*j^2) := by rw [skew]; noncomm_ring
    _ = 6 := by rw [hi,hj]; norm_num
  have hl : (i+2*j)^2 = 5 := calc
    _ = i^2+2*(i*j + j*i)+4*j^2 := by noncomm_ring
    _ = 5 := by rw [skew,hi,hj]; simp only [add_neg_cancel, mul_zero, add_zero]; norm_num
  by_cases h₁ : IsSquare (-3:E)
  · by_cases h₂ : IsSquare (2:E)
    · by_cases h₃ : IsSquare (6:E)
      · have ns : ¬ IsSquare (5:E) := by
          rintro ⟨s,hs⟩
          obtain ⟨a,ha⟩ := h₁
          obtain ⟨u,hu⟩ := h₂
          obtain ⟨v,hv⟩ := h₃
          exact not_all_squares bound (a:=a) (u:=u) (v:=v) (s:=s)
            (by simpa [sq] using ha.symm) (by simpa [sq] using hu.symm)
            (by simpa [sq] using hv.symm) (by simpa [sq] using hs.symm)
        exact GuitartDescent.quadratic_field_action (5:E) ns (i+2*j) (by simpa only [map_ofNat, ← sq] using hl)
      · exact GuitartDescent.quadratic_field_action (6:E) h₃ (i*j) (by simpa only [map_ofNat, ← sq] using hk)
    · exact GuitartDescent.quadratic_field_action (2:E) h₂ j (by simpa only [map_ofNat, ← sq] using hj)
  · exact GuitartDescent.quadratic_field_action (-3:E) h₁ i (by simpa only [map_neg, map_ofNat, ← sq] using hi)

end
end ZOverQ.Qualitative.QuaternionField
#print axioms ZOverQ.Qualitative.QuaternionField.not_all_squares
#print axioms ZOverQ.Qualitative.QuaternionField.field_action
