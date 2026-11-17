import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

/-! Uniform filtering of the roots of a polynomial by a nonvanishing
condition. U is the outer polynomial variable, T the inner one. -/
namespace Sun28.Mask
open Polynomial
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]
/-- A root at which the guard vanishes contributes exactly U. -/
def factor (r a : L) : (L[X])[X] := X + C (C a * (X - C r))

def product (s : Multiset L) (g : L → L) : (L[X])[X] :=
  (s.map fun r => factor r (g r)).prod

def survivors (s : Multiset L) (g : L → L) : L[X] :=
  (s.map fun r => if g r = 0 then 1 else C (g r) * (X - C r)).prod

def rejected (s : Multiset L) (g : L → L) : ℕ :=
  (s.filter fun r => g r = 0).card

theorem survivors_ne (s : Multiset L) (g : L → L) : survivors s g ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [survivors]
  | cons r s ih =>
    simp only [survivors,Multiset.map_cons,Multiset.prod_cons] at ih ⊢
    by_cases h : g r = 0
    · simpa [h] using ih
    · simpa [h] using mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h) (X_sub_C_ne_zero r)) ih

theorem survivors_root (s : Multiset L) (g : L → L) (t : L) :
    (survivors s g).IsRoot t ↔ t ∈ s ∧ g t ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [survivors,IsRoot]
  | cons r s ih =>
    simp only [survivors,Multiset.map_cons,Multiset.prod_cons] at ih ⊢
    simp only [IsRoot.def] at ih ⊢
    rw [eval_mul,mul_eq_zero,ih,Multiset.mem_cons]
    by_cases h : g r = 0
    · simp [h]; aesop
    · simp [h,sub_eq_zero]; aesop

/-- Factor off one power of U for each rejected geometric root, including each
copy of a root of higher multiplicity. -/
theorem factorization (s : Multiset L) (g : L → L) :
    ∃ q : (L[X])[X], product s g = X^(rejected s g) * q ∧ q.coeff 0 = survivors s g := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1,by simp [product,rejected],by simp [survivors]⟩
  | cons r s ih =>
    obtain ⟨q,hq,h0⟩ := ih
    have hm : product (r ::ₘ s) g = factor r (g r) * product s g := by simp [product]
    by_cases h : g r = 0
    · refine ⟨q,?_,?_⟩
      · rw [hm,hq]; simp [factor,h,rejected,pow_succ]; ring
      · simpa [survivors,h] using h0
    · refine ⟨factor r (g r)*q,?_,?_⟩
      · rw [hm,hq]; simp [rejected,h]; ring
      · simp [factor,h0,survivors,h]

/-- The first nonzero coefficient in U is a polynomial in T whose roots are
exactly the surviving roots. The index is read from polynomial coefficients. -/
theorem first_coefficient (s : Multiset L) (g : L → L) :
    let e := rejected s g
    e ≤ s.card ∧ (∀ j < e, (product s g).coeff j = 0) ∧
      (product s g).coeff e ≠ 0 ∧
      ∀ t : L, ((product s g).coeff e).IsRoot t ↔ t ∈ s ∧ g t ≠ 0 := by
  dsimp only
  obtain ⟨q,hq,h0⟩ := factorization s g
  have he : (product s g).coeff (rejected s g) = survivors s g := by
    simpa [hq,coeff_X_pow_mul'] using h0
  refine ⟨Multiset.card_le_card (Multiset.filter_le ..),?_,he ▸ survivors_ne s g,?_⟩
  · intro j hj; simp [hq,coeff_X_pow_mul',Nat.not_le.mpr hj]
  · rw [he]; exact survivors_root s g

end
end Sun28.Mask
#print axioms Sun28.Mask.factorization
#print axioms Sun28.Mask.first_coefficient
