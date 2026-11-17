import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

namespace ZInQBlueprint.Diagonal210
open Polynomial UniqueFactorizationMonoid
noncomputable section
open scoped Polynomial

/-- Finite zeros and poles of a rational square class are read in its reduced
numerator and denominator. Multiplication by the denominator squared gives
the integral representative used here. -/
theorem polynomial_squareclass (f l : ℚ[X]) (hf : f≠0)
    (parity : ∀ q : ℚ[X], Odd ((normalizedFactors f).count q) ↔ q=l) :
    ∃ c : ℚ, c≠0 ∧ ∃ g : ℚ[X], f=C c*l*g^2 := by
  classical
  let s := normalizedFactors f
  have mem : l∈s.toFinset := by
    apply Multiset.mem_toFinset.mpr
    by_contra h
    have odd := (parity l).2 rfl
    change Odd (s.count l) at odd
    rw [Multiset.count_eq_zero_of_notMem h] at odd
    exact (by decide : ¬ Odd (0:ℕ)) odd
  let g := ∏ q ∈ s.toFinset, q^(s.count q/2)
  have pair (q : ℚ[X]) :
      q^(s.count q) = (if q=l then q else 1)*(q^(s.count q/2))^2 := by
    by_cases h : q=l
    · simp only [show (q=l)=True from eq_true h,ite_true,← pow_mul,← pow_succ']
      congr 1
      have H := Nat.odd_iff.mp ((parity q).mpr h)
      change s.count q % 2 = 1 at H
      omega
    · simp only [h,ite_false,one_mul,← pow_mul]
      congr 1
      have H := Nat.not_odd_iff.mp (fun o=>(h ((parity q).mp o)))
      change s.count q % 2 = 0 at H
      omega
  have prod : s.prod=l*g^2 := calc
    s.prod = ∏ q ∈ s.toFinset, q ^ s.count q := Finset.prod_multiset_count s
    _ = _ := by simp_rw [pair]; rw [Finset.prod_mul_distrib, Finset.prod_pow]; simp [g,mem]
  obtain ⟨unit,hunit⟩ := prod_normalizedFactors hf
  obtain ⟨c,hc,ce⟩ := Polynomial.isUnit_iff.mp unit.isUnit
  refine ⟨c,hc.ne_zero,g,?_⟩
  rw [← hunit,← ce]
  change s.prod*C c=_
  rw [prod]
  ring

/-- Over the rational function field, one finite place of odd multiplicity
forces a constant twist of its defining polynomial. Infinity needs no input. -/
theorem one_branch_character (h : RatFunc ℚ) (hh : h≠0) (a : ℚ)
    (orders : ∀ q : ℚ[X], Odd ((normalizedFactors (h.num*h.denom)).count q) ↔ q=X-C a) :
    ∃ c : ℚ, c≠0 ∧ ∃ v : RatFunc ℚ,
      h=algebraMap ℚ _ c * algebraMap ℚ[X] _ (X-C a)*v^2 := by
  obtain ⟨c,hc,g,hg⟩ := polynomial_squareclass _ _ (mul_ne_zero (RatFunc.num_ne_zero hh) h.denom_ne_zero) orders
  let f := algebraMap ℚ[X] (RatFunc ℚ)
  have dn : f h.denom≠0 := fun H=>h.denom_ne_zero ((IsFractionRing.injective ℚ[X] (RatFunc ℚ)) (H.trans f.map_zero.symm))
  have comp : f (C c)=algebraMap ℚ (RatFunc ℚ) c := (IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) c).symm
  have e := congrArg f hg
  simp only [map_mul,map_pow,comp] at e
  refine ⟨c,hc,f g/f h.denom,?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom h]
  change f h.num/f h.denom=_
  field_simp [dn]
  linear_combination e

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.polynomial_squareclass
#print axioms ZInQBlueprint.Diagonal210.one_branch_character
