import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-! Removing all multiplicities of the roots on a forbidden hypersurface. -/
open Polynomial
namespace Sun28.Guard
variable {K : Type*} [Field K] [DecidableEq K]

/-- At a point of a polynomial branch, divide by its common factor with a sufficiently
large power of the polynomial that must be nonzero. -/
noncomputable def keep (P G : K[X]) (N : ℕ) : K[X] := P / EuclideanDomain.gcd P (G^N)

theorem keep_mul_gcd (P G : K[X]) (N : ℕ) :
    keep P G N * EuclideanDomain.gcd P (G^N) = P := by
  have hd := EuclideanDomain.gcd_dvd_left P (G^N)
  by_cases hz : EuclideanDomain.gcd P (G^N)=0
  · rw [hz,zero_dvd_iff] at hd
    rw [hd,mul_comm]; simp [keep]
  · exact (mul_comm _ _).trans (EuclideanDomain.mul_div_cancel' hz hd)

theorem keep_ne_zero {P : K[X]} (hP : P≠0) (G : K[X]) (N : ℕ) :
    keep P G N ≠ 0 := by
  intro h
  exact hP (by rw [←keep_mul_gcd P G N,h,zero_mul])

/-- Every forbidden root is removed with its full multiplicity. -/
theorem isRoot_keep {P G : K[X]} {N : ℕ} (hP : P≠0) (bound : P.natDegree≤N) (t : K) :
    (keep P G N).IsRoot t ↔ P.IsRoot t ∧ ¬ G.IsRoot t := by
  let d := EuclideanDomain.gcd P (G^N)
  let m := P.rootMultiplicity t
  have fac : keep P G N*d=P := keep_mul_gcd P G N
  have bound' : m≤N := by
    have a := natDegree_le_of_dvd (P.pow_rootMultiplicity_dvd t) hP
    simpa [natDegree_pow,natDegree_X_sub_C,m] using a.trans bound
  constructor
  · intro h
    have lin : X-C t ∣ keep P G N := dvd_iff_isRoot.mpr h
    refine ⟨dvd_iff_isRoot.mp (lin.trans ⟨d,fac.symm⟩),?_⟩
    intro forbidden
    have powd : (X-C t)^m ∣ d := EuclideanDomain.dvd_gcd (P.pow_rootMultiplicity_dvd t)
      ((pow_dvd_pow _ bound').trans (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr forbidden) N))
    have too : (X-C t)^(m+1) ∣ P := by
      rw [pow_succ,←fac,mul_comm (keep P G N) d]
      exact mul_dvd_mul powd lin
    exact P.pow_rootMultiplicity_not_dvd hP t too
  · rintro ⟨yes,no⟩
    have nd : ¬ d.IsRoot t := by
      intro bad
      have gpow := (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr bad).trans
        (EuclideanDomain.gcd_dvd_right P (G^N))))
      change (G^N).eval t=0 at gpow
      rw [eval_pow] at gpow
      exact (pow_ne_zero _ no) gpow
    have eq : (keep P G N).eval t * d.eval t = 0 := by
      rw [←eval_mul,fac]; exact yes
    exact (mul_eq_zero.mp eq).resolve_right nd

/-- The same polynomial works on all extensions, including an algebraic closure. -/
theorem map_keep {L : Type*} [Field L] [DecidableEq L] (f : K →+* L) (P G : K[X]) (N : ℕ) :
    (keep P G N).map f = keep (P.map f) (G.map f) N := by
  rw [keep,keep,Polynomial.map_div,←Polynomial.gcd_map,Polynomial.map_pow]

theorem isRoot_map_keep {L : Type*} [Field L] [DecidableEq L] (f : K →+* L)
    {P G : K[X]} {N : ℕ} (hP : P≠0) (bound : P.natDegree≤N) (t : L) :
    ((keep P G N).map f).IsRoot t ↔ (P.map f).IsRoot t ∧ ¬(G.map f).IsRoot t := by
  rw [map_keep]
  apply isRoot_keep
  · exact fun h => hP ((Polynomial.map_eq_zero_iff f.injective).mp h)
  · exact (natDegree_map_le).trans bound

#print axioms keep_mul_gcd
#print axioms keep_ne_zero
#print axioms isRoot_keep
#print axioms map_keep
#print axioms isRoot_map_keep
end Sun28.Guard
