import PolynomialBranches
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Degree strata convert a parameter-dependent univariate polynomial to
a monic rational-root chart. The leading coefficient is its common denominator. -/
namespace Sun28.Branches
open Polynomial
noncomputable section

private theorem horner_from (d t : ℚ) (hd : d ≠ 0) (a : ℕ → ℚ) (j n : ℕ) :
    d * Projection.monicValue d t ((List.range' j n).map a) =
      d * t^n + ∑ i ∈ Finset.range n, a (j+i) * t^i := by
  induction n generalizing j with
  | zero => simp [Projection.monicValue]
  | succ n ih =>
    rw [List.range'_succ,List.map_cons,Projection.monicValue,Finset.sum_range_succ',
      pow_succ]
    simp only [Nat.add_zero,pow_zero,mul_one]
    have hr := ih (j+1)
    linear_combination (norm := skip) t * hr
    simp [pow_succ,Nat.add_comm,Nat.add_left_comm,mul_comm,mul_left_comm,mul_assoc]
    ring_nf
    rw [Finset.mul_sum]
    field_simp
    ring

def lower {m} (p : Polynomial (Poly m)) (n : ℕ) : List (Poly m) :=
  (List.range n).map p.coeff

def degreeChart {m} (p : Polynomial (Poly m)) (n : ℕ) : Chart m where
  eqs := ((List.range (p.natDegree+1)).filter (n < ·)).map p.coeff
  guard := 1
  den := p.coeff n
  nums := lower p n

theorem monic_eval {m} (p : Polynomial (Poly m)) (x : Fin m → ℚ) (n : ℕ)
    (h : (p.map (value x)).natDegree = n) (hn : p.map (value x) ≠ 0) (t : ℚ) :
    value x (p.coeff n) * Projection.monicValue (value x (p.coeff n)) t
      ((lower p n).map (value x)) = (p.map (value x)).eval t := by
  let q := p.map (value x)
  have hd : value x (p.coeff n) ≠ 0 := by
    rw [← coeff_map,← h,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hn
  rw [eval_eq_sum_range,h,Finset.sum_range_succ]
  simp only [coeff_map,lower,List.map_map]
  simpa [List.range_eq_range',Function.comp_def,add_comm] using
    horner_from (value x (p.coeff n)) t hd (fun j => value x (p.coeff j)) 0 n

theorem degreeChart_spec {m} (p : Polynomial (Poly m)) (x : Fin m → ℚ) (n : ℕ)
    :
    (degreeChart p n).accepts x ↔
      p.map (value x) ≠ 0 ∧ (p.map (value x)).natDegree = n ∧ ∃ t : ℚ, (p.map (value x)).IsRoot t := by
  let q := p.map (value x)
  have hb : q.natDegree ≤ p.natDegree := natDegree_map_le
  have hc (j : ℕ) : q.coeff j = value x (p.coeff j) := coeff_map ..
  have hd (hq : q ≠ 0) (h : q.natDegree = n) : value x (p.coeff n) ≠ 0 := by
    rw [← hc,h.symm,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq
  change ((∀ e ∈ (((List.range (p.natDegree+1)).filter (n < ·)).map p.coeff), value x e = 0) ∧
    value x 1 ≠ 0 ∧ value x (p.coeff n) ≠ 0 ∧ ∃ t, _ = 0) ↔ _
  constructor
  · rintro ⟨zero,_,nz,t,ht⟩
    have q0 : q ≠ 0 := fun eq => nz (by rw [← hc,eq,coeff_zero])
    have lo : n ≤ q.natDegree := le_natDegree_of_ne_zero ((hc n).trans_ne nz)
    have hi : q.natDegree ≤ n := by
      by_contra! gt
      have mem : p.coeff q.natDegree ∈ (((List.range (p.natDegree+1)).filter (n < ·)).map p.coeff) := by
        apply List.mem_map_of_mem
        simp [gt,hb]
      exact (leadingCoeff_ne_zero.mpr q0) ((hc q.natDegree).trans (zero _ mem))
    have eq := le_antisymm hi lo
    refine ⟨q0,eq,t,?_⟩
    change q.eval t = 0
    rw [← monic_eval p x n eq q0 t]
    exact mul_eq_zero_of_right _ ht
  · rintro ⟨q0,eq,t,ht⟩
    refine ⟨?_,by simp,hd q0 eq,t,?_⟩
    · intro e he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
      rw [← hc]
      apply coeff_eq_zero_of_natDegree_lt
      have gt : n < j := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp hj).2
      exact eq ▸ gt
    · have ev := monic_eval p x n eq q0 t
      exact (mul_eq_zero.mp (ev.trans ht)).resolve_left (hd q0 eq)

end
end Sun28.Branches
#print axioms Sun28.Branches.monic_eval
#print axioms Sun28.Branches.degreeChart_spec
