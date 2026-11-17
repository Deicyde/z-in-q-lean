import BranchRows
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The discriminant and the Vandermonde product of six ordered roots. -/
namespace ZInQBlueprint.BranchFormula
open Polynomial BranchI4
noncomputable section

private def linearProduct (r : Fin 6 → ℂ) : ℂ[X] := ∏ i, (X - C (r i))

private theorem degree_linearProduct (r : Fin 6 → ℂ) : (linearProduct r).natDegree = 6 := by
  unfold linearProduct
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))]
  simp

private def slopeProduct (r : Fin 6 → ℂ) (i : Fin 6) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (r i - r j)

private theorem slope_at_root (r : Fin 6 → ℂ) (i : Fin 6) :
    (linearProduct r).derivative.eval (r i) = slopeProduct r i := by
  unfold linearProduct
  rw [← Finset.mul_prod_erase _ (fun j => X - C (r j)) (Finset.mem_univ i), derivative_mul]
  simp [slopeProduct, eval_prod]

private theorem slope_ne_diagonal (r : Fin 6 → ℂ) (i : Fin 6) :
    slopeProduct r i = ∏ j, (if i = j then 1 else r i - r j) := by
  unfold slopeProduct
  rw [← Finset.mul_prod_erase _ (fun j => if i = j then 1 else r i - r j) (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1.symm]

private theorem signed_difference (r : Fin 6 → ℂ) (i j : Fin 6) :
    (if i = j then 1 else r i-r j) =
    (if j < i then -1 else 1) *
    ((if i < j then r i-r j else 1) * (if j < i then r j-r i else 1)) := by
  rcases lt_trichotomy i j with h | h | h
  · simp [h,h.ne,not_lt_of_ge h.le]
  · subst j; simp
  · simp [h,h.ne.symm,not_lt_of_ge h.le]

private def pairSign (i j : Fin 6) : ℤ := if j < i then -1 else 1

private theorem sign_product :
    (∏ i : Fin 6, ∏ j : Fin 6, (if j < i then -1 else 1 : ℂ)) = -1 := by
  have row (i : Fin 6) : ∏ j, pairSign i j = (-1 : ℤ)^i.val := by
    fin_cases i <;> norm_num [pairSign, Fin.prod_univ_succ, Fin.lt_def]
  have integer : (∏ i : Fin 6, ∏ j, pairSign i j) = -1 := by
    simp only [row]
    norm_num [Fin.prod_univ_succ]
  have mapped := congrArg (Int.castRingHom ℂ) integer
  simpa only [pairSign,map_prod,apply_ite,map_neg,map_one] using mapped

theorem product_slopes (r : Fin 6 → ℂ) : (∏ i, slopeProduct r i) = - (vandermonde r)^2 := by
  simp only [slope_ne_diagonal, signed_difference, Finset.prod_mul_distrib]
  rw [sign_product]
  let a (i j : Fin 6) : ℂ := if i < j then r i-r j else 1
  change -1*((∏ i, ∏ j, a i j) * ∏ i, ∏ j, a j i) = - (vandermonde r)^2
  rw [Finset.prod_comm (f := fun i j => a j i)]
  change -1*(vandermonde r*vandermonde r) = _
  ring

theorem discriminant_roots (f : ℚ[X]) (hd : f.natDegree = 6)
    (r : Fin 6 → ℂ) (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0) :
    (f.discr : ℂ) = (f.leadingCoeff : ℂ)^10 * (vandermonde r)^2 := by
  let φ := algebraMap ℚ ℂ
  let a : ℂ := f.leadingCoeff
  let g := linearProduct r
  have ha : a ≠ 0 := by
    change (↑f.leadingCoeff : ℂ) ≠ 0
    exact_mod_cast leadingCoeff_ne_zero.mpr (fun hf => by simp [hf] at hd)
  have hp : 0 < f.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hres := congrArg φ (resultant_deriv hp)
  rw [hd] at hres
  norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reduceDiv,Odd.neg_one_pow (by decide : Odd 15)] at hres
  have fac : f.map φ = C a * g := factorization f hd r hr hz
  have dmap : f.derivative.map φ = C a * g.derivative := by rw [← derivative_map,fac,derivative_C_mul]
  have gl : g.natDegree = 6 := degree_linearProduct r
  have gd : g.derivative.natDegree ≤ 5 := by rw [natDegree_derivative,gl]
  have hprod : g.resultant g.derivative 6 5 = ∏ i, slopeProduct r i := by
    have key := resultant_prod_left Finset.univ (fun i : Fin 6 => X - C (r i)) g.derivative 5 (by simp) gd
    change g.resultant g.derivative g.natDegree 5 = _ at key
    rw [gl] at key
    simpa only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ gd, g, slope_at_root] using key
  rw [← resultant_map_map,fac,dmap,resultant_C_mul_left,resultant_C_mul_right,hprod,product_slopes] at hres
  change a^5*(a^6* - (vandermonde r)^2) = _ at hres
  simp only [map_mul,map_neg,map_one] at hres
  change _ = -1*a*(f.discr:ℂ) at hres
  apply mul_left_cancel₀ ha
  linear_combination hres

end
end ZInQBlueprint.BranchFormula
#print axioms ZInQBlueprint.BranchFormula.product_slopes
#print axioms ZInQBlueprint.BranchFormula.discriminant_roots
