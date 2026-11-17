import BranchFields

/-! The monic odd equation of the six-contact curve in the branch coordinates of Thomae. -/
open Polynomial
namespace ZInQBlueprint.OddModel
open ThetaPeriod BinaryCover SexticThetaHeight
noncomputable section

/-- Eilers' odd equation on the chart z = 1/(x − r₅). -/
def quintic (r : Fin 6 → ℂ) : ℂ[X] := ∏ i, (X - C (finiteBranches r i))

/-- On the complementary chart t = x − r₅ the point t = 0 is a branch point. -/
def infinityChart (r : Fin 6 → ℂ) : ℂ[X] := X * ∏ i, (1 - C (finiteBranches r i) * X)

theorem quintic_monic_degree (r : Fin 6 → ℂ) : (quintic r).Monic ∧ (quintic r).natDegree = 5 := by
  refine ⟨monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _), ?_⟩
  unfold quintic
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (finiteBranches r i))]
  simp

theorem quintic_roots (r : Fin 6 → ℂ) (z : ℂ) :
    (quintic r).eval z = 0 ↔ ∃ i, z = finiteBranches r i := by
  classical
  simp [quintic, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

theorem finiteBranch_ne {r : Fin 6 → ℂ} (hr : Function.Injective r) (i : Fin 5) :
    finiteBranches r i ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last i)))

private theorem reverse_factor {b : ℂ} (hb : b ≠ 0) :
    (1 - C b * X : ℂ[X]).reverse = X - C b := by
  have h : (1 - C b * X : ℂ[X]) = C (-b) * X + C 1 := by simp; ring
  rw [h, reverse_add_C, reverse_mul_X, reverse_C, natDegree_C_mul (neg_ne_zero.mpr hb), natDegree_X]
  simp; ring

private theorem reverse_product {ι : Type*} (S : Finset ι) (p : ι → ℂ[X]) :
    (∏ i ∈ S, p i).reverse = ∏ i ∈ S, (p i).reverse := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, map_one] using (reverse_C (1 : ℂ))
  | insert i S hi ih => simp only [Finset.prod_insert hi, reverse_mul_of_domain, ih]

theorem reverse_infinityChart {r : Fin 6 → ℂ} (hr : Function.Injective r) :
    (infinityChart r).reverse = quintic r := by
  rw [infinityChart, reverse_X_mul, reverse_product]
  exact Finset.prod_congr rfl (fun i _ => reverse_factor (finiteBranch_ne hr i))

/-- This scalar is f'(r₅) when f has leading coefficient a and roots r. -/
def ordinateFactor (a : ℂ) (r : Fin 6 → ℂ) : ℂ := a * ∏ i : Fin 5, (r (Fin.last 5) - r i.castSucc)

theorem ordinateFactor_ne {a : ℂ} (ha : a ≠ 0) {r : Fin 6 → ℂ} (hr : Function.Injective r) :
    ordinateFactor a r ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr fun i _ =>
      sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last i).symm))

/-- Translation of the original polynomial, including its leading coefficient. -/
theorem translated_factor {f : ℚ[X]} (hd : f.natDegree = 6) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0) :
    algEquivAevalXAddC (r (Fin.last 5)) (f.map (algebraMap ℚ ℂ)) =
      C (ordinateFactor (f.leadingCoeff : ℂ) r) * infinityChart r := by
  let a := r (Fin.last 5)
  let e := algEquivAevalXAddC a
  have onX : e X = X + C a := by simp [e]
  have onC (z : ℂ) : e (C z) = C z := e.commutes z
  have lin (i : Fin 5) : X + C a - C (r i.castSucc) =
      C (a - r i.castSucc) * (1 - C (finiteBranches r i) * X) := by
    have h : (a - r i.castSucc) * finiteBranches r i = -1 := by
      change (a - r i.castSucc) * (r i.castSucc - a)⁻¹ = -1
      rw [← neg_sub (r i.castSucc) a, neg_mul, mul_inv_cancel₀ (sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last i)))]
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, h]
    simp; ring
  rw [BranchI4.factorization f hd r hr hz, map_mul, map_prod]
  change e (C _) * ∏ i, e (X - C (r i)) = _
  simp only [onC, map_sub, onX]
  rw [Fin.prod_univ_castSucc, show X + C a - C (r (Fin.last 5)) = (X : ℂ[X]) by simp [a]]
  simp_rw [lin]
  rw [Finset.prod_mul_distrib]
  simp only [ordinateFactor, infinityChart, map_mul, map_prod, a]
  ring

theorem paper_degree {u : ℚ} (hu : u ∉ ZInQ.contactSet) : (paper ℚ u false).natDegree = 6 := by
  have hδ : (GlobalTwist.delta u : ℚ) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  rw [paper_affine_eq_sextic hu, ← map_pow, natDegree_C_mul (pow_ne_zero 2 (CurveChart.yScale_ne hu))]
  exact (smooth_sextic hu hδ).1

theorem roots_of_untwisted {u : ℚ} (hu : u ∉ ZInQ.contactSet) {r : Fin 6 → ℂ}
    (hz : ∀ i, aeval (r i) (sextic u 1) = 0) (i : Fin 6) : aeval (r i) (paper ℚ u false) = 0 := by
  apply (paper_root_iff hu _).mpr
  apply (BranchHeight.root_iff_unit_twist hu (by exact_mod_cast (GlobalTwist.delta_pos u).ne') _).mpr
  exact hz i

end
end ZInQBlueprint.OddModel
#print axioms ZInQBlueprint.OddModel.quintic_monic_degree
#print axioms ZInQBlueprint.OddModel.quintic_roots
#print axioms ZInQBlueprint.OddModel.reverse_infinityChart
#print axioms ZInQBlueprint.OddModel.ordinateFactor_ne
#print axioms ZInQBlueprint.OddModel.translated_factor
#print axioms ZInQBlueprint.OddModel.paper_degree
#print axioms ZInQBlueprint.OddModel.roots_of_untwisted
