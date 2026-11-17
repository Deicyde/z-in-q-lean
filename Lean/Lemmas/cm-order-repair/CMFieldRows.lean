import SixRationalCM
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Basic

/-! Identifying rational CM points from their rational center fields, without
computing the conductor of their integral endomorphism rings. -/
namespace ZInQBlueprint.CMRepair
open QuaternionLift
noncomputable section

abbrev QuadraticModel (k : ℚ) := QuadraticAlgebra ℚ k 0

/-- A negative rational square in the quadratic field must be the square of
a purely imaginary element. This is also valid in a quadratic algebra. -/
theorem squareclass_of_negative_root {d k : ℚ} (hd : d < 0) (hk : k ≠ 0)
    (x : QuadraticModel k) (hx : x^2 = algebraMap ℚ (QuadraticModel k) d) : IsSquare (d/k) := by
  have hr := congrArg QuadraticAlgebra.re hx
  have hi := congrArg QuadraticAlgebra.im hx
  simp only [sq,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,zero_mul,add_zero] at hr hi
  have ni : x.im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg x.re]
  have hprod : x.re*x.im = 0 := by nlinarith only [hi]
  have nr : x.re = 0 := (mul_eq_zero.mp hprod).resolve_right ni
  refine ⟨x.im,(div_eq_iff hk).mpr ?_⟩
  rw [nr] at hr
  linear_combination -hr

private theorem row_negative {a : CMRow} (ha : a ∈ rationalCMRows) : (a.1 : ℚ) < 0 := by
  have empty : rationalCMRows.filter (fun b => decide (0 ≤ b.1)) = [] := by decide +kernel
  by_contra h
  have hn : 0 ≤ a.1 := by exact_mod_cast le_of_not_gt h
  have hm : a ∈ rationalCMRows.filter (fun b => decide (0 ≤ b.1)) :=
    List.mem_filter.mpr ⟨ha, by simp [hn]⟩
  rw [empty] at hm
  exact List.not_mem_nil hm

def fieldRows (k : ℚ) : List CMRow :=
  rationalCMRows.filter (fun a => decide (IsSquare ((a.1 : ℚ)/k)))

theorem two_center_tables :
    fieldRows (-19) = [(-19,3^7,2^10)] ∧ fieldRows (-6) = [(-24,1,1)] := by decide +kernel

private theorem row_of_center_map {a : CMRow} (ha : a ∈ rationalCMRows) {k : ℚ} (hk : k ≠ 0)
    (centerMap : QuadraticModel (a.1 : ℚ) →ₐ[ℚ] QuadraticModel k) : a ∈ fieldRows k := by
  let z : QuadraticModel (a.1 : ℚ) := QuadraticAlgebra.omega
  have hz : z^2 = algebraMap ℚ _ (a.1 : ℚ) := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  have h : (centerMap z)^2 = algebraMap ℚ _ (a.1 : ℚ) := by rw [← map_pow, hz, centerMap.commutes]
  exact List.mem_filter.mpr ⟨ha, by simp [squareclass_of_negative_root (row_negative ha) hk _ h]⟩

theorem row_of_cm19_center {a : CMRow} (ha : a ∈ rationalCMRows)
    (centerMap : QuadraticModel (a.1 : ℚ) →ₐ[ℚ] QuadraticModel (-19)) :
    a = (-19,3^7,2^10) := by
  have p := row_of_center_map ha (by norm_num : (-19:ℚ) ≠ 0) centerMap
  simpa [two_center_tables.1] using p

theorem row_of_cm24_center {a : CMRow} (ha : a ∈ rationalCMRows)
    (centerMap : QuadraticModel (a.1 : ℚ) →ₐ[ℚ] QuadraticModel (-6)) :
    a = (-24,1,1) := by
  have p := row_of_center_map ha (by norm_num : (-6:ℚ) ≠ 0) centerMap
  simpa [two_center_tables.2] using p

/-- The reciprocal absolute value cannot occur at any rational CM point.
The check includes the zero and infinity rows projectively. -/
theorem no_reciprocal_row : rationalCMRows.filter
    (fun a => decide (1024*a.2.2 = 2187*a.2.1)) = [] := by decide +kernel

/-- Once the scale at -24 and the unordered divisors are fixed, *any*
rational CM row at the second sextic suffices to determine the orientation.
Only the magnitude of its coordinate is used. -/
theorem normalized_of_rational_cm {X : Type*} (T t : X → ℂ) (p : X)
    (alternatives : T = t ∨ ∀ x, t x ≠ 0 → T x*t x = 1)
    (arithmetic : T p = -(27:ℂ)/16 * (81/64)) (nonzero : t p ≠ 0)
    (q : ℚ) (rational : t p = (q : ℂ)) (a : CMRow) (ha : a ∈ rationalCMRows)
    (table : |q*(a.2.2 : ℚ)| = (a.2.1 : ℚ)) : T = t := by
  rcases alternatives with done | inverse
  · exact done
  have prod := inverse p nonzero
  rw [arithmetic, rational] at prod
  have cleared : (2187:ℂ)*(q:ℂ) = -1024 := by linear_combination -1024*prod
  have hq : (2187:ℚ)*q = -1024 := by exact_mod_cast cleared
  have value : q = -1024/2187 := by linear_combination hq/2187
  rw [value, abs_mul, abs_of_nonneg (show 0 ≤ (a.2.2 : ℚ) from Nat.cast_nonneg _)] at table
  norm_num at table
  have product : (1024:ℚ)*(a.2.2 : ℚ) = 2187*(a.2.1 : ℚ) := by linarith
  have integral : 1024*a.2.2 = 2187*a.2.1 := by exact_mod_cast product
  have hit : a ∈ rationalCMRows.filter (fun b => decide (1024*b.2.2 = 2187*b.2.1)) :=
    List.mem_filter.mpr ⟨ha, by simp [integral]⟩
  rw [no_reciprocal_row] at hit
  exact False.elim (List.not_mem_nil hit)

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.squareclass_of_negative_root
#print axioms ZInQBlueprint.CMRepair.two_center_tables
#print axioms ZInQBlueprint.CMRepair.row_of_cm19_center
#print axioms ZInQBlueprint.CMRepair.row_of_cm24_center
#print axioms ZInQBlueprint.CMRepair.no_reciprocal_row
#print axioms ZInQBlueprint.CMRepair.normalized_of_rational_cm
