import ChartBaseChange
import SmoothCharts
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! The nonconstant squarefree radicand remains nonsquare in the rational function field. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
open DirectCharts
noncomputable section

/-- A square root of a polynomial in its fraction field must already be a polynomial.
A nonconstant polynomial coprime to its derivative therefore has no such square root. -/
theorem nonsquare_fraction {K : Type} [Field K] {f : K[X]}
    (hd : 0 < f.natDegree) (hf : IsCoprime f f.derivative) :
    ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) f) := by
  rintro ⟨r,hr⟩
  have hr' : r^2 = algebraMap K[X] (FractionRing K[X]) f := by simpa [sq] using hr.symm
  obtain ⟨p,hp⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := K[X]) (x := r) (n := 2) (by decide) (hr' ▸ isIntegral_algebraMap)
  have he : f = p*p := by
    apply IsFractionRing.injective K[X] (FractionRing K[X])
    rw [map_mul,hp,hr]
  have hu := hf.isUnit_of_dvd' (show p ∣ f from he ▸ dvd_mul_right _ _) (by
    rw [he, derivative_mul]; exact dvd_add (dvd_mul_left _ _) (dvd_mul_right _ _))
  have hz := natDegree_eq_zero_of_isUnit hu
  rw [he,natDegree_mul hu.ne_zero hu.ne_zero,hz] at hd
  omega

theorem domain_separable_cover {K : Type} [Field K] {f : K[X]}
    (hd : 0 < f.natDegree) (hf : IsCoprime f f.derivative) : IsDomain (Cover f) := by
  let α := algebraMap K[X] (FractionRing K[X])
  let : Fact (¬ IsSquare (α f)) := ⟨nonsquare_fraction hd hf⟩
  let e := QuadraticAlgebra.mapRingHom α f 0
  have : IsDomain (QuadraticAlgebra (FractionRing K[X]) (α f) (α 0)) := by
    rw [map_zero]
    exact inferInstanceAs (IsDomain (Cover (α f)))
  exact (QuadraticAlgebra.mapRingHom_injective α f 0 (IsFractionRing.injective _ _)).isDomain e

private theorem rational_chart_regular {u : ℚ} (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    0 < (paper ℚ u i).natDegree ∧ (paper ℚ u i).Separable := by
  obtain ⟨s,t,e,hs,ht,he⟩ := chart_normal_form hu i
  let f := C s * monicSextic t
  have hd : f.natDegree = 6 := (natDegree_C_mul hs).trans (monic_six t).2
  have sep : f.Separable := separable_normal_form hs ht
  have nonzero : f ≠ 0 := fun h => by simp [h] at hd
  have nonunit : ¬ IsUnit f := not_isUnit_of_natDegree_pos _ (by omega)
  change e f = _ at he
  rw [← he]
  constructor
  · by_contra! h
    have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    have nz : (e f).coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hc
      exact nonzero (e.injective (hc.trans e.map_zero.symm))
    exact nonunit ((isUnit_map_iff e f).mp (hc ▸ (isUnit_C.mpr nz.isUnit)))
  · apply PerfectField.separable_iff_squarefree.mpr
    intro x hx
    have H := map_dvd e.symm hx
    have h' : e.symm x * e.symm x ∣ f := by simpa only [map_mul, AlgEquiv.symm_apply_apply] using H
    exact (isUnit_map_iff e.symm x).mp (sep.squarefree _ h')

/-- The whole coordinate ring of either chart is a domain after any extension of Q. -/
theorem field_chart_domain (K : Type) [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (i : Bool) : IsDomain (Cover (paper K u i)) := by
  obtain ⟨hd,hs⟩ := rational_chart_regular hu i
  rw [← paper_baseChange]
  apply domain_separable_cover
  · rwa [natDegree_map_eq_of_injective (algebraMap ℚ K).injective]
  · exact hs.map

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.nonsquare_fraction
#print axioms ZInQBlueprint.BinaryCover.domain_separable_cover
#print axioms ZInQBlueprint.BinaryCover.field_chart_domain
