import GeometricCharts
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! Integral closure of the coordinate ring of a separable hyperelliptic chart. -/
open CategoryTheory AlgebraicGeometry Polynomial
open scoped nonZeroDivisors
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- If f is squarefree and f z² is integral in Frac(R), then z already belongs to the UFD R. -/
theorem squarefree_denominator {R L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field L] [Algebra R L] [IsFractionRing R L] (f : R) (hf : Squarefree f) (z : L)
    (h : IsLocalization.IsInteger R (algebraMap R L f * z^2)) : IsLocalization.IsInteger R z := by
  obtain ⟨m,hm⟩ := h
  let n := IsFractionRing.num R z
  let d : R := IsFractionRing.den R z
  have hd : z * algebraMap R L d = algebraMap R L n := IsFractionRing.num_mul_den_eq_num_iff_eq.mpr rfl
  have he : f*(n*n) = d*d*m := by
    apply IsFractionRing.injective R L
    simp only [map_mul,← hd,hm]
    ring
  have hdiv : d ∣ n*n := hf.dvd_of_squarefree_of_mul_dvd_mul_right ⟨m,he⟩
  have hcop : IsRelPrime d n := (IsFractionRing.num_den_reduced R z).symm
  exact IsFractionRing.isInteger_of_isUnit_den (hcop.isUnit_of_dvd (hcop.dvd_of_dvd_mul_left hdiv))

section Quadratic
variable {R L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable [Field L] [Algebra R L] [IsFractionRing R L]
local notation "α" => algebraMap R L
local notation "O" f => QuadraticAlgebra R f (0:R)
local notation "T" f => QuadraticAlgebra L (α f) (α 0)
attribute [local instance] QuadraticAlgebra.algebra

omit [UniqueFactorizationMonoid R] in
/-- The localized quadratic algebra is the fraction field as soon as it is a field. -/
private theorem quadratic_fraction (f : R) [IsDomain (O f)] (field : IsField (T f)) :
    IsFractionRing (O f) (T f) := by
  let S := Algebra.algebraMapSubmonoid (O f) R⁰
  have : IsLocalization S (T f) := by
    apply (Algebra.isLocalization_iff_isPushout R⁰ L).mpr
    rw [Algebra.IsPushout.comm]
    exact QuadraticAlgebra.isPushout L f 0
  apply IsLocalization.of_le S
  · rintro _ ⟨x,hx,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ QuadraticAlgebra.algebraMap_injective).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  · intro x hx
    let := field.toField
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
      (QuadraticAlgebra.mapRingHom_injective α f 0 (IsFractionRing.injective _ _))).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hx))

/-- A square root of a squarefree element gives an integrally closed quadratic order
over a UFD if two is invertible and the resulting fraction algebra is a field. -/
theorem normal_quadratic (f : R) (hf : Squarefree f) [Invertible (2:R)]
    [IsDomain (O f)] (field : IsField (T f)) : IsIntegrallyClosed (O f) := by
  have := quadratic_fraction f field
  apply (isIntegrallyClosed_iff (T f)).mpr
  intro z hz
  have h : _root_.IsIntegral R z := isIntegral_trans z hz
  let σ : (T f) →ₐ[R] (T f) := {
    toRingHom := starRingAut.toRingHom
    commutes' := fun r => by
      change star (algebraMap L (T f) (α r)) = algebraMap L (T f) (α r)
      apply QuadraticAlgebra.ext <;> simp }
  have hc : _root_.IsIntegral R (star z) := h.map σ
  have htr : _root_.IsIntegral R (QuadraticAlgebra.trace z) := by
    apply (isIntegral_algebraMap_iff (B := T f)).mp
    rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
    exact h.add hc
  have hnorm : _root_.IsIntegral R (QuadraticAlgebra.norm z) := by
    apply (isIntegral_algebraMap_iff (B := T f)).mp
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact h.mul hc
  obtain ⟨s,hs⟩ := (isIntegrallyClosed_iff L).mp (inferInstanceAs (IsIntegrallyClosed R)) htr
  obtain ⟨n,hn⟩ := (isIntegrallyClosed_iff L).mp (inferInstanceAs (IsIntegrallyClosed R)) hnorm
  let a := ⅟(2:R)*s
  have ha : α a = z.re := by
    have hc : α (⅟(2:R)) * 2 = 1 := by simpa only [map_mul,map_ofNat,map_one] using congrArg α (invOf_mul_self (2:R))
    simp only [a,map_mul,hs,QuadraticAlgebra.trace_def,map_zero,zero_mul,add_zero,← mul_assoc,hc,one_mul]
  obtain ⟨b,hb⟩ := squarefree_denominator f hf z.im (show IsLocalization.IsInteger R (α f*z.im^2) from by
    refine ⟨a^2-n,?_⟩
    simp only [map_sub,map_pow,ha,hn,QuadraticAlgebra.norm_def,map_zero,zero_mul,add_zero]
    ring)
  exact ⟨⟨a,b⟩,QuadraticAlgebra.ext ha hb⟩
end Quadratic

/-- The squarefree positive-degree hyperelliptic chart has an integrally closed coordinate ring. -/
theorem normal_cover {K : Type} [Field K] [Invertible (2:K)] {f : K[X]}
    (hd : 0 < f.natDegree) (hf : IsCoprime f f.derivative) : IsIntegrallyClosed (Cover f) := by
  let L := FractionRing K[X]
  let α := algebraMap K[X] L
  let := domain_separable_cover hd hf
  let : Fact (¬ IsSquare (α f)) := ⟨nonsquare_fraction hd hf⟩
  let : Invertible (2:K[X]) := by
    rw [← C_ofNat]
    exact Invertible.map (C : K →+* K[X]) (2:K)
  apply normal_quadratic (L := L) f (show f.Separable from hf).squarefree
  change IsField (QuadraticAlgebra L (α f) (α 0))
  rw [map_zero]
  exact Field.toIsField (QuadraticAlgebra L (α f) 0)

theorem dedekind_cover {K : Type} [Field K] [Invertible (2:K)] {f : K[X]}
    (hd : 0 < f.natDegree) (hf : IsCoprime f f.derivative) : IsDedekindDomain (Cover f) := by
  let := domain_separable_cover hd hf
  let := normal_cover hd hf
  have : Ring.DimensionLEOne (Cover f) := Ring.DimensionLEOne.of_isIntegral K[X] (Cover f)
  exact (isDedekindDomain_iff (Cover f) (FractionRing (Cover f))).mpr
    ⟨inferInstance,IsNoetherianRing.of_finite K[X] (Cover f),inferInstance,(isIntegrallyClosed_iff _).mp (normal_cover hd hf)⟩

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.squarefree_denominator
#print axioms ZInQBlueprint.BinaryCover.normal_quadratic
#print axioms ZInQBlueprint.BinaryCover.normal_cover
#print axioms ZInQBlueprint.BinaryCover.dedekind_cover
