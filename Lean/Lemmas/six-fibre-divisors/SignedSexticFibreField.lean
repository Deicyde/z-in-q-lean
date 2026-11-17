import QuadraticFibreDivisors
import GeometricCharts
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension

/-! The signed sextic as an explicit quadratic extension of K(x). -/
open Polynomial
namespace ZInQBlueprint.FibreDivisors
open BinaryCover AlgebraicCurve
noncomputable section
open scoped QuadraticAlgebra
open Classical

variable {K : Type} [Field K]

theorem nonsquare_of_chart_domain (f : K[X]) [IsDomain (Cover f)] :
    ¬IsSquare (algebraMap K[X] (RatFunc K) f) := by
  rintro ⟨z,hz⟩
  have hz' : z ^ 2 = algebraMap K[X] (RatFunc K) f := by simpa only [sq] using hz.symm
  obtain ⟨g,hg⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := K[X]) (x := z) (n := 2) (by decide) (hz' ▸ isIntegral_algebraMap)
  have hf : g ^ 2 = f := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    rw [map_pow,hg,hz']
  have h : (ω : Cover f) ^ 2 = (algebraMap K[X] (Cover f) g) ^ 2 := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero, ←map_pow, hf]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with he | he <;>
    have hi := congrArg (fun a : Cover f => a.im) he <;> simpa using hi

def ordinateConjugation {F : Type*} [Field F] (f : F) : Cover f ≃ₐ[F] Cover f :=
  { (starRingAut : RingAut (Cover f)) with
    commutes' := fun r => by
      change star (algebraMap F (Cover f) r) = _
      apply QuadraticAlgebra.ext <;> simp }

theorem ordinateConjugation_omega {F : Type*} [Field F] (f : F) :
    ordinateConjugation f ω = -ω := by
  change star (ω : Cover f) = -ω
  apply QuadraticAlgebra.ext <;> simp

theorem ordinateConjugation_ne_one {F : Type*} [Field F] [CharZero F] (f : F) :
    ordinateConjugation f ≠ 1 := by
  intro h
  have h' := AlgEquiv.congr_fun h ω
  rw [ordinateConjugation_omega] at h'
  have eq := congrArg (fun r : Cover f => r.im) h'
  change - (1:F) = 1 at eq
  norm_num at eq

variable [CharZero K]

def radicand (K : Type) [Field K] [CharZero K] (u : ℚ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (paper K u false)

abbrev SignedField (K : Type) [Field K] [CharZero K] {u : ℚ} (_hu : u ∉ ZInQ.contactSet) :=
  Cover (radicand K u)

theorem paper_nonsquare {u : ℚ} (hu : u ∉ ZInQ.contactSet) : ¬IsSquare (radicand K u) := by
  let := field_chart_domain K hu false
  exact nonsquare_of_chart_domain _

@[instance_reducible] def signedFieldStructure {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Field (SignedField K hu) := by
  let : Fact (¬IsSquare (radicand K u)) := ⟨paper_nonsquare hu⟩
  exact inferInstanceAs (Field (Cover (radicand K u)))

theorem signed_orbit_principal [IsAlgClosed K] {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI : Fact (¬ IsSquare (radicand K u)) := ⟨paper_nonsquare hu⟩
    ∀ P Q : Place K (SignedField K hu),
      (orbitDivisor (ordinateConjugation (radicand K u)) P -
       orbitDivisor (ordinateConjugation (radicand K u)) Q).IsPrincipal := by
  letI : Fact (¬ IsSquare (radicand K u)) := ⟨paper_nonsquare hu⟩
  intro P Q
  exact orbit_difference_principal (QuadraticAlgebra.finrank_eq_two _ _) _
    (ordinateConjugation_ne_one _) P Q

end
end ZInQBlueprint.FibreDivisors
#print axioms ZInQBlueprint.FibreDivisors.nonsquare_of_chart_domain
#print axioms ZInQBlueprint.FibreDivisors.ordinateConjugation_omega
#print axioms ZInQBlueprint.FibreDivisors.paper_nonsquare
#print axioms ZInQBlueprint.FibreDivisors.signed_orbit_principal

