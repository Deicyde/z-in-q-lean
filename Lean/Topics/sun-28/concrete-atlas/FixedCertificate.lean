import FixedBranches
import DyadicTruncation

/-! The polynomial zero locus over any input, before any height hypothesis is used. -/
namespace Sun28.Concrete
open Forward FixedPreparation WitnessIndices Ordinary ScalarHeight ZInQ
noncomputable section

def WitnessAt (x : ℚ) : Prop :=
  ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, PointCertificate (nineAffine a).doubles fixedMultiplier
    anchor x η gamma denominator smallMultipliers smallMultipliers

theorem polynomial_iff_certificate (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial x w=0) ↔ WitnessAt x := by
  rw [fixedPolynomial,Branches.polynomial28_spec]
  simp_rw [Compiler.branchAtlas_spec]
  have he (z : Fin 27 → ℚ) := fixed_exact (Fin.cases x z)
  simp_rw [he]
  constructor
  · rintro ⟨z,a,h⟩
    rw [fixed_cutoff,multiplier_at_cutoff] at h
    exact ⟨a,z 18,free_tests_certificate h⟩
  · rintro ⟨a,η,h⟩
    obtain ⟨z,_,hz⟩ := certificate_free_tests _ _ _ _ _ _ _ _ _ h
    refine ⟨z,a,?_⟩
    rw [fixed_cutoff,multiplier_at_cutoff]
    exact hz

/-- The two logarithms in denominators are nonzero on every certificate, including
certificates of a putative nonintegral input. No height theorem enters this step. -/
theorem certificate_log_guards (a : Fin 9 → AffineInput) {x η : ℚ}
    (h : PointCertificate (nineAffine a).doubles fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers) :
    truncAt (nineAffine a).doubles.H≠0 ∧ conjugation (truncAt (translatedBase (nineAffine a).doubles anchor))≠0 := by
  have hm := fixed_multiplier_spec
  obtain ⟨z,hz,_⟩ := extract_from_doubles (nineAffine a) fixedMultiplier anchor (by omega) hm.1
    ⟨h.q_nonzero,h.h_nonzero,h.base_nonzero,(rational_chart_iff _).1 h.odd_N,
      (rational_chart_iff _).1 h.odd_T,(rational_chart_iff _).1 h.odd_Z⟩
  exact both_denominators hz


end
end Sun28.Concrete
#print axioms Sun28.Concrete.polynomial_iff_certificate
#print axioms Sun28.Concrete.certificate_log_guards
