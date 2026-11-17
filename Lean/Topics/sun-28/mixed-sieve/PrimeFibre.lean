import RayRectangles
import WeightedSelection

namespace Sun28.MixedSieve
open ManuscriptV15.Arithmetic Sun28.NormSieve Sun28.ContactFactors Sun28.WeightedSelection

variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- The oriented Gaussian generator in a candidate reduces to the circle over
the numerical prime value at the corresponding cleared shift. -/
noncomputable def primeFibre (a : Candidate A d H Y) (p : ℕ) [Fact p.Prime] (r : ↥(shifts A)) :
    Circle p (norms (coefficients A p) (a.u:ZMod p) (a.v:ZMod p) r) :=
  ⟨(realResidue p (a.gaussian r),imagResidue p (a.gaussian r)),by
    rw [←gaussian_residue,a.rays.norm,prime_value_residue a.values r p]⟩

theorem fibre_bad_iff (a : Candidate A d H Y) (p : ℕ) [Fact p.Prime]
    (r : ↥(shifts A)) (e : Bool) :
    primeFibre a p r∈bad p _ e ↔ p∣adjacentNorm (a.gaussian r) e := by
  rw [bad,Finset.mem_filter,← ZMod.natCast_eq_zero_iff]
  cases e <;> simp [primeFibre,adjacentNorm,gaussian_residue,realResidue,imagResidue]

theorem fibre_obstructed_iff (a : Candidate A d H Y) (p : ℕ) [Fact p.Prime] :
    primeFibre a p∈obstructed _ ↔
      ∃ i j,p∣adjacentNorm (a.gaussian i) true ∧ p∣adjacentNorm (a.gaussian j) false := by
  simp_rw [obstructed_iff,fibre_bad_iff]

/-- Outside the fixed modulus the exact local test in the global selection
problem is exactly survival in the finite mixed norm model. -/
theorem atPrime_iff_fibre (a : Candidate A d H Y) (T : Finset ℕ) (κ p : ℕ)
    [Fact p.Prime] (odd : p≠2) (outside : p∉T) (aux : p∉κ.primeFactors) :
    atPrime a.gaussian T κ p ↔ primeFibre a p∉obstructed _ := by
  rw [fibre_obstructed_iff]
  constructor
  · rintro ⟨mixed,diag,_,_⟩ ⟨i,j,plus,minus⟩
    by_cases eq : i=j
    · subst j
      obtain ⟨split,neg⟩:=self_obstruction odd _ plus minus
      exact diag split i neg ((diagonal_iff odd _).mp ⟨plus,minus⟩)
    · exact mixed i j eq ⟨(forbidden_iff odd _ _).mpr plus,(forbidden_iff odd _ _).mpr minus⟩
  · intro good
    refine ⟨fun i j _ h => good ⟨i,j,(forbidden_iff odd _ _).mp h.1,(forbidden_iff odd _ _).mp h.2⟩,
      fun _ i _ h => good ⟨i,i,(diagonal_iff odd _).mpr h⟩,
      fun h => (outside h).elim,fun h => (aux h).elim⟩

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.fibre_bad_iff
#print axioms Sun28.MixedSieve.fibre_obstructed_iff
#print axioms Sun28.MixedSieve.atPrime_iff_fibre
