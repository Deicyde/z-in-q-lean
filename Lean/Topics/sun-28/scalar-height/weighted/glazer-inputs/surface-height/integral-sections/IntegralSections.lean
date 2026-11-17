import VerticalDLog

/-! Integral expressions for the two bicanonical sections on the five-mark line. -/
namespace ZInQBlueprint.IntegralSections

/-- The four finite factors in the coordinate t = 32s. -/
def branchProduct {K : Type*} [CommRing K] (t : K) : K :=
  t * (t-32) * (t-76832) * (t+343)

/-- Two integer partial-fraction identities, with the numerator of the second section scaled
by only 75. The products on the right are products of logarithmic derivatives. -/
theorem section_identities {K : Type*} [Field K] (t a : K) (off : branchProduct t ≠ 0) :
    let A := a/t
    let B := a/(t-32)
    let C := a/(t-76832)
    let D := a/(t+343)
    let q := a^2/branchProduct t
    let qt := (B*D-C*D)+205*(B*C-C*D)
    75*t*q = qt ∧ 823200*q = -75*(A*C-B*C)-32*qt := by
  have off' : t ≠ 0 ∧ t-32 ≠ 0 ∧ t-76832 ≠ 0 ∧ t+343 ≠ 0 := by
    simpa only [branchProduct, mul_ne_zero_iff, and_assoc] using off
  rcases off' with ⟨h0,h1,h2,h3⟩
  dsimp only [branchProduct]
  constructor <;> field_simp [h0,h1,h2,h3] <;> ring

variable {V K : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- Both bicanonical coefficients lie in the vertical DVR for any integral tangent operator. -/
theorem vertical_sections (p : ℕ) (hp : Irreducible (p : V)) (D : Derivation ℤ K K)
    (preserves : ∀ v : V, D (algebraMap V K v) ∈ (algebraMap V K).range)
    (t : K) (off : branchProduct t ≠ 0) :
    (823200 * ((D t)^2 / branchProduct t)) ∈ (algebraMap V K).range ∧
    (75*t * ((D t)^2 / branchProduct t)) ∈ (algebraMap V K).range := by
  let S := (algebraMap V K).range
  have off' : t ≠ 0 ∧ t-32 ≠ 0 ∧ t-76832 ≠ 0 ∧ t+343 ≠ 0 := by
    simpa only [branchProduct, mul_ne_zero_iff, and_assoc] using off
  obtain ⟨h0,h1,h2,h3⟩ := off'
  have A : D t/t ∈ S := log_derivative_integral p hp D preserves t h0
  have d32 : D (32:K) = 0 := D.map_natCast 32
  have B : D t/(t-32) ∈ S := by
    simpa only [Derivation.map_sub, d32, sub_zero] using
      log_derivative_integral p hp D preserves _ h1
  have d76832 : D (76832:K) = 0 := D.map_natCast 76832
  have C : D t/(t-76832) ∈ S := by
    simpa only [Derivation.map_sub, d76832, sub_zero] using
      log_derivative_integral p hp D preserves _ h2
  have d343 : D (343:K) = 0 := D.map_natCast 343
  have E : D t/(t+343) ∈ S := by
    simpa only [Derivation.map_add, d343, add_zero] using
      log_derivative_integral p hp D preserves _ h3
  have ids := section_identities t (D t) off
  dsimp only at ids
  have qt : 75*t*((D t)^2/branchProduct t) ∈ S := by
    rw [ids.1]
    exact S.add_mem (S.sub_mem (S.mul_mem B E) (S.mul_mem C E))
      (S.mul_mem (natCast_mem S 205) (S.sub_mem (S.mul_mem B C) (S.mul_mem C E)))
  refine ⟨?_,qt⟩
  rw [ids.2, ← ids.1]
  exact S.sub_mem (S.mul_mem (S.neg_mem (natCast_mem S 75))
    (S.sub_mem (S.mul_mem A C) (S.mul_mem B C))) (S.mul_mem (natCast_mem S 32) qt)

end ZInQBlueprint.IntegralSections
#print axioms ZInQBlueprint.IntegralSections.section_identities
#print axioms ZInQBlueprint.IntegralSections.vertical_sections
