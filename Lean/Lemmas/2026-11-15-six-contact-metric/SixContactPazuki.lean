import R22BranchBound

/-! The actual six-contact arithmetic endpoint from any nonzero twist of the sextic. -/
namespace ZInQBlueprint.SixMetric
open ThetaQuotient ThetaPeriod BranchHeight OriginalTheta ZInQ.LeafPush2 ZInQ.DefFaltings PkgI3
noncomputable section

/-- The complex periods determine the theta point. The surface here carries the original
bounded stable height and its actual lattice; Eilers's identities couple that lattice to the
six roots. These are the geometric data to construct, without a theta point or height witness. -/
structure MarkedSurface (u δ : ℚ) where
  roots : Fin 6 → ℂ
  distinct : Function.Injective roots
  root : ∀ i, Polynomial.aeval (roots i) (SexticThetaHeight.sextic u δ)=0
  K : Type
  [fieldK : Field K]
  [numberK : NumberField K]
  A : AbVar K
  dim : A.dim=(2:WithBot ℕ∞)
  stable : ℝ
  actual : stableFaltingsHeight A=stable
  upper : stable ≤ HeightBudget.vonKaenelBudget u
  embed : K →+* ℂ
  lattice : Submodule ℤ (Fin 2 → ℂ)
  uniformizing : (Fin 2 → ℂ) → CPts A embed
  uniform : IsUniformization embed lattice uniformizing
  Ω : Matrix (Fin 2) (Fin 2) ℂ
  siegel : IsSiegel Ω
  period : IsPeriodMatrix lattice Ω
  detA : ℂ
  invertible : detA≠0
  first : FirstThomae Ω (finiteBranches roots) detA

theorem canonical_of_surfaces (hr : R22_Pazuki)
    (h : ∀ u : ℚ, u∉ZInQ.contactSet → ∃ δ : ℚ, δ≠0 ∧ Nonempty (MarkedSurface u δ)) :
    CanonicalBranchBound := by
  intro u hu
  obtain ⟨δ,hδ,⟨p⟩⟩ := h u hu
  let := p.fieldK
  let := p.numberK
  have root₁ (i : Fin 6) := (root_iff_unit_twist hu hδ (p.roots i)).mp (p.root i)
  exact ⟨p.roots,p.distinct,root₁,branch_budget_of_R22 hu one_ne_zero p.roots p.distinct root₁
    hr p.K p.A p.dim p.stable p.actual p.upper p.embed p.lattice p.uniformizing p.uniform
    p.Ω p.siegel p.period p.detA p.invertible p.first⟩

theorem sixContactMin_of_surfaces (hr : R22_Pazuki)
    (h : ∀ u : ℚ, u∉ZInQ.contactSet → ∃ δ : ℚ, δ≠0 ∧ Nonempty (MarkedSurface u δ)) : ZInQ.SixContactMin :=
  sixContactMin_of_branchHeight (canonical_iff_bounded.mp (canonical_of_surfaces hr h))

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.canonical_of_surfaces
#print axioms ZInQBlueprint.SixMetric.sixContactMin_of_surfaces
