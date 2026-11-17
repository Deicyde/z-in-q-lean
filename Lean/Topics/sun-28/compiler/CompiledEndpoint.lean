import SeparatedCompiler
import PolynomialEndpoint

/-! From a finite disjunction of tested triangular systems to the literal
one-input, 28-witness signature. Tower lengths may differ between branches. -/
open ZInQBlueprint.SunResultant ZInQBlueprint.SunResultant.ParamTower Sun28.Branches
namespace Sun28.Compiler
noncomputable section

/-- A monic triangular system together with the polynomial conditions on a
common tuple. The number of tuple coordinates belongs to the individual branch. -/
structure Branch (m : ℕ) where
  length : ℕ
  tower : ParamTower (Poly m) length
  equations : List (Test m length)
  guards : List (Test m length)

/-- Concatenation implements the disjunction without introducing a selector variable. -/
def branchAtlas {m : ℕ} (branches : List (Branch m)) : List (Chart m) :=
  branches.flatMap fun a => atlas a.tower a.equations a.guards

theorem branchAtlas_spec {m : ℕ} (branches : List (Branch m)) (p : Fin m → ℚ) :
    (∃ a ∈ branchAtlas branches, a.accepts p) ↔
    ∃ B ∈ branches, Solutions B.tower B.equations B.guards p := by
  simp only [branchAtlas,List.mem_flatMap]
  constructor
  · rintro ⟨a,⟨B,hB,ha⟩,hx⟩
    exact ⟨B,hB,(atlas_spec ..).mp ⟨a,ha,hx⟩⟩
  · rintro ⟨B,hB,h⟩
    obtain ⟨a,ha,hx⟩ := (atlas_spec ..).mpr h
    exact ⟨a,⟨B,hB,ha⟩,hx⟩

private theorem branchAtlas_explicit {m : ℕ} (bs : List (Branch m)) (p : Fin m → ℚ) :
    (∃ a ∈ branchAtlas bs, a.accepts p) ↔
    ∃ B ∈ bs, ∃ y : Fin B.length → ℚ,
        Satisfies (value p) B.tower y ∧
        (∀ f ∈ B.equations, MvPolynomial.eval₂Hom (value p) y f = 0) ∧
        ∀ g ∈ B.guards, MvPolynomial.eval₂Hom (value p) y g ≠ 0 := by
  simpa only [Solutions] using branchAtlas_spec bs p

/-- The input is first. A tuple of 27 free parameters and a tested triangular
system specify the remaining arithmetic certificate. -/
def branchRelation (branches : List (Branch 28)) (x : ℚ) : Prop :=
  ∃ z : Fin 27 → ℚ, ∃ B ∈ branches, Solutions B.tower B.equations B.guards (Fin.cases x z)

attribute [local irreducible] branchAtlas atlas Chart.accepts polynomial28 Sun28.eval28 Satisfies value in
theorem eval28_iff (branches : List (Branch 28)) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 (polynomial28 (branchAtlas branches)) x w = 0) ↔
    ∃ z : Fin 27 → ℚ, ∃ B ∈ branches, ∃ y : Fin B.length → ℚ,
        Satisfies (value (Fin.cases x z)) B.tower y ∧
        (∀ f ∈ B.equations, MvPolynomial.eval₂Hom (value (Fin.cases x z)) y f = 0) ∧
        ∀ g ∈ B.guards, MvPolynomial.eval₂Hom (value (Fin.cases x z)) y g ≠ 0 := by
  constructor
  · intro h
    obtain ⟨z,accepted⟩ := (polynomial28_spec (branchAtlas branches) x).mp h
    exact ⟨z,(branchAtlas_explicit (m := 28) branches (Fin.cases x z)).mp accepted⟩
  · rintro ⟨z,accepted⟩
    apply (polynomial28_spec (branchAtlas branches) x).mpr
    exact ⟨z,(branchAtlas_explicit (m := 28) branches (Fin.cases x z)).mpr accepted⟩

/-- Arithmetic completeness on integers and the listed estimates on accepted
certificates imply the full 28-witness Diophantine definition. -/
theorem integerDefinition28_of_branches (branches : List (Branch 28))
    {C K S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S)
    (complete : ∀ m : ℤ, branchRelation branches (m:ℚ))
    (sound : ∀ x : ℚ, branchRelation branches x →
      ∃ (n Δ : ℤ) (B c hβ : ℝ),
        (Sun28.multiplier C K S : ℝ) ≤ c ∧ c-1 ≤ B ∧ |(Δ:ℝ)| ≤ 10*B^4 ∧
        (Δ ≠ 0 → B^2 ≤ C*(1 + |(Δ:ℝ)| ^ (3/8:ℝ))) ∧
        (Δ = 0 → c-4 < Real.log B) ∧
        (2*x^2+3 ≠ (n:ℚ) → Real.log B ≤ K+3*hβ) ∧ hβ ≤ S*Real.sqrt c) :
    Sun28.IntegerDefinition28 := by
  exact ⟨polynomial28 (branchAtlas branches),Sun28.projection_of_estimates hC hS (branchRelation branches)
    _ (eval28_iff branches) complete sound⟩

#print axioms branchAtlas_spec
#print axioms eval28_iff
#print axioms integerDefinition28_of_branches
end
end Sun28.Compiler
