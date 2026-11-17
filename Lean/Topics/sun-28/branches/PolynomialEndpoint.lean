import PolynomialBranches
import SunCertificate

/-! From a finite list of root charts over the input and 27 free rationals to
Sun's exact 29-variable integer-polynomial signature. -/
namespace Sun28.Branches
open MvPolynomial

private def reorder : Fin 29 → Fin 29 :=
  Fin.cases 1 (Fin.cases 0 (fun i : Fin 27 => i.succ.succ))

/-- Move the input to position zero and the reciprocal witness to position one. -/
noncomputable def polynomial28 (atlas : List (Chart 28)) : Poly 29 :=
  rename reorder (atlasPolynomial atlas)

theorem eval28_polynomial28 (atlas : List (Chart 28)) (x w : ℚ) (z : Fin 27 → ℚ) :
    Sun28.eval28 (polynomial28 atlas) x (Fin.cases w z) =
      value (Fin.cases w (Fin.cases x z)) (atlasPolynomial atlas) := by
  unfold Sun28.eval28 polynomial28
  rw [eval₂_rename]
  change eval₂ _ _ _ = eval₂ _ _ _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

set_option maxHeartbeats 2000000 in
/-- Exact witness transfer. The same integer polynomial works at every input. -/
theorem polynomial28_spec (atlas : List (Chart 28)) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (polynomial28 atlas) x y = 0) ↔
      ∃ z : Fin 27 → ℚ, ∃ a ∈ atlas, a.accepts (Fin.cases x z) := by
  constructor
  · rintro ⟨y,hy⟩
    let z : Fin 27 → ℚ := fun i => y i.succ
    have h : Fin.cases (y 0) z = y := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    refine ⟨z,(atlas_projection _ _).mp ⟨y 0,?_⟩⟩
    rw [← eval28_polynomial28,h]
    exact hy
  · rintro ⟨z,hz⟩
    let base : Fin 28 → ℚ := Fin.cases x z
    have accepted : ∃ a ∈ atlas, a.accepts base := hz
    have hwitness := (atlas_projection atlas base).mpr accepted
    obtain ⟨w,hw⟩ := hwitness
    refine ⟨Fin.cases w z,?_⟩
    rw [eval28_polynomial28]
    exact hw

/-- A chart atlas with complete witnesses and these arithmetic estimates gives
the literal 28-witness theorem. All hypotheses concern the charts and arithmetic;
the output polynomial is constructed by the preceding definition. -/
theorem integerDefinition28_of_charts (atlas : List (Chart 28))
    {C K S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S)
    (complete : ∀ m : ℤ, ∃ z : Fin 27 → ℚ, ∃ a ∈ atlas, a.accepts (Fin.cases (m:ℚ) z))
    (sound : ∀ x : ℚ, (∃ z : Fin 27 → ℚ, ∃ a ∈ atlas, a.accepts (Fin.cases x z)) →
      ∃ (n Δ : ℤ) (B c hβ : ℝ),
        (Sun28.multiplier C K S : ℝ) ≤ c ∧ c-1 ≤ B ∧ |(Δ:ℝ)| ≤ 10*B^4 ∧
        (Δ ≠ 0 → B^2 ≤ C*(1 + |(Δ:ℝ)| ^ (3/8:ℝ))) ∧
        (Δ = 0 → c-4 < Real.log B) ∧
        (2*x^2+3 ≠ (n:ℚ) → Real.log B ≤ K+3*hβ) ∧ hβ ≤ S*Real.sqrt c) :
    Sun28.IntegerDefinition28 := by
  exact ⟨polynomial28 atlas,Sun28.projection_of_estimates hC hS _ _
    (polynomial28_spec atlas) complete sound⟩

end Sun28.Branches
#print axioms Sun28.Branches.eval28_polynomial28
#print axioms Sun28.Branches.polynomial28_spec
#print axioms Sun28.Branches.integerDefinition28_of_charts
