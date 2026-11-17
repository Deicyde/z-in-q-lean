import SeparatedCompiler
import Mathlib.Data.Fin.Tuple.Basic

/-! Rational projections of finite unions of hypersurface charts or tested
monic towers. The k input coordinates always precede the d free coordinates
and the last witness. No bound on the number or degrees of the equations is used. -/
open Sun28.Branches ZInQBlueprint.SunResultant
namespace RelativeWidth
noncomputable section

/-- Form the tuple in its displayed polynomial order. -/
def point {k d : ℕ} (x : Fin k → ℚ) (z : Fin d → ℚ) (w : ℚ) : Fin (k+d+1) → ℚ :=
  Fin.append (Fin.append x z) (fun _ : Fin 1 => w)

private def lastWitness (n : ℕ) : Fin (n+1) → Fin (n+1) :=
  Fin.cases (Fin.natAdd n (0 : Fin 1)) (Fin.castAdd 1)

def equation {k d : ℕ} (charts : List (Chart (k+d))) : Poly (k+d+1) :=
  MvPolynomial.rename (lastWitness (k+d)) (atlasPolynomial charts)

private theorem evaluation {k d : ℕ} (c : List (Chart (k+d))) (x : Fin k → ℚ)
    (z : Fin d → ℚ) (w : ℚ) :
    value (point x z w) (equation c) =
      value (Fin.cases w (Fin.append x z)) (atlasPolynomial c) := by
  unfold equation value
  change MvPolynomial.eval₂ _ _ (MvPolynomial.rename _ _) = MvPolynomial.eval₂ _ _ _
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Fin.append_right (Fin.append x z) (fun _ : Fin 1 => w) 0
  · exact Fin.append_left (Fin.append x z) (fun _ : Fin 1 => w) j

theorem charts_spec {k d : ℕ} (c : List (Chart (k+d))) (x : Fin k → ℚ) :
    (∃ z : Fin d → ℚ, ∃ w : ℚ, value (point x z w) (equation c) = 0) ↔
      ∃ z : Fin d → ℚ, ∃ a ∈ c, a.accepts (Fin.append x z) := by
  apply exists_congr
  intro z
  simpa only [evaluation] using atlas_projection c (Fin.append x z)

/-- The number of stages and their degrees may vary from branch to branch. -/
structure TowerBranch (m : ℕ) where
  stages : ℕ
  tower : ParamTower (Poly m) stages
  equations : List (Sun28.Compiler.Test m stages)
  guards : List (Sun28.Compiler.Test m stages)

def TowerBranch.charts {m : ℕ} (b : TowerBranch m) : List (Chart m) :=
  Sun28.Compiler.atlas b.tower b.equations b.guards

def TowerBranch.accepts {m : ℕ} (b : TowerBranch m) (p : Fin m → ℚ) : Prop :=
  Sun28.Compiler.Solutions b.tower b.equations b.guards p

theorem towers_spec {k d : ℕ} (bs : List (TowerBranch (k+d))) (x : Fin k → ℚ) :
    (∃ z : Fin d → ℚ, ∃ w : ℚ, value (point x z w) (equation (bs.flatMap TowerBranch.charts)) = 0) ↔
      ∃ z : Fin d → ℚ, ∃ b ∈ bs, b.accepts (Fin.append x z) := by
  rw [charts_spec]
  apply exists_congr
  intro z
  constructor
  · rintro ⟨c,hc,h⟩
    obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hc
    exact ⟨b,hb,(Sun28.Compiler.atlas_spec ..).mp ⟨c,hm,h⟩⟩
  · rintro ⟨b,hb,h⟩
    obtain ⟨c,hm,hc⟩ := (Sun28.Compiler.atlas_spec b.tower b.equations b.guards _).mpr h
    exact ⟨c,List.mem_flatMap.mpr ⟨b,hb,hm⟩,hc⟩

/-- Exactly one input and 84 rational witnesses. A single polynomial
represents every fibre of the given collection simultaneously. -/
theorem bound85 (bs : List (TowerBranch 84)) :
    ∃ P : Poly 85, ∀ t : ℚ,
      (∃ z : Fin 83 → ℚ, ∃ w : ℚ, value (point (k:=1) (fun _ => t) z w) P = 0) ↔
        ∃ z : Fin 83 → ℚ, ∃ b ∈ bs, b.accepts (Fin.append (fun _ : Fin 1 => t) z) := by
  exact ⟨equation (k:=1) (d:=83) (bs.flatMap TowerBranch.charts),
    fun t => towers_spec (k:=1) (d:=83) bs (fun _ => t)⟩

end
end RelativeWidth
#print axioms RelativeWidth.charts_spec
#print axioms RelativeWidth.towers_spec
#print axioms RelativeWidth.bound85
