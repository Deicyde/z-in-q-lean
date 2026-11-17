import ParamCollision
import RationalLocator

/-! Rational values of the locator and its guard samples at one and the same tuple. -/
open Polynomial ZInQBlueprint.SunTower ZInQBlueprint.SunResultant
open ZInQBlueprint.SunResultant.ParamTower
namespace Sun28.Compiler
noncomputable section
variable {R : Type*} [CommRing R] {n : ℕ}
local notation "Ω" => AlgebraicClosure ℚ
local instance : DecidableEq Ω := Classical.decEq _

/-- Separation on all geometric tuples, including nonrational conjugates. -/
def Separates (T : ParamTower R n) (φ : R →+* ℚ) (b : ℕ) : Prop :=
  Set.InjOn (separator (b:Ω)) ((rootTuples ((algebraMap ℚ Ω).comp φ) T).toFinset : Set (Fin n → Ω))

theorem rational_selects_iff (T : ParamTower R n) (φ : R →+* ℚ) (b : ℕ) :
    Separates T φ b ↔ ∃ d ≤ T.degreeProduct^2, Selected T φ b d := by
  have h := selects_iff T ((algebraMap ℚ Ω).comp φ) b
  simpa only [Separates,Selected,RingHom.comp_apply,ne_eq,map_eq_zero_iff _ (algebraMap ℚ Ω).injective] using h

theorem exists_selection (T : ParamTower R n) (φ : R →+* ℚ) :
    ∃ b ≤ bound T, ∃ d ≤ T.degreeProduct^2, Selected T φ b d := by
  let ρ := (algebraMap ℚ Ω).comp φ
  obtain ⟨b,hb,hi⟩ := exists_bounded_separator (rootTuples ρ T).toFinset
  exact ⟨b,hb.trans (fibre_card_bound T ρ),(rational_selects_iff T φ b).mp hi⟩

theorem rational_samples (T : ParamTower R n) (φ : R →+* ℚ)
    (f : MvPolynomial (Fin n) R) {b : ℕ} (hi : Separates T φ b)
    (x : Fin n → ℚ) (hx : Satisfies φ T x) :
    (∀ j ≤ T.degreeProduct, ((sample T b j f).map φ).IsRoot (separator (b:ℚ) x)) ↔
      MvPolynomial.eval₂Hom φ x f = 0 := by
  let ι : ℚ →+* Ω := algebraMap ℚ Ω
  let ρ := ι.comp φ
  let y := fun i => ι (x i)
  have sep : separator (b:Ω) y = ι (separator (b:ℚ) x) := by simp [separator,y,ι]
  have root (P : R[X]) (z : ℚ) : (P.map ρ).IsRoot (ι z) ↔ (P.map φ).IsRoot z := by
    change (P.map (ι.comp φ)).eval (ι z) = 0 ↔ (P.map φ).eval z = 0
    rw [← Polynomial.map_map,eval_map_apply,map_eq_zero_iff _ ι.injective]
  have h := finite_guard_samples T ρ f hi y ((satisfies_hom φ ι T x).mpr hx)
  have hf : MvPolynomial.eval₂Hom ρ y f = ι (MvPolynomial.eval₂Hom φ x f) :=
    (MvPolynomial.map_eval₂Hom φ x ι f).symm
  simpa only [sep,root,hf,map_eq_zero_iff _ ι.injective] using h

#print axioms rational_selects_iff
#print axioms exists_selection
#print axioms rational_samples
end
end Sun28.Compiler
