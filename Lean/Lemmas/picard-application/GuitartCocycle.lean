import PicardConjugateEnd
import CentralIsogenyCocycle

/-! The composition of two compatible semilinear quasi-isogenies over a
finite Galois number field. The multiplier is an equality in rational Hom. -/
open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.AbelianModel ZInQBlueprint.NormalDescent
open scoped TensorProduct ZInQBlueprint.NormalDescent
namespace ZOverQ.Qualitative.GuitartCocycle
open PicardConjugateEnd
noncomputable section

/-- Scalar extension on rational Hom sends an ordinary arrow to its pullback. -/
def changeHom {K L : Type} [Field K] [Field L] (φ : K →+* L) {X Y : GroupScheme K} :
    QHom X Y →ₗ[ℚ] QHom ((baseChange φ).obj X) ((baseChange φ).obj Y) := by
  let F := baseChange φ
  let : F.Additive := additive_mapCommGrp (Over.pullback (Spec.map (CommRingCat.ofHom φ)))
  exact (F.mapAddHom (X:=X) (Y:=Y)).toIntLinearMap.baseChange ℚ

@[simp] theorem changeHom_tmul {K L : Type} [Field K] [Field L] (φ : K →+* L)
    {X Y : GroupScheme K} (r : ℚ) (f : X ⟶ Y) :
    changeHom φ (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] (baseChange φ).map f := by rfl

variable {L : Type} [Field L] [CharZero L]
abbrev pull (σ : Gal(L/ℚ)) (J : GroupScheme L) := (baseChange σ.toRingHom).obj J
abbrev Maps (J : GroupScheme L) := (σ : Gal(L/ℚ)) → QHom (pull σ J) J

/-- Compatibility is precisely the commutative square in Guitart's Definition
2.1. Both composites are evaluated in the category up to isogeny. -/
def Compatible (J : GroupScheme L) (μ : Maps J) : Prop :=
  ∀ σ, (∃ ν : QHom J (pull σ J), comp (μ σ) ν = (1:ℚ) ⊗ₜ[ℤ] 𝟙 (pull σ J) ∧
    comp ν (μ σ) = (1:ℚ) ⊗ₜ[ℤ] 𝟙 J) ∧
    ∀ z : QEnd J, comp (asHom (pull σ J) (change σ.toRingHom J z)) (μ σ) =
      comp (μ σ) (asHom J z)

/-- The geometric multiplication law defining the central cocycle on p. 594.
The first factor identifies pullback by στ with iterated pullback. -/
def Multiplier (J : GroupScheme L) (μ : Maps J) (c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ) : Prop :=
  ∀ σ τ, let i : pull (σ*τ) J ≅ pull σ (pull τ J) :=
      WittAscent.baseChangeCompIso τ.toRingHom σ.toRingHom J
    comp ((1:ℚ) ⊗ₜ[ℤ] i.hom) (comp (changeHom σ.toRingHom (μ τ)) (μ σ)) =
      (↑(c (σ,τ)) : ℚ) • μ (σ*τ)

/-- Choosing one compatible arrow per element of a finite Galois group uses
only the actual rational homomorphisms supplied at each conjugate. -/
theorem choose_maps (J : GroupScheme L)
    (given : ∀ σ : Gal(L/ℚ), ∃ (m : QHom (pull σ J) J) (n : QHom J (pull σ J)),
      comp m n = (1:ℚ) ⊗ₜ[ℤ] 𝟙 (pull σ J) ∧ comp n m = (1:ℚ) ⊗ₜ[ℤ] 𝟙 J ∧
      ∀ z : QEnd J, comp (asHom (pull σ J) (change σ.toRingHom J z)) m =
        comp m (asHom J z)) : ∃ μ : Maps J, Compatible J μ := by
  choose μ ν l r h using given
  exact ⟨μ,fun σ => ⟨⟨ν σ,l σ,r σ⟩,h σ⟩⟩

end
end ZOverQ.Qualitative.GuitartCocycle

#print axioms ZOverQ.Qualitative.GuitartCocycle.changeHom_tmul
#print axioms ZOverQ.Qualitative.GuitartCocycle.Multiplier
#print axioms ZOverQ.Qualitative.GuitartCocycle.choose_maps
