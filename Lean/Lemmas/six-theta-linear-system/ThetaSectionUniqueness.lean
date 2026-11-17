import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleZeroSchemeIdealEq
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.SectionsOf
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A one-dimensional space of global sections determines the entire zero ideal.
The scalar action comes from the structural morphism to the ground field.
No affine-cover hypothesis is imposed on the scheme. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.ThetaLinearSystem
noncomputable section
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Dimension of global sections for the actual base-field action. -/
abbrev rankH0 (c : X ⟶ Spec (.of k)) (L : X.Modules) : ℕ :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L ⊤
  Module.finrank k Γ(L, ⊤)

private theorem eq_zero_of_top {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)
    (h : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = 0) : s = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  have hm : m = Scheme.Modules.ofUnitSection U m • Scheme.Modules.toUnitSection U (1 : Γ(X,U)) := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h1 : Scheme.Modules.toUnitSection U (1 : Γ(X,U)) =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one]
  have hn : s.app U ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (Scheme.Modules.toUnitSection ⊤ 1)) = L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
    have nat := s.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op
    exact congr($(nat) (Scheme.Modules.toUnitSection ⊤ 1))
  rw [hm, Scheme.Modules.Hom.app_smul, h1, hn, h, map_zero, smul_zero, Scheme.Modules.Hom.zero_app]
  rfl

/-- Global nonzero sections cut out the very same ideal, including multiplicities. -/
theorem zeroScheme_eq (c : X ⟶ Spec (.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (h0 : rankH0 c L = 1)
    (s t : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) (ht : t ≠ 0) :
    Scheme.Modules.zeroSchemeIdeal s = Scheme.Modules.zeroSchemeIdeal t := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L ⊤
  have vs : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) ≠ 0 := fun h => hs (eq_zero_of_top s h)
  have vt : t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) ≠ 0 := fun h => ht (eq_zero_of_top t h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ vs).1 h0
    (t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
  have h : a ≠ 0 := by
    rintro rfl
    exact vt (by rw [← ha, zero_smul])
  exact hL.zeroSchemeIdeal_eq_of_app_eq_smul s t (algebraMap k Γ(X,⊤) a)
    ((IsUnit.mk0 a h).map _) ha.symm

end
end ZInQBlueprint.ThetaLinearSystem
#print axioms ZInQBlueprint.ThetaLinearSystem.zeroScheme_eq
