import PicardConjugateEnd
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! Clearing the denominators of two inverse rational homomorphisms. -/
open CategoryTheory AlgebraicGeometry ZInQBlueprint.AbelianModel
open scoped TensorProduct ZInQBlueprint.NormalDescent
namespace ZOverQ.Qualitative.PicardIntegralHom
open PicardConjugateEnd
noncomputable section
section
variable {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}

abbrev integral (X Y : C) := TensorProduct.mk ℤ ℚ (X ⟶ Y) 1

private theorem comp_integral (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp (integral X Y f) (integral Y Z g) = integral X Z (f ≫ g) := by
  simp [integral]

private theorem scale_left (a : ℤ) (f : QHom X Y) (g : QHom Y Z) :
    comp (a • f) g = a • comp f g := by rw [map_zsmul]; rfl

private theorem scale_right (a : ℤ) (f : QHom X Y) (g : QHom Y Z) :
    comp f (a • g) = a • comp f g := map_zsmul _ _ _

/-- A rational isomorphism between two objects of a preadditive category has
integral representatives whose two composites are the same nonzero integer
multiple of the identity. This holds even for Hom groups with torsion. -/
theorem integral_representatives (μ : QHom X Y) (ν : QHom Y X)
    (hm : comp μ ν = integral X X (𝟙 X)) (hn : comp ν μ = integral Y Y (𝟙 Y)) :
    ∃ (f : X ⟶ Y) (g : Y ⟶ X) (n k : ℤ), n ≠ 0 ∧ k ≠ 0 ∧
      f ≫ g = n • 𝟙 X ∧ g ≫ f = n • 𝟙 Y ∧ integral X Y f = k • μ := by
  let S := nonZeroDivisors ℤ
  obtain ⟨⟨f,a⟩,hf⟩ := IsLocalizedModule.surj S (integral X Y) μ
  obtain ⟨⟨g,b⟩,hg⟩ := IsLocalizedModule.surj S (integral Y X) ν
  change (a:ℤ) • μ = integral X Y f at hf
  change (b:ℤ) • ν = integral Y X g at hg
  let n : ℤ := (a:ℤ)*(b:ℤ)
  have ea : integral X X (f ≫ g) = integral X X (n • 𝟙 X) := by
    rw [← comp_integral,← hf,← hg,scale_left,scale_right,hm,map_zsmul,mul_smul]
  have eb : integral Y Y (g ≫ f) = integral Y Y (n • 𝟙 Y) := by
    rw [← comp_integral,← hf,← hg,scale_left,scale_right,hn,map_zsmul,smul_smul,mul_comm (b:ℤ)]
  obtain ⟨u,hu⟩ := (IsLocalizedModule.eq_iff_exists S (integral X X)).mp ea
  obtain ⟨v,hv⟩ := (IsLocalizedModule.eq_iff_exists S (integral Y Y)).mp eb
  change (u:ℤ) • (f ≫ g) = (u:ℤ) • (n • 𝟙 X) at hu
  change (v:ℤ) • (g ≫ f) = (v:ℤ) • (n • 𝟙 Y) at hv
  have nz (z : S) : (z:ℤ) ≠ 0 := nonZeroDivisors.ne_zero z.2
  let m : ℤ := (v:ℤ)*(u:ℤ)
  refine ⟨m • f,g,m*n,m*(a:ℤ),mul_ne_zero (mul_ne_zero (nz _) (nz _)) (mul_ne_zero (nz _) (nz _)),
    mul_ne_zero (mul_ne_zero (nz _) (nz _)) (nz _),?_,?_,?_⟩
  · rw [Preadditive.zsmul_comp,mul_smul,mul_smul,hu]
    exact (mul_smul _ _ _).symm
  · rw [Preadditive.comp_zsmul,show m = (u:ℤ)*(v:ℤ) by exact mul_comm _ _,mul_smul,mul_smul,hv]
    exact (mul_smul _ _ _).symm
  · rw [map_zsmul,← hf]
    exact (mul_smul _ _ _).symm
end

private abbrev underlying {K : Type} [Field K] {A B : GroupScheme K} (f : A ⟶ B) :=
  f.hom.hom.hom.left

/-- Nonzero integer multiplication on the source is finite, and on the
target it is surjective. Under these standard abelian-variety facts an
integral representative of the compatible quasi-isogeny is a finite
surjective morphism of group schemes. -/
theorem isogeny_of_quasi {K : Type} [Field K] {A B : GroupScheme K}
    (μ : QHom A B) (ν : QHom B A) (hm : comp μ ν = integral A A (𝟙 A))
    (hn : comp ν μ = integral B B (𝟙 B)) (sep : IsSeparated B.X.hom)
    (finite : ∀ n : ℤ, n ≠ 0 → IsFinite (underlying (n • 𝟙 A)))
    (surj : ∀ n : ℤ, n ≠ 0 → Surjective (underlying (n • 𝟙 B))) :
    ∃ (f : A ⟶ B) (k : ℤ), k ≠ 0 ∧ IsFinite (underlying f) ∧ Surjective (underlying f) ∧
      integral A B f = k • μ := by
  obtain ⟨f,g,n,k,hn,hk,fg,gf,hvalue⟩ := integral_representatives μ ν hm hn
  have hfg : IsFinite (underlying f ≫ underlying g) := by
    change IsFinite (underlying (f ≫ g))
    rw [fg]; exact finite n hn
  have hgf : Surjective (underlying g ≫ underlying f) := by
    change Surjective (underlying (g ≫ f))
    rw [gf]; exact surj n hn
  have hsep : IsSeparated (underlying g ≫ A.X.hom) := by
    rw [show underlying g ≫ A.X.hom = B.X.hom from g.hom.hom.hom.w]
    exact sep
  have : IsSeparated (underlying g) := IsSeparated.of_comp _ A.X.hom
  exact ⟨f,k,hk,IsFinite.of_comp _ (underlying g),Surjective.of_comp (underlying g) _,hvalue⟩

end
end ZOverQ.Qualitative.PicardIntegralHom
#print axioms ZOverQ.Qualitative.PicardIntegralHom.integral_representatives
#print axioms ZOverQ.Qualitative.PicardIntegralHom.isogeny_of_quasi
