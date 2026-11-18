import GuitartDescent
import PicardLocalization

namespace ZOverQ.Qualitative.GuitartDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZInQBlueprint
open CategoryTheory.Functor MonoidalCategory MonObj
open NormalDescent AbelianModel UniformDescent
open scoped NormalDescent TensorProduct CategoryTheory.Obj
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable (M : FiniteGaloisIntermediateField ℚ Qbar)
local notation "F" => baseChange (algebraMap M Qbar)

/-- The equality of rationalized geometric homomorphisms in Guitart's
splitting formula, restricted to the subgroup fixing M. -/
def GeometricLaw {A B : GroupScheme M}
    (b : Gal(M/ℚ) → Qbarˣ)
    (φ : coefficientField b →ₐ[ℚ] (ℚ ⊗[ℤ] End ((F).obj A)))
    (κ : (F).obj A ⟶ (F).obj B) : Prop :=
  ∀ σ : Gal(Qbar/M), (1:ℚ) ⊗ₜ[ℤ] (conjugate κ σ) = afterHom κ
    (φ (↑((coefficientUnit b (restriction M (σ.restrictScalars ℚ)))⁻¹) : coefficientField b))

/-- Nonzero integer multiplication on a geometric abelian variety is finite,
flat and surjective (Milne, Abelian Varieties, Theorem 8.2). -/
def Multiplications : Prop :=
  ∀ A : GroupScheme Qbar, IsAbelianScheme A → ∀ z : ℤ, z ≠ 0 →
    let f := (z • 𝟙 A).hom.hom.hom.left
    IsFinite f ∧ Flat f ∧ Surjective f

/-- For abelian varieties the geometric assumptions in the descent-of-morphisms
theorem follow from smoothness and properness. -/
theorem descended_isogeny {A B : GroupScheme M} (a : IsAbelianScheme A) (d : IsAbelianScheme B)
    (b : Gal(M/ℚ) → Qbarˣ) (c : Gal(M/ℚ) × Gal(M/ℚ) → ℚˣ) (hc : c (1,1) = 1)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h))
    (φ : coefficientField b →ₐ[ℚ] (ℚ ⊗[ℤ] End ((F).obj A)))
    (κ : (F).obj A ⟶ (F).obj B) (hf : IsFinite κ.hom.hom.hom.left) (hs : Surjective κ.hom.hom.hom.left)
    (multiply : Multiplications) (law : GeometricLaw M b φ κ) :
    ∃ f : A ⟶ B, IsFinite f.hom.hom.hom.left ∧ Surjective f.hom.hom.hom.left := by
  let : LocallyOfFiniteType A.X.hom := (finite_presentation_data a).2.2.2.1
  let : IsReduced A.X.left := isReduced_of_smooth_over_field (g:=A.X.hom) a.smooth
  let : IsProper B.X.hom := d.proper
  obtain ⟨f,h,_⟩ := isogeny_of_splitting_law M a.proper (inferInstanceAs (IsSeparated B.X.hom))
    b c hc hb φ κ hf hs (multiply _ (isAbelianScheme_baseChange _ a)) law
  exact ⟨f,h.2⟩

end
end ZOverQ.Qualitative.GuitartDescent

#print axioms ZOverQ.Qualitative.GuitartDescent.GeometricLaw

#print axioms ZOverQ.Qualitative.GuitartDescent.descended_isogeny
