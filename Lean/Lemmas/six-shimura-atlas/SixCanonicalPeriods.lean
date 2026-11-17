import SixAtlasEndpoint
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-! Uniform inputs on the upper half-plane, with the marked algebraic
representative selected prior to the choice of its complex uniformizer. -/
open CategoryTheory AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel
noncomputable section

/-- Projective coordinates [A:Y:Z] from Theorem 3.10, without a
choice of a common analytic scalar. The ordinary conic point is [4:y:z]. -/
def LiesAbove (ι : Qbar →+* ℂ) (A Y Z : ℂ) (p : ConicPoint) : Prop :=
  A ≠ 0 ∧ 4*Y = A*ι p.y ∧ 4*Z = A*ι p.z

/-- An exact comparison between the three modular coefficients and the raw
sextic in Corollary 3.15, valid even if the common modular factor is
transcendental. The two numerical constants are chosen once for the family. -/
theorem raw_equation (ι : Qbar →+* ℂ) {A Y Z : ℂ} {p : ConicPoint}
    (above : LiesAbove ι A Y Z p) (e l : Qbar) (x z : ℂ) :
    modularBinary A (ι e*Y) (2*ι l*Z) x z =
      A * modularBinary 1 (3*ι (e*p.y/3)/4) (ι (l*p.z)/2) x z := by
  obtain ⟨_,hY,hZ⟩ := above
  have h₁ : ι e*Y = A*(3*ι (e*p.y/3)/4) := by
    rw [map_div₀,map_mul,map_ofNat]
    linear_combination ι e / 4 * hY
  have h₂ : 2*ι l*Z = A*(ι (l*p.z)/2) := by
    rw [map_mul]
    linear_combination ι l / 2 * hZ
  rw [h₁,h₂]
  unfold modularBinary
  ring

/-- Distinct analytic and algebraic inputs. The functions A,Y,Z stand for
h₄³,h₆²,h₁₂. The constant generator choices and the uniformization are
global. The modular equation is used only above actual off-contact fibres. -/
structure CanonicalPeriods {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ι : Qbar →+* ℂ) (hom : HomBaseChange ι) where
  e : Qbar
  l : Qbar
  e_square : e^2 = -6
  l_square : l^2 = 2
  A : UpperHalfPlane → ℂ
  Y : UpperHalfPlane → ℂ
  Z : UpperHalfPlane → ℂ
  surface : UpperHalfPlane → GroupScheme ℂ
  covers : ∀ p : ConicPoint, ∃ τ : UpperHalfPlane, LiesAbove ι (A τ) (Y τ) (Z τ) p
  representative : ∀ (j : ℚ), OutsideCM j → ∀ p : ConicPoint, p.y^2 = 9*(j:Qbar) →
    ∃ w : PeriodRepresentative C chart ι hom p, ∀ τ : UpperHalfPlane,
      LiesAbove ι (A τ) (Y τ) (Z τ) p → Nonempty ((baseChange ι).obj w.surface ≅ surface τ)
  cor315 : ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet) (p : ConicPoint)
    (hp : FibrePoint u p) (τ : UpperHalfPlane), LiesAbove ι (A τ) (Y τ) (Z τ) p →
    Nonempty (surface τ ≅ (baseChange ι).obj (modularJacobian hu hp e_square l_square))

theorem modular_of_canonical {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} {ι : Qbar →+* ℂ} {hom : HomBaseChange ι}
    (P : CanonicalPeriods C chart ι hom) : ModularComparison C chart ι hom := by
  intro u hu ordinary
  obtain ⟨p,hp⟩ := fibre_nonempty hu
  obtain ⟨τ,hτ⟩ := P.covers p
  obtain ⟨w,hw⟩ := P.representative (SixContact.J u) ordinary p hp.y_square
  exact ⟨p,hp,P.e,P.l,P.e_square,P.l_square,w,
    ⟨(hw τ hτ).some ≪≫ (P.cor315 u hu p hp τ hτ).some⟩⟩

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.raw_equation
#print axioms ZInQBlueprint.ShimuraAtlas.modular_of_canonical
