import PicardAssembly
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Finite powers of abelian schemes and their reduction under isogeny. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open ZInQBlueprint.AbelianModel

namespace ZOverQ.Qualitative.AbelianPowers
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S]

/-- The product commutative group scheme over the base. -/
def product (A B : GroupScheme R) : GroupScheme R := ⟨A.X ⊗ B.X⟩

/-- The power with n+1 factors. -/
def power (A : GroupScheme R) : ℕ → GroupScheme R
  | 0 => A
  | n+1 => product (power A n) A

theorem abelian_product {A B : GroupScheme R} (a : IsAbelianScheme A) (b : IsAbelianScheme B) :
    IsAbelianScheme (product A B) := by
  let := a.proper
  let := b.proper
  let := a.smooth
  let := b.smooth
  let := a.geometricallyConnected
  let := b.geometricallyConnected
  let fst := pullback.fst A.X.hom B.X.hom
  change IsAbelianScheme ⟨A.X ⊗ B.X⟩
  exact ⟨inferInstanceAs (IsProper (fst ≫ A.X.hom)), inferInstanceAs (Smooth (fst ≫ A.X.hom)),
    GeometricallyConnected.comp fst A.X.hom⟩

theorem abelian_power {A : GroupScheme R} (a : IsAbelianScheme A) (n : ℕ) :
    IsAbelianScheme (power A n) := by
  induction n with
  | zero => exact a
  | succ n ih => exact abelian_product ih a

/-- Extension of the generic fibre of any product of models agrees with the
product of the given isomorphisms on generic fibres. -/
def baseChangePowerIso (f : R →+* S) {A : GroupScheme R} {B : GroupScheme S}
    (e : (baseChange f).obj A ≅ B) : (n : ℕ) → (baseChange f).obj (power A n) ≅ power B n
  | 0 => e
  | n+1 => by
    let U := CommGrp.forget₂Grp (Over (Spec (.of S)))
    let F := (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp
    apply (CommGrp.fullyFaithfulForget₂Grp _).preimageIso
    change F.obj ((power A n).toGrp ⊗ A.toGrp) ≅ (power B n).toGrp ⊗ B.toGrp
    exact (Functor.Monoidal.μIso F _ _).symm ≪≫
      tensorIso (U.mapIso (baseChangePowerIso f e n)) (U.mapIso e)

open Picard.Assembly LocalSupport
variable (p : ℕ) [Fact p.Prime]

/-- The actual product model over the unramified Witt ring gives good reduction
of each positive power of the specified local Jacobian. -/
theorem goodWitt_power (k : Subfield (Residues p))
    {J : GroupScheme (FractionRing (WittVector p k))} (h : GoodWitt p k J) (n : ℕ) :
    GoodWitt p k (power J n) := by
  obtain ⟨M,hM,⟨e⟩⟩ := h
  exact ⟨power M n, abelian_power hM n, ⟨baseChangePowerIso _ e n⟩⟩

/-- Serre–Tate transfers good reduction to the rational factor directly along
a local isogeny from a power of the Jacobian. Only surjectivity is required. -/
theorem reduction_of_power (st : SerreTateAt p) {B : GroupScheme ℚ} (hB : IsAbelianScheme B)
    (k : Subfield (Residues p)) [Finite k] (n : ℕ)
    (J : GroupScheme (FractionRing (WittVector p k))) (hJ : IsAbelianScheme J)
    (good : GoodWitt p k J)
    (quotient : letI := wittFractionAlgebra p k
      ∃ f : power J n ⟶ (baseChange (algebraMap ℚ_[p] (FractionRing (WittVector p k)))).obj
        ((baseChange (algebraMap ℚ ℚ_[p])).obj B), Surjective f.hom.hom.hom.left) :
    GoodReductionAt p B := by
  obtain ⟨f, hf⟩ := quotient
  exact reduction_of_unramified_quotient p st hB
    ⟨k, inferInstance, power J n, f, abelian_power hJ n, goodWitt_power p k good n, hf⟩

end
end ZOverQ.Qualitative.AbelianPowers

#print axioms ZOverQ.Qualitative.AbelianPowers.abelian_product
#print axioms ZOverQ.Qualitative.AbelianPowers.abelian_power
#print axioms ZOverQ.Qualitative.AbelianPowers.baseChangePowerIso
#print axioms ZOverQ.Qualitative.AbelianPowers.goodWitt_power
#print axioms ZOverQ.Qualitative.AbelianPowers.reduction_of_power
