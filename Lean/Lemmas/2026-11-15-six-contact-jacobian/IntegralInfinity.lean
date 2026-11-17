import OrdinaryGeometry
import Mathlib.RingTheory.Etale.StandardEtale
import ChartBaseChange

/-! The two points over infinity form an explicit finite étale multisection. -/
open Polynomial AlgebraicGeometry CategoryTheory
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.OrdinaryModel
noncomputable section
variable {R : Type} [CommRing R]

/-- A standard étale presentation of the quadratic algebra obtained by adjoining
a square root of a unit when 2 is invertible. -/
def quadraticPair (u v : Rˣ) (h2 : (v:R)=2) : StandardEtalePair R where
  f := X^2-C (u:R)
  monic_f := monic_X_pow_sub_C _ (by decide : (2:ℕ) ≠ 0)
  g := 1
  cond := by
    let a : R := ↑v⁻¹ * (↑u⁻¹ : R)
    refine ⟨C a*X,-C (↑u⁻¹ : R),0,?_⟩
    have D : derivative (X^2-C (u:R)) = C (2:R)*X := by simp [map_ofNat]; ring
    rw [D,pow_zero]
    have hv : (2:R)*↑v⁻¹=1 := by rw [←h2]; simp
    have hcoeff : (2:R)*a = ↑u⁻¹ := by dsimp [a]; rw [← mul_assoc,hv,one_mul]
    calc
      _ = C ((2:R)*a)*X^2-C (↑u⁻¹ : R)*X^2+C ((↑u⁻¹:R)*(u:R)) := by simp only [map_mul]; ring
      _ = 1 := by rw [hcoeff]; simp

theorem etale_quadratic (u : Rˣ) (h2 : IsUnit (2:R)) : Algebra.Etale R (Cover (u:R)) := by
  let P := quadraticPair u h2.unit h2.unit_spec
  let S := Cover (u:R)
  let w : S := QuadraticAlgebra.omega
  have hw : w^2 = algebraMap R S u := by
    change (QuadraticAlgebra.omega : QuadraticAlgebra R (u:R) 0)^2 = _
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  have hx : P.HasMap w := by
    constructor
    · change aeval w (X^2-C (u:R))=0
      simp [hw]
    · change IsUnit (aeval w 1)
      simp
  let f := P.lift w hx
  have hr : P.X * P.X = (u:R) • (1:P.Ring) + (0:R) • P.X := by
    have h := P.hasMap_X.1
    change aeval P.X (X^2-C (u:R))=0 at h
    simp only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero] at h
    simpa [sq,Algebra.algebraMap_eq_smul_one] using h
  let g : S →ₐ[R] P.Ring := QuadraticAlgebra.lift (a := (u:R)) (b := 0) ⟨P.X,hr⟩
  have gw : g w = P.X := by simp [g,w,QuadraticAlgebra.lift]
  let e : P.Ring ≃ₐ[R] S := AlgEquiv.ofAlgHom f g
    (by apply QuadraticAlgebra.algHom_ext; change f (g w) = w; rw [gw]; exact P.lift_X _ _)
    (by apply P.hom_ext; change g (f P.X)=P.X; rw [show f P.X=w from P.lift_X _ _,gw])
  exact Algebra.Etale.of_equiv e

/-- The two conjugate points above z=0 give a point after the quadratic
algebra R[sqrt(s)], without requiring the exterior scalar s to be square in R. -/
def infinityPoint (s t : R) : SpecOver (R := R) (Cover s) ⟶ model s t := by
  let T := Cover s
  let w : T := QuadraticAlgebra.omega
  have hw : w^2=aeval (0:T) (C s*infinityForm t) := by
    change (QuadraticAlgebra.omega : Cover s)^2 = _
    rw [infinity_coeffs]
    simp [T,Cover,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  let ev := IntegralCover.affinePoint (C s*infinityForm t) (0:T) w hw
  let j : SpecOver (R:=R) T ⟶ SpecOver (R:=R) (Cover (C s*infinityForm t)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ev.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [←Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext ev.comp_algebraMap))
  exact j ≫ chartInclusion R _ _ (overlap s t) true

theorem infinity_cover [Nontrivial R] (u : Rˣ) (t : R) (h2 : IsUnit (2:R)) :
    Module.Finite R (Cover (u:R)) ∧ Algebra.Etale R (Cover (u:R)) ∧
    Module.finrank R (Cover (u:R)) = 2 ∧
    Nonempty (SpecOver (R := R) (Cover (u:R)) ⟶ model (u:R) t) := by
  classical
  refine ⟨inferInstance,etale_quadratic u h2,?_,⟨infinityPoint _ _⟩⟩
  simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (u:R) 0)

end
end ZInQBlueprint.OrdinaryModel
#print axioms ZInQBlueprint.OrdinaryModel.etale_quadratic
#print axioms ZInQBlueprint.OrdinaryModel.infinityPoint
#print axioms ZInQBlueprint.OrdinaryModel.infinity_cover
