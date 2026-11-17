import SixShimuraChart
import BinaryCover

/-! The affine y≠0 portion of the discriminant-six Shimura conic. With
t=3z/y and s=3x/y it is s²=−t²−27. The involution w₃ negates s. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift BinaryCover NormalDescent
noncomputable section

abbrev ConicRing := Cover (-(X : ℚ[X])^2 - 27)

theorem fixed_polynomials (a : ConicRing) :
    star a = a ↔ ∃! b : ℚ[X], algebraMap ℚ[X] ConicRing b = a := by
  constructor
  · intro h
    have hneg : -a.im = a.im := congrArg QuadraticAlgebra.im h
    have hz : a.im = 0 := by
      have e : (2 : ℚ[X]) * a.im = 0 := by linear_combination -hneg
      exact (mul_eq_zero.mp e).resolve_left (by norm_num)
    refine ⟨a.re,QuadraticAlgebra.ext rfl hz.symm,?_⟩
    intro b hb
    exact congrArg QuadraticAlgebra.re hb
  · rintro ⟨b,hb,_⟩
    rw [← hb]
    apply QuadraticAlgebra.ext <;> simp

/-- A rational homomorphism of affine coordinate algebras, on spectra. -/
def specHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) : SpecOver (R := ℚ) B ⟶ SpecOver (R := ℚ) A := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext f.commutes

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C] (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) :
    specHom g ≫ specHom f = specHom (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

abbrev Line := SpecOver (R := ℚ) ℚ[X]
abbrev Conic := SpecOver (R := ℚ) ConicRing
abbrev geometricDomain := SpecOver (R := ℚ) Qbar

def quotientMorphism : Conic ⟶ Line := specHom (IsScalarTower.toAlgHom ℚ ℚ[X] ConicRing)
def linePoint (t : Qbar) : geometricDomain ⟶ Line := specHom (aeval t)

def galoisPoint (σ : Gal) : geometricDomain ⟶ geometricDomain := specHom σ.toAlgHom

theorem linePoint_conjugate (t : Qbar) (σ : Gal) :
    galoisPoint σ ≫ linePoint t = linePoint (σ t) := by
  rw [galoisPoint,linePoint,spec_comp]
  congr 1
  ext
  simp

def radicalCoordinate (p : ConicPoint) : Qbar := 12 / p.y

theorem conic_equation (p : ConicPoint) :
    (radicalCoordinate p)^2 = -p.quotientCoordinate^2-27 := by
  dsimp [radicalCoordinate,ConicPoint.quotientCoordinate]
  field_simp [p.y_ne]
  linear_combination 9*p.onCurve

def conicAlgebraPoint (p : ConicPoint) : ConicRing →ₐ[ℚ] Qbar := by
  let eval := aeval (R := ℚ) p.quotientCoordinate
  letI : Algebra ℚ[X] Qbar := eval.toAlgebra
  letI : IsScalarTower ℚ ℚ[X] Qbar := IsScalarTower.of_algebraMap_eq (fun r => (eval.commutes r).symm)
  let a := radicalCoordinate p
  have h : a*a = (-(X : ℚ[X])^2-27) • (1 : Qbar) + (0 : ℚ[X]) • a := by
    rw [← Algebra.algebraMap_eq_smul_one,zero_smul,add_zero]
    change a*a = eval _
    simpa [eval,a,sq,map_ofNat] using conic_equation p
  exact (QuadraticAlgebra.lift ⟨a,h⟩).restrictScalars ℚ

theorem quotient_on_point (p : ConicPoint) :
    specHom (conicAlgebraPoint p) ≫ quotientMorphism = linePoint p.quotientCoordinate := by
  rw [quotientMorphism,spec_comp,linePoint]
  congr 1
  ext
  change (aeval p.quotientCoordinate) X * 1 + (aeval p.quotientCoordinate) 0 * radicalCoordinate p = _
  simp

theorem deck_coordinate (p : ConicPoint) :
    radicalCoordinate p.w3 = -radicalCoordinate p ∧
      p.w3.quotientCoordinate = p.quotientCoordinate := by
  constructor
  · exact div_neg (12 : Qbar)
  · exact ((quotient_eq_iff p p.w3).mpr (Or.inr rfl)).symm

end
end ZInQBlueprint.ShimuraAtlas

#print axioms ZInQBlueprint.ShimuraAtlas.fixed_polynomials
#print axioms ZInQBlueprint.ShimuraAtlas.spec_comp
#print axioms ZInQBlueprint.ShimuraAtlas.linePoint_conjugate
#print axioms ZInQBlueprint.ShimuraAtlas.conic_equation
#print axioms ZInQBlueprint.ShimuraAtlas.quotient_on_point
#print axioms ZInQBlueprint.ShimuraAtlas.deck_coordinate
