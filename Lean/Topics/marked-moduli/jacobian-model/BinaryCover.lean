import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Polynomial.Basic

/-! The affine double cover y²=f and its coordinate changes as schemes over the base. -/

open CategoryTheory AlgebraicGeometry Polynomial

namespace ZInQBlueprint.BinaryCover

abbrev Cover {R : Type*} [CommRing R] (f : R) := QuadraticAlgebra R f 0

/-- The map brings the square relation for the source to the square relation for
the target. On coordinate rings it sends y to u y'. -/
def squareEquiv {K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R]
    [Algebra K S] {f : R} {g : S} (e : R ≃ₐ[K] S) (u : Sˣ)
    (h : e f = (u : S)^2*g) : Cover f ≃ₐ[K] Cover g where
  toFun z := ⟨e z.re, u*e z.im⟩
  invFun z := ⟨e.symm z.re, e.symm ((↑u⁻¹ : S)*z.im)⟩
  left_inv z := by ext <;> simp [← mul_assoc]
  right_inv z := by ext <;> simp [← mul_assoc]
  map_mul' x y := by ext <;> simp [h] <;> ring
  map_add' x y := by ext <;> simp [mul_add]
  commutes' r := by
    change (⟨e (algebraMap K R r), (u : S)*e 0⟩ : Cover g) = ⟨algebraMap K S r, 0⟩
    simp

noncomputable def SpecOver {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A] :
    Over (Spec (.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- An algebra isomorphism induces an isomorphism of affine schemes over the base. -/
noncomputable def specIso {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) : SpecOver (R := R) B ≅ SpecOver A := by
  refine Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R A)) = Spec.map (CommRingCat.ofHom (algebraMap R B))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

noncomputable def dilate {R : Type*} [CommRing R] (u : Rˣ) : R[X] ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (aeval (C (u : R)*X)) (aeval (C (↑u⁻¹ : R)*X))
    (by ext; simp [aeval_mul, ← mul_assoc, ← C_mul])
    (by ext; simp [aeval_mul, ← mul_assoc, ← C_mul])

@[simp] theorem dilate_X {R : Type*} [CommRing R] (u : Rˣ) : dilate u X = C (u : R) * X :=
  aeval_X _

@[simp] theorem dilate_C {R : Type*} [CommRing R] (u : Rˣ) (a : R) : dilate u (C a) = C a :=
  (dilate u).commutes a

end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.squareEquiv
#print axioms ZInQBlueprint.BinaryCover.specIso
#print axioms ZInQBlueprint.BinaryCover.dilate
