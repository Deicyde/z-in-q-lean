import BinaryCover
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Polynomial.Taylor

/-! The infinitesimal lifting criterion for a square root of a separable polynomial. -/
open Polynomial
namespace ZInQBlueprint.BinaryCover

noncomputable section
variable {K : Type} [Field K] {B : Type} [CommRing B] [Algebra K B]

/-- An algebra map from the double cover is determined by the chosen coordinates. -/
def affinePoint (f : K[X]) (x y : B) (h : y^2 = aeval x f) : Cover f →ₐ[K] B where
  toFun z := aeval x z.re + aeval x z.im * y
  map_one' := by change aeval x 1 + aeval x 0*y = 1; simp
  map_zero' := by change aeval x 0 + aeval x 0*y = 0; simp
  map_add' a b := by
    change aeval x (a.re+b.re) + aeval x (a.im+b.im)*y = _
    simp only [map_add]; ring
  map_mul' a b := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_zero, zero_mul]
    linear_combination -((aeval x a.im)*(aeval x b.im)) * h
  commutes' k := by
    change aeval x (C k) + aeval x 0*y = _
    simp

theorem polynomial_image {f : K[X]} (g : Cover f →ₐ[K] B) (p : K[X]) :
    g (algebraMap K[X] (Cover f) p) =
      aeval (g (algebraMap K[X] (Cover f) X)) p := by
  let s := IsScalarTower.toAlgHom K K[X] (Cover f)
  have e : g.comp s = aeval (g (algebraMap K[X] (Cover f) X)) := by
    apply Polynomial.algHom_ext
    simp [s]
  exact DFunLike.congr_fun e p

theorem ordinate_square {f : K[X]} (g : Cover f →ₐ[K] B) :
    g QuadraticAlgebra.omega ^ 2 = aeval (g (algebraMap K[X] (Cover f) X)) f := by
  rw [← map_pow, QuadraticAlgebra.omega_pow_two_eq_add, zero_smul, add_zero,
    ← Algebra.algebraMap_eq_smul_one, polynomial_image]

theorem affinePoint_image {f : K[X]} (g : Cover f →ₐ[K] B) (z : Cover f) :
    g z = aeval (g (algebraMap K[X] (Cover f) X)) z.re +
      aeval (g (algebraMap K[X] (Cover f) X)) z.im * g QuadraticAlgebra.omega := by
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul, polynomial_image g z.re,
    polynomial_image g z.im]

/-- Correct lifted coordinates over a square-zero ideal using a Bézout identity. -/
theorem repair_coordinates (f : K[X]) (hf : IsCoprime f f.derivative) [Invertible (2 : K)]
    (I : Ideal B) (hI : I^2 = ⊥) (x y : B) (hd : y^2 - aeval x f ∈ I) :
    ∃ X Y : B, X - x ∈ I ∧ Y - y ∈ I ∧ Y^2 = aeval X f := by
  obtain ⟨a,b,hab⟩ := hf
  let d := y^2 - aeval x f
  have hz : d^2 = 0 := by
    have h := Ideal.mul_mem_mul hd hd
    rwa [← sq, hI, Ideal.mem_bot, ← sq] at h
  let A := aeval x a
  let D := aeval x f.derivative
  let E := aeval x b
  let c := algebraMap K B (⅟(2:K))
  have hc : c*2=1 := by
    have h := congrArg (algebraMap K B) (invOf_mul_self (2:K))
    simpa only [c,map_mul,map_ofNat,map_one] using h
  have he : A * aeval x f + E*D = 1 := by
    simpa [A,E,D] using congrArg (aeval x) hab
  refine ⟨x+E*d, y-(c*A*y)*d, ?_, ?_, ?_⟩
  · simpa using I.mul_mem_left E hd
  · simpa using I.neg_mem (I.mul_mem_left (c*A*y) hd)
  · rw [aeval_add_of_sq_eq_zero f x (E*d) (by rw [mul_pow,hz,mul_zero])]
    have hf' : aeval x f = y^2-d := by simp [d]
    change (y-c*A*y*d)^2 = aeval x f+D*(E*d)
    rw [hf'] at he ⊢
    linear_combination (c*A*y)^2 * hz - A * hz - d*he - A*y^2*d*hc

/-- A separable affine equation in characteristic different from two is smooth over its field. -/
theorem smooth_cover (f : K[X]) (hf : IsCoprime f f.derivative) [Invertible (2 : K)] :
    Algebra.Smooth K (Cover f) := by
  constructor
  · apply Algebra.FormallySmooth.iff_comp_surjective.mpr
    intro B _ _ I hI g
    let q := Ideal.Quotient.mkₐ K I
    let v := g (algebraMap K[X] (Cover f) X)
    let w := g QuadraticAlgebra.omega
    obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective v
    obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective w
    have qx : q x = v := hx
    have qy : q y = w := hy
    have hd : y^2 - aeval x f ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q (y^2 - aeval x f) = 0
      rw [map_sub,map_pow,← aeval_algHom_apply q,qx,qy]
      exact sub_eq_zero.mpr (ordinate_square g)
    obtain ⟨x',y',hx',hy',h'⟩ := repair_coordinates f hf I hI x y hd
    have eqQ {s t : B} (h : s-t ∈ I) : q s = q t := by
      apply sub_eq_zero.mp
      rw [← map_sub q]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr h
    refine ⟨affinePoint f x' y' h', AlgHom.ext fun z => ?_⟩
    change q (aeval x' z.re + aeval x' z.im*y') = g z
    rw [map_add,map_mul,← aeval_algHom_apply q,← aeval_algHom_apply q,eqQ hx',eqQ hy',qx,qy]
    exact (affinePoint_image g z).symm
  · apply Algebra.FinitePresentation.of_finiteType.mp
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X]) inferInstance

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.repair_coordinates
#print axioms ZInQBlueprint.BinaryCover.smooth_cover
