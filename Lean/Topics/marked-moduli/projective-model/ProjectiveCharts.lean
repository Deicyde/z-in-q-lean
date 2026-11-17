import SquareRootSmooth
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Reverse

/-! Affine equations in the four-quadric projective embedding of a binary sextic. -/
namespace ZInQBlueprint.SexticEmbedding
variable {R : Type*} [CommRing R]

/-- Dehomogenize a binary sextic at Z=1. -/
def sextic (c : Fin 7 → R) (x : R) : R :=
  c 0+c 1*x+c 2*x^2+c 3*x^3+c 4*x^4+c 5*x^5+c 6*x^6

/-- The binary form as a quadratic in the cubic Veronese coordinates. -/
def quadratic (c : Fin 7 → R) (A B C D : R) : R :=
  c 0*D^2+c 1*C*D+c 2*B*D+c 3*A*D+c 4*A*C+c 5*A*B+c 6*A^2

def equations (c : Fin 7 → R) (A B C D T : R) : Prop :=
  A*C=B^2 ∧ A*D=B*C ∧ B*D=C^2 ∧ T^2=quadratic c A B C D

/-- On D=1 the equations force B=C², A=C³ and the original square-root equation. -/
theorem finite_chart (c : Fin 7 → R) (a b x y : R) :
    equations c a b x 1 y ↔ a=x^3 ∧ b=x^2 ∧ y^2=sextic c x := by
  simp only [equations,mul_one]
  constructor
  · rintro ⟨_,hab,hb,hq⟩
    subst b
    have ha : a=x^3 := by rw [hab]; ring
    refine ⟨ha,rfl,?_⟩
    rw [hq,ha]
    unfold quadratic sextic
    ring
  · rintro ⟨rfl,rfl,hy⟩
    refine ⟨by ring,by ring,rfl,?_⟩
    rw [hy]
    unfold quadratic sextic
    ring

/-- On A=1 the equations give the reversed sextic, including a simple root at infinity. -/
theorem infinity_chart (c : Fin 7 → R) (z b d w : R) :
    equations c 1 z b d w ↔ b=z^2 ∧ d=z^3 ∧ w^2=sextic (fun i => c i.rev) z := by
  simp only [equations,one_mul]
  constructor
  · rintro ⟨hb,hd,_,hq⟩
    subst b
    have h : d=z^3 := by rw [hd]; ring
    refine ⟨rfl,h,?_⟩
    rw [h] at hq
    rw [hq]
    change quadratic c 1 z (z^2) (z^3) = c 6+c 5*z+c 4*z^2+c 3*z^3+c 2*z^4+c 1*z^5+c 0*z^6
    unfold quadratic
    ring
  · rintro ⟨rfl,rfl,hw⟩
    refine ⟨rfl,by ring,by ring,?_⟩
    rw [hw]
    change c 6+c 5*z+c 4*z^2+c 3*z^3+c 2*z^4+c 1*z^5+c 0*z^6 = quadratic c 1 z (z^2) (z^3)
    unfold quadratic
    ring

/-- Every field-valued projective point lies in at least one of these two charts. -/
theorem covers_field_points {K : Type*} [Field K] (c : Fin 7 → K) (b x y : K)
    (h : equations c 0 b x 0 y) : b=0 ∧ x=0 ∧ y=0 := by
  obtain ⟨hb,_,hx,hy⟩ := h
  have b0 : b=0 := by simpa using hb.symm
  have x0 : x=0 := by simpa using hx.symm
  refine ⟨b0,x0,?_⟩
  simpa [b0,x0,quadratic] using hy

/-- If xz=1 and w=z³y, the normalized coordinate tuples on the overlap differ by the unit z³. -/
theorem transition {x z y : R} (hxz : x*z=1) :
    z^3*x^3=1 ∧ z^3*x^2=z ∧ z^3*x=z^2 ∧ z^3*1=z^3 ∧ z^3*y=y*z^3 := by
  have h (i : ℕ) : x^i*z^i=1 := by rw [← mul_pow,hxz,one_pow]
  refine ⟨by rw [mul_comm,h],?_,?_,mul_one _,mul_comm _ _⟩
  · calc z^3*x^2 = z*(x^2*z^2) := by ring
         _ = z := by rw [h,mul_one]
  · calc z^3*x = z^2*(x*z) := by ring
         _ = z^2 := by rw [hxz,mul_one]

section AlgebraPoints
open Polynomial BinaryCover
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

noncomputable def equationPolynomial (c : Fin 7 → K) : K[X] := sextic (fun i => C (c i)) X

private theorem eval_equation (c : Fin 7 → K) (x : S) :
    aeval x (equationPolynomial c) = sextic (fun i => algebraMap K S (c i)) x := by
  simp [equationPolynomial,sextic]

/-- Points of the affine square-root chart over every commutative K-algebra. -/
noncomputable def coverPoints (c : Fin 7 → K) :
    (Cover (equationPolynomial c) →ₐ[K] S) ≃
      {p : S × S // p.2^2 = sextic (fun i => algebraMap K S (c i)) p.1} where
  toFun g := ⟨⟨g (algebraMap K[X] _ X),g QuadraticAlgebra.omega⟩,
    (ordinate_square g).trans (eval_equation c _)⟩
  invFun p := affinePoint (equationPolynomial c) p.1.1 p.1.2 (p.2.trans (eval_equation c _).symm)
  left_inv g := AlgHom.ext fun z => (affinePoint_image g z).symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change aeval p.1.1 (X : K[X]) + aeval p.1.1 (0:K[X])*p.1.2 = p.1.1
      simp
    · change aeval p.1.1 (0:K[X]) + aeval p.1.1 (1:K[X])*p.1.2 = p.1.2
      simp

/-- Every affine-chart algebra point gives exactly one normalized projective tuple on D=1. -/
def standardDPoints (c : Fin 7 → R) :
    {p : R × R // p.2^2 = sextic c p.1} ≃
    {v : R × R × R × R // equations c v.1 v.2.1 v.2.2.1 1 v.2.2.2} where
  toFun p := ⟨⟨p.1.1^3,p.1.1^2,p.1.1,p.1.2⟩,(finite_chart ..).mpr ⟨rfl,rfl,p.2⟩⟩
  invFun v := ⟨⟨v.1.2.2.1,v.1.2.2.2⟩,((finite_chart ..).mp v.2).2.2⟩
  left_inv _ := rfl
  right_inv v := by
    obtain ⟨⟨a,b,x,y⟩,hv⟩ := v
    obtain ⟨ha,hb,-⟩ := (finite_chart ..).mp hv
    apply Subtype.ext
    exact Prod.ext ha.symm (Prod.ext hb.symm rfl)

def standardAPoints (c : Fin 7 → R) :
    {p : R × R // p.2^2 = sextic (fun i => c i.rev) p.1} ≃
    {v : R × R × R × R // equations c 1 v.1 v.2.1 v.2.2.1 v.2.2.2} where
  toFun p := ⟨⟨p.1.1,p.1.1^2,p.1.1^3,p.1.2⟩,(infinity_chart ..).mpr ⟨rfl,rfl,p.2⟩⟩
  invFun v := ⟨⟨v.1.1,v.1.2.2.2⟩,((infinity_chart ..).mp v.2).2.2⟩
  left_inv _ := rfl
  right_inv v := by
    obtain ⟨⟨z,b,d,w⟩,hv⟩ := v
    obtain ⟨hb,hd,-⟩ := (infinity_chart ..).mp hv
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext hb.symm (Prod.ext hd.symm rfl))

theorem coefficient_equation (f : K[X]) (hd : f.natDegree ≤ 6) :
    equationPolynomial (fun i : Fin 7 => f.coeff i) = f := by
  have hs := f.as_sum_range_C_mul_X_pow' (n := 7) (by omega)
  simpa [equationPolynomial,sextic,Finset.sum_range_succ] using hs.symm

private theorem reversed_coefficients (f : K[X]) (hd : f.natDegree = 6) :
    (fun i : Fin 7 => f.reverse.coeff i) = fun i => f.coeff i.rev := by
  funext i
  have hi : (i:ℕ) ≤ 6 := by omega
  rw [coeff_reverse,hd,revAt_le hi,Fin.val_rev]
  congr 1
  omega

/-- The D=1 presentation represents the actual finite chart of any degree-six equation. -/
noncomputable def finiteChartAlgebraPoints (f : K[X]) (hd : f.natDegree = 6) :
    (Cover f →ₐ[K] S) ≃ {v : S × S × S × S //
      equations (fun i => algebraMap K S (f.coeff i)) v.1 v.2.1 v.2.2.1 1 v.2.2.2} := by
  let c : Fin 7 → K := fun i => f.coeff i
  let e := (coverPoints (S := S) c).trans (standardDPoints _)
  exact (Equiv.cast (congrArg (fun h : K[X] => Cover h →ₐ[K] S) (coefficient_equation f hd.le).symm)).trans e

/-- The A=1 presentation represents the actual reciprocal square-root chart. -/
noncomputable def infinityChartAlgebraPoints (f : K[X]) (hd : f.natDegree = 6) :
    (Cover f.reverse →ₐ[K] S) ≃ {v : S × S × S × S //
      equations (fun i => algebraMap K S (f.coeff i)) 1 v.1 v.2.1 v.2.2.1 v.2.2.2} := by
  let c : Fin 7 → K := fun i => f.coeff i
  let e := (coverPoints (S := S) (fun i => c i.rev)).trans (standardAPoints (fun i => algebraMap K S (c i)))
  have he : equationPolynomial (fun i => c i.rev) = f.reverse := by
    rw [← reversed_coefficients f hd]
    exact coefficient_equation _ (f.reverse_natDegree_le.trans hd.le)
  exact (Equiv.cast (congrArg (fun h : K[X] => Cover h →ₐ[K] S) he.symm)).trans e

end AlgebraPoints

end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.finite_chart
#print axioms ZInQBlueprint.SexticEmbedding.infinity_chart
#print axioms ZInQBlueprint.SexticEmbedding.covers_field_points
#print axioms ZInQBlueprint.SexticEmbedding.transition
#print axioms ZInQBlueprint.SexticEmbedding.coverPoints
#print axioms ZInQBlueprint.SexticEmbedding.standardDPoints
#print axioms ZInQBlueprint.SexticEmbedding.standardAPoints
#print axioms ZInQBlueprint.SexticEmbedding.coefficient_equation
#print axioms ZInQBlueprint.SexticEmbedding.finiteChartAlgebraPoints
#print axioms ZInQBlueprint.SexticEmbedding.infinityChartAlgebraPoints
