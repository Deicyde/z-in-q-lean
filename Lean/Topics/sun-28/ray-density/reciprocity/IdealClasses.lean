import IntegralRay
import Mathlib.GroupTheory.Congruence.Basic

namespace Sun28.Reciprocity
open Ideal Submodule.IsPrincipal
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (M : Ideal R) [Nontrivial (R ⧸ M)]

/-- Integral ideals prime to the finite modulus. -/
def coprimeIdeals : Submonoid (Ideal R) where
  carrier := {J | J ⊔ M = ⊤}
  one_mem' := by simp
  mul_mem' h k := ((Ideal.isCoprime_iff_sup_eq.mpr h).mul_left
    (Ideal.isCoprime_iff_sup_eq.mpr k)).sup_eq

def idealClass (J : coprimeIdeals M) : unitClasses M :=
  classOf M (generator J.val) ((invertible_iff M _).2 (by
    change Ideal.span {generator J.val} ⊔ M = ⊤
    rw [Ideal.span_singleton_generator]
    exact J.2))

theorem ideal_ray_iff (J K : coprimeIdeals M) :
    idealEquivalent M J.val K.val ↔ idealClass M J = idealClass M K := by
  unfold idealClass
  rw [← principal_ray_iff]
  simp [principal]

theorem idealClass_spec (J : coprimeIdeals M) (x : R) (hx : IsUnit (residue M x))
    (hJ : principal x = J.val) : idealClass M J = classOf M x hx := by
  unfold idealClass
  apply (principal_ray_iff M _ _ _ _).1
  refine ⟨1,1,one_ne_zero,one_ne_zero,map_one _,map_one _,?_⟩
  simp [hJ,principal,Ideal.span_singleton_generator]

omit [IsDomain R] [IsPrincipalIdealRing R] [Nontrivial (R ⧸ M)] in
theorem class_product (x y : R) (hx : IsUnit (residue M x)) (hy : IsUnit (residue M y)) :
    classOf M (x*y) (map_mul (residue M) x y ▸ hx.mul hy) = classOf M x hx * classOf M y hy := by
  unfold classOf
  exact (congrArg (QuotientGroup.mk' _) (Units.ext (v := hx.unit * hy.unit) (by simp [IsUnit.unit_spec]))).trans (map_mul _ _ _)

def idealClassHom : coprimeIdeals M →* unitClasses M where
  toFun := idealClass M
  map_one' := by
    rw [idealClass_spec M 1 1 (by simp) (by simp [principal])]
    unfold classOf
    exact (congrArg (QuotientGroup.mk' _) (Units.ext (v := 1) (by simp))).trans (map_one _)
  map_mul' J K := by
    let x := generator J.val
    let y := generator K.val
    have hx : IsUnit (residue M x) := (invertible_iff M _).2 (by unfold principal x; rw [Ideal.span_singleton_generator]; exact J.2)
    have hy : IsUnit (residue M y) := (invertible_iff M _).2 (by unfold principal y; rw [Ideal.span_singleton_generator]; exact K.2)
    have hxy : IsUnit (residue M (x*y)) := map_mul (residue M) x y ▸ hx.mul hy
    rw [idealClass_spec M (J*K) (x*y) hxy (by
      change Ideal.span {x*y}=J.val*K.val
      rw [← Ideal.span_singleton_mul_span_singleton]
      simp [x,y])]
    exact class_product M x y hx hy

theorem idealClass_surjective : Function.Surjective (idealClassHom M) := by
  intro a
  obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective (unitReduction M).range a
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (v : R ⧸ M)
  have hxu : IsUnit (residue M x) := ⟨v,hx.symm⟩
  let J : coprimeIdeals M := ⟨principal x,(invertible_iff M _).1 hxu⟩
  refine ⟨J,?_⟩
  change idealClass M J = a
  rw [idealClass_spec M J x hxu rfl,← hv]
  exact congrArg (QuotientGroup.mk' _) (Units.ext (hxu.unit_spec.trans hx))

/-- Milne V.1.6's integral ray-equivalence relation is the group congruence of this map. -/
theorem rayCongruence (J K : coprimeIdeals M) :
    (Con.ker (idealClassHom M)).r J K ↔ idealEquivalent M J.val K.val :=
  (ideal_ray_iff M J K).symm

/-- The integral ideal quotient, with actual multiplication of ideals, calculated in a PID. -/
noncomputable def rayEquiv :
    (Con.ker (idealClassHom M)).Quotient ≃* unitClasses M :=
  Con.quotientKerEquivOfSurjective _ (idealClass_surjective M)

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.ideal_ray_iff
#print axioms Sun28.Reciprocity.idealClass_surjective
#print axioms Sun28.Reciprocity.rayCongruence
#print axioms Sun28.Reciprocity.rayEquiv
