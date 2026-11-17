import IntegralQuaternionOrder
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! A finite integral endomorphism ring in the ordinary rational quaternion
algebra cannot strictly contain the printed order. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
open QuaternionAlgebra
noncomputable section

private theorem integer_of_integral {r : ℚ} (h : IsIntegral ℤ r) : isInteger r := by
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  exact ⟨a,ha.symm⟩

private theorem quadratic_relation (q : B) :
    q*q = (-reducedNorm q) • (1:B) + trd q • q := by
  rcases q with ⟨r,s,t,v⟩
  ext <;> simp [reducedNorm,trd] <;> ring

private abbrev quadraticModel (q : B) := QuadraticAlgebra ℚ (-reducedNorm q) (trd q)
private def evaluateAt (q : B) : quadraticModel q →ₐ[ℚ] B :=
  QuadraticAlgebra.lift ⟨q,quadratic_relation q⟩

private theorem evaluate_injective {q : B} (noncentral : ¬(q.imI=0 ∧ q.imJ=0 ∧ q.imK=0)) :
    Function.Injective (evaluateAt q) := by
  intro z w eq
  change z.re • (1:B) + z.im • q = w.re • 1 + w.im • q at eq
  have hi : z.im*q.imI = w.im*q.imI := by simpa using congrArg QuaternionAlgebra.imI eq
  have hj : z.im*q.imJ = w.im*q.imJ := by simpa using congrArg QuaternionAlgebra.imJ eq
  have hk : z.im*q.imK = w.im*q.imK := by simpa using congrArg QuaternionAlgebra.imK eq
  have im : z.im = w.im := by
    by_cases i : q.imI=0
    · by_cases j : q.imJ=0
      · exact mul_right_cancel₀ (fun k => noncentral ⟨i,j,k⟩) hk
      · exact mul_right_cancel₀ j hj
    · exact mul_right_cancel₀ i hi
  exact QuadraticAlgebra.ext (by simpa [im] using congrArg QuaternionAlgebra.re eq) im

/-- The reduced trace and norm of an integral rational quaternion are
integers. For a nonscalar quaternion its generated commutative quadratic
algebra embeds faithfully, so both conjugate roots are integral. -/
theorem integral_invariants {q : B} (hq : IsIntegral ℤ q) :
    isInteger (trd q) ∧ isInteger (reducedNorm q) := by
  by_cases scalar : q.imI=0 ∧ q.imJ=0 ∧ q.imK=0
  · have eq : algebraMap ℚ B q.re = q := by
      rw [QuaternionAlgebra.algebraMap_eq]
      exact QuaternionAlgebra.ext rfl scalar.1.symm scalar.2.1.symm scalar.2.2.symm
    have h : IsIntegral ℤ q.re :=
      (isIntegral_algHom_iff (algebraMap ℚ B).toIntAlgHom (algebraMap ℚ B).injective).mp
        (show IsIntegral ℤ (algebraMap ℚ B q.re) from eq.symm ▸ hq)
    obtain ⟨n,hn⟩ := integer_of_integral h
    constructor
    · exact ⟨2*n,by simp [trd,hn]⟩
    · exact ⟨n^2,by simp [reducedNorm,scalar.1,scalar.2.1,scalar.2.2,hn]; ring⟩
  · let w : quadraticModel q := QuadraticAlgebra.omega
    have eval : evaluateAt q w = q := by change (0:ℚ) • (1:B) + (1:ℚ) • q = q; simp
    have hw : IsIntegral ℤ w :=
      (isIntegral_algHom_iff (evaluateAt q).toRingHom.toIntAlgHom (evaluate_injective scalar)).mp
        (show IsIntegral ℤ (evaluateAt q w) from eval.symm ▸ hq)
    have hc : IsIntegral ℤ (star w) := hw.map (starRingEnd (quadraticModel q)).toIntAlgHom
    have ht : algebraMap ℚ (quadraticModel q) (trd q) = w + star w := by
      ext <;> simp [w,QuadraticAlgebra.omega,quadraticModel]
    have hn : algebraMap ℚ (quadraticModel q) (reducedNorm q) = w * star w := by
      ext <;> simp [w,QuadraticAlgebra.omega,quadraticModel]
    constructor
    · apply integer_of_integral
      exact (isIntegral_algHom_iff (algebraMap ℚ (quadraticModel q)).toIntAlgHom
        (algebraMap ℚ (quadraticModel q)).injective).mp (ht.symm ▸ hw.add hc)
    · apply integer_of_integral
      exact (isIntegral_algHom_iff (algebraMap ℚ (quadraticModel q)).toIntAlgHom
        (algebraMap ℚ (quadraticModel q)).injective).mp (hn.symm ▸ hw.mul hc)

/-- A faithful realization of a finite ℤ-algebra in the rational quaternion
algebra extending the fixed action identifies the actual integral rings. -/
def fullAction {E : Type*} [Ring E] [Module.Finite ℤ E]
    (action : O →+* E) (realize : E →+* B) (faithful : Function.Injective realize)
    (compatible : ∀ x, realize (action x) = embed x) : O ≃+* E := by
  have h (x : E) : IsIntegral ℤ (realize x) :=
    (IsIntegral.of_finite ℤ x).map realize.toIntAlgHom
  exact actionEquiv action realize faithful compatible
    (fun x => (integral_invariants (h x)).1) (fun x => (integral_invariants (h x)).2)

theorem fullAction_apply {E : Type*} [Ring E] [Module.Finite ℤ E]
    (action : O →+* E) (realize : E →+* B) (faithful : Function.Injective realize)
    (compatible : ∀ x, realize (action x) = embed x) (x : O) :
    fullAction action realize faithful compatible x = action x := rfl

/-- There is no strictly larger order in B containing the displayed one. -/
theorem no_finite_overorder (S : Subring B) [Module.Finite ℤ S]
    (contains : ∀ x : O, embed x ∈ S) : S = embedHom.range := by
  let a : O →+* S := embedHom.codRestrict S contains
  let equiv := fullAction a S.subtype Subtype.val_injective (fun _ => rfl)
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := equiv.surjective (⟨x,hx⟩ : S)
    exact ⟨v,congrArg Subtype.val hv⟩
  · rintro ⟨v,rfl⟩
    exact contains v

end
end ZInQBlueprint.LevelThree.IntegralOrder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.integral_invariants
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.no_finite_overorder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullAction
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullAction_apply
