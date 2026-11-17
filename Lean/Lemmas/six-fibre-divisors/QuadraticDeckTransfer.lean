import SignedSexticFibreField
/-! Transport the quadratic map to the literal function field, retaining its embedded constants. -/
namespace ZInQBlueprint.FibreDivisors
open AlgebraicCurve BinaryCover
noncomputable section
variable {K E : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field E] [Algebra K E]
variable (f : RatFunc K) [Fact (¬ IsSquare f)]

theorem principal_of_coordinate_equiv
    (e : E ≃ₐ[K] Cover f) (s : E ≃ₐ[K] E)
    (action : ∀ x, e (s x) = ordinateConjugation f (e x))
    (P Q : Place K E) :
    ((pointDivisor P + pointDivisor (SemilinearAut.ofAlgAut s • P)) -
     (pointDivisor Q + pointDivisor (SemilinearAut.ofAlgAut s • Q))).IsPrincipal := by
  let φ := e.symm.toRingEquiv.toRingHom.comp (algebraMap (RatFunc K) (Cover f))
  let : Algebra (RatFunc K) E := φ.toAlgebra
  have ec (x : RatFunc K) :
      e (algebraMap (RatFunc K) E x) = algebraMap (RatFunc K) (Cover f) x :=
    e.apply_symm_apply _
  let : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun c => by
    apply e.injective
    rw [e.commutes,ec,IsScalarTower.algebraMap_apply K (RatFunc K) (Cover f)])
  let q : E ≃ₐ[RatFunc K] Cover f := { e.toRingEquiv with commutes' := ec }
  let : FiniteDimensional (RatFunc K) E := Module.Finite.equiv q.symm.toLinearEquiv
  have d : Module.finrank (RatFunc K) E = 2 :=
    q.toLinearEquiv.finrank_eq.trans (QuadraticAlgebra.finrank_eq_two _ _)
  let : Algebra.IsQuadraticExtension (RatFunc K) E := ⟨d⟩
  let lift : E ≃ₐ[RatFunc K] E :=
    { s.toRingEquiv with
      commutes' := fun x => by
        apply e.injective
        change e (s _) = e _
        rw [action,ec,(ordinateConjugation f).commutes] }
  have hl : lift ≠ 1 := by
    intro h
    apply ordinateConjugation_ne_one f
    apply AlgEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    have hh : s x = x := AlgEquiv.congr_fun h x
    rw [←action,hh]
    rfl
  have hd : deck lift = SemilinearAut.ofAlgAut s := by
    unfold deck
    congr 1
  have result := orbit_difference_principal d lift hl P Q
  simpa only [orbitDivisor,hd] using result
end
end ZInQBlueprint.FibreDivisors
#print axioms ZInQBlueprint.FibreDivisors.principal_of_coordinate_equiv

