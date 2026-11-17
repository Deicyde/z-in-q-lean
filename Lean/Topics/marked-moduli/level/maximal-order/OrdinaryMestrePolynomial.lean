import MestrePolynomial
import OrdinaryEndomorphismAlgebra
import RationalQuaternionAction

/-! The ordinary moduli input on the algebraic Mestre route, with the integral
endomorphism ring recovered from the dimension of the rational algebra. -/
open CategoryTheory AlgebraicGeometry NumberField
open scoped ZInQBlueprint.NormalDescent

namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel
noncomputable section

/-- A real-labelled surface on the non-CM locus together with its rational
endomorphism algebra. The dimension bound suffices to recover the given
integral quaternion action as the entire endomorphism ring. -/
structure OrdinaryQMPoint where
  surface : GroupScheme Qbar
  abelian : IsAbelianScheme surface
  theta : surface.X.left.Modules
  principal : EffectivePrincipal abelian theta
  action : LevelThree.O →+* End surface
  finiteEnd : Module.Finite ℤ (End surface)
  rationalEnd : Type 1
  [ringD : Ring rationalEnd]
  [nontrivialD : Nontrivial rationalEnd]
  [algebraD : Algebra ℚ rationalEnd]
  [finiteD : FiniteDimensional ℚ rationalEnd]
  incl : End surface →+* rationalEnd
  faithful : Function.Injective incl
  dimension : Module.finrank ℚ rationalEnd ≤ 4

attribute [local instance] OrdinaryQMPoint.ringD OrdinaryQMPoint.nontrivialD
  OrdinaryQMPoint.algebraD OrdinaryQMPoint.finiteD OrdinaryQMPoint.finiteEnd

def OrdinaryQMPoint.asOrdinary (w : OrdinaryQMPoint) : OrdinarySurface :=
  ⟨w.surface, w.abelian, w.theta, w.principal,
   LevelThree.IntegralOrder.fullActionOfDimension w.action w.incl w.faithful
     (LevelThree.IntegralOrder.extendRationalAction (w.incl.comp w.action))
     (fun x => (LevelThree.IntegralOrder.extendRationalAction_embed (w.incl.comp w.action) x).symm)
     w.dimension⟩

def OrdinaryQMPoint.coarseClass (w : OrdinaryQMPoint) : ModuliClass :=
  moduliClass (markedObject w.surface w.theta w.action)

theorem OrdinaryQMPoint.asOrdinary_coarseClass (w : OrdinaryQMPoint) :
    w.asOrdinary.coarseClass = w.coarseClass := rfl

/-- The ordinary classes on the labelled quotient, described using the
marked integral action and the dimension of its rational endomorphism algebra. -/
def OrdinaryQMClasses {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ (t : Qbar) (j : ℚ), OutsideCM j → (j : Qbar) * (t^2 + 27) = -16 →
    C.read (linePoint t ≫ chart) ∈ Set.range OrdinaryQMPoint.coarseClass

theorem algebraicOrdinary_of_qm {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ordinary : OrdinaryQMClasses C chart) : AlgebraicOrdinaryClasses C chart := by
  intro t j nonCM quotient
  obtain ⟨w, hw⟩ := ordinary t j nonCM quotient
  exact ⟨w.asOrdinary, w.asOrdinary_coarseClass.trans hw⟩

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

/-- Glazer's original bounded polynomial through the algebraic Mestre equation.
On the ordinary locus it suffices to exhibit the marked action with a faithful
inclusion into a rational endomorphism algebra of dimension at most four. -/
theorem original_of_ordinary_mestre (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar)
    (ordinary : OrdinaryQMClasses C chart) (forget : AlgebraicForgetfulMap C chart E)
    (mestre : MestreEquation E) (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_mestre hF hp effective pqm st ddmm factor C chart E
    (algebraicOrdinary_of_qm C chart ordinary) forget mestre uniquePol primitive genus rank

end
end ZInQBlueprint.MinimalDiscriminant

#print axioms ZInQBlueprint.ShimuraAtlas.OrdinaryQMPoint.asOrdinary_coarseClass
#print axioms ZInQBlueprint.ShimuraAtlas.algebraicOrdinary_of_qm
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_ordinary_mestre
