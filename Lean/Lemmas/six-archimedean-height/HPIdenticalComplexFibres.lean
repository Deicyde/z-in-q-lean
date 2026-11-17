import OddCompletion
import JacobianDiscriminant

/-! A single restricted complex model of the actual signed curve works at
every embedding of any number field over which the model has been extended. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ArchimedeanHeight
open BinaryCover NormalDescent AbelianModel OddModel ThetaPeriod
noncomputable section
variable {K : Type} [Field K] [NumberField K]

abbrev embeddingSpec (σ : K →ₐ[ℚ] ℂ) := Spec.map (CommRingCat.ofHom σ.toRingHom)

theorem embedding_over_rat (σ : K →ₐ[ℚ] ℂ) :
    embeddingSpec σ ≫ specExtension ℚ K = specExtension ℚ ℂ := by
  rw [embeddingSpec,specExtension,specExtension,← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

def complexComparison (σ : K →ₐ[ℚ] ℂ) :
    Over.pullback (specExtension ℚ ℂ) ≅
      Over.pullback (specExtension ℚ K) ⋙ Over.pullback (embeddingSpec σ) :=
  eqToIso (congrArg (fun f => Over.pullback f) (embedding_over_rat σ).symm) ≪≫
    Over.pullbackComp (embeddingSpec σ) (specExtension ℚ K)

def complexGroupComparison (A : GroupScheme ℚ) (σ : K →ₐ[ℚ] ℂ) :
    (Over.pullback (specExtension ℚ ℂ)).mapCommGrp.obj A ≅
      (Over.pullback (embeddingSpec σ)).mapCommGrp.obj
        ((Over.pullback (specExtension ℚ K)).mapCommGrp.obj A) :=
  (Functor.mapCommGrpNatIso (complexComparison σ)).app A ≪≫ Functor.mapCommGrpCompIso.app A

abbrev embeddedCurve (u : ℚ) (σ : K →ₐ[ℚ] ℂ) :=
  (Over.pullback (embeddingSpec σ)).obj (paperPullback K u)

def signedCurveComparison (u : ℚ) (σ : K →ₐ[ℚ] ℂ) :
    paperPullback ℂ u ≅ embeddedCurve u σ :=
  (complexComparison σ).app (paperModel ℚ u)

def signedJacobianComparison {u : ℚ} (hu : u ∉ ZInQ.contactSet) (σ : K →ₐ[ℚ] ℂ) :=
  complexGroupComparison (SixJacobian.jacobian hu) σ

/-- The monic separable quintic and the ordering are chosen before the
embedding. Only the map of that fixed proper curve to the conjugate fibre varies. -/
theorem one_restricted_curve {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ (r : Fin 6 → ℂ) (hr : Function.Injective r), (quintic r).Monic ∧
      (quintic r).natDegree = 5 ∧ (quintic r).Separable ∧ (∀ i, aeval (r i) (SexticThetaHeight.sextic u 1) = 0) ∧
      (∀ σ : K →ₐ[ℚ] ℂ, Nonempty (oddCurve hr ≅ embeddedCurve u σ)) := by
  obtain ⟨r,hr,hz⟩ := six_roots hu (one_ne_zero : (1:ℚ) ≠ 0)
  obtain ⟨s,e,hs,g,hg,_⟩ := paper_odd_completion hu hr hz
  exact ⟨r,hr,(quintic_monic_degree r).1,(quintic_monic_degree r).2,
    (by unfold quintic; exact separable_prod_X_sub_C_iff.mpr (finiteBranches_injective hr)),hz,
    fun σ => ⟨g ≪≫ signedCurveComparison u σ⟩⟩

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.embedding_over_rat
#print axioms ZInQBlueprint.ArchimedeanHeight.signedCurveComparison
#print axioms ZInQBlueprint.ArchimedeanHeight.signedJacobianComparison
#print axioms ZInQBlueprint.ArchimedeanHeight.one_restricted_curve
