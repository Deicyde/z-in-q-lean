import HPSexticDiscriminant
import HPCovolume
import HPIdenticalComplexFibres
import HPEmbeddingHeight

/-! The arithmetic covolume of the original rational signed model and its
connection to a single period in the all-embeddings formula. -/
open Polynomial MeasureTheory NumberField Real
namespace ZInQBlueprint.ArchimedeanHeight
open OddModel ThetaPeriod BinaryCover JacobianHeight NormalDescent ThetaClass
noncomputable section
abbrev rationalTerm (f : ℚ[X]) (V : ℝ) := (2:ℝ)^8 * ‖(f.discr:ℂ)‖ * V^5

/-- The ordinate and differential changes cancel on the full archimedean term. -/
theorem odd_covolume_invariant (f : ℚ[X]) (hd : f.natDegree=6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0) (s : ℂ)
    (hs : s^2=ordinateFactor (f.leadingCoeff : ℂ) r) (V : ℝ) :
    (2:ℝ)^8*‖(quintic r).discr‖*(‖s‖^4*V)^5 = rationalTerm f V := by
  have eq := congrArg (fun x : ℂ => ‖x‖) (sextic_discriminant f hd r hr hz s hs)
  simp only [norm_mul,norm_pow] at eq
  unfold rationalTerm
  rw [← eq]
  ring

/-- Homology columns may be compared in any fixed Haar measure on ℂ².
Only the period-integral realization of the columns is analytic. -/
theorem signed_covolume_invariant {u : ℚ} (hu : u ∉ ZInQ.contactSet) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (SexticThetaHeight.sextic u 1)=0)
    (s : ℂ) (hs : s^2=ordinateFactor ((paper ℚ u false).leadingCoeff : ℂ) r)
    (L L' : Submodule ℤ PeriodSpace)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L']
    (b : Module.Basis (Fin 4) ℤ L) (b' : Module.Basis (Fin 4) ℤ L')
    (b₀ : Module.Basis (Fin 4) ℝ PeriodSpace) (μ : Measure PeriodSpace) [μ.IsAddHaarMeasure]
    (transforms : ∀ i, (b' i : PeriodSpace)=realChange (r (Fin.last 5)) s (b i : PeriodSpace)) :
    (2:ℝ)^8*‖(quintic r).discr‖*(ZLattice.covolume L' μ)^5 =
      rationalTerm (paper ℚ u false) (ZLattice.covolume L μ) := by
  rw [covolume_change _ _ L L' b b' b₀ μ transforms]
  exact odd_covolume_invariant _ (paper_degree hu) r hr (roots_of_untwisted hu hz) s hs _

/-- If the arithmetic covolume is read on the rational sextic then one
Lockhart evaluation and the Arakelov norm formula produce exactly IgusaPeriod. -/
def igusa_of_rational_covolume {K : Type} [Field K] [NumberField K]
    {hF : AbelianModel.GroupScheme ℚ → ℝ} {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (localFormula : GoodLocalIgusa u I)
    (Z : SiegelPeriod) (red : InStrengDomain Z) (nz : rawChi Z ≠ 0) (V : ℝ)
    (lockhartValue : rationalTerm (paper ℚ u false) V = lockhart Z)
    (degree : (Module.finrank ℚ K:ℝ)*hF (SixJacobian.jacobian hu) =
      log (I.absNorm:ℝ)/60-(Module.finrank ℚ K:ℝ)*log (rationalTerm (paper ℚ u false) V)/10) :
    IgusaPeriod K hF hu := by
  refine ⟨Z,red,I,hI,localFormula,?_⟩
  rw [lockhartValue,metric_log nz] at degree
  linarith only [degree]

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.odd_covolume_invariant
#print axioms ZInQBlueprint.ArchimedeanHeight.signed_covolume_invariant
#print axioms ZInQBlueprint.ArchimedeanHeight.igusa_of_rational_covolume
