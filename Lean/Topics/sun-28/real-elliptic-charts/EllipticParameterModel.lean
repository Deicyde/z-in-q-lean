import EmbeddedMultiples
import ProjectiveParameter

/-! The two projective charts on the actual conjugate curves and their diagonal orbit. -/
namespace Sun28.RealCharts
open ZInQ WeierstrassCurve WeierstrassCurve.Affine Sun28.Scalar Sun28.RealRatio
open scoped Sun28.RealCharts
noncomputable section

theorem parameter_agrees (σ : K0 →+* ℝ) (P : EmbeddedPoint σ) :
    parameterOn _ P=realParameter σ P := by
  cases P with
  | zero => exact (at_infinity _).1
  | some x y on => rfl

theorem embedded_chart_continuous (σ : K0 →+* ℝ) (m : ℤ) :
    ContinuousAt (parameterOn _) (embedded σ (paperMultiple m)) := by
  by_cases zm : m=0
  · subst m
    simpa only [paperMultiple,zero_zsmul,Point.zero_def,embedded] using (at_infinity ((curve _).map σ)).2
  · have live := zAt_ne zm σ
    have eq : parameter (paperMultiple m)=zAt m := rfl
    generalize h : paperMultiple m=Q at *
    cases Q with
    | zero =>
      rw [←eq] at live
      simp [parameter] at live
    | some x y on =>
      have yn : σ y≠0 := by
        intro e
        have zero := σ.injective (e.trans σ.map_zero.symm)
        rw [←eq] at live
        simp [parameter,zero] at live
      exact (at_affine _ _ _ _).2 yn

/-- Both factors carry the induced projective real topology. -/
abbrev RealPair := EmbeddedPoint (place false) × EmbeddedPoint (place true)

def diagonalGenerator : RealPair :=
  (embedded (place false) (paperGenerator sqrt2_sq),embedded (place true) (paperGenerator sqrt2_sq))

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Identification of the image of the generator suffices on the entire signed orbit. -/
def parameterModel_of_hom (a : Orbit G) (π : ∀ s : Bool,G →+ EmbeddedPoint (place s))
    (continuous : ∀ s,Continuous (π s)) (generator : ∀ s,π s a.generator=embedded (place s) (paperGenerator sqrt2_sq)) :
    ParameterModel a where
  z s := parameterOn _ ∘ π s
  value s m := by
    simp only [Function.comp_apply,map_zsmul,generator,←embedded_multiple,parameter_agrees,real_parameter_agrees]
    rfl
  zero_continuous s := by
    have h : ContinuousAt (parameterOn _) (π s 0) := (π s).map_zero.symm ▸ (at_infinity _).2
    exact ContinuousAt.comp (f:=π s) h (continuous s).continuousAt
  affine_continuous s m _ := by
    have h : ContinuousAt (parameterOn _) (π s (m • a.generator)) := by
      rw [map_zsmul,generator,←embedded_multiple]
      exact embedded_chart_continuous _ _
    exact ContinuousAt.comp (f:=π s) h (continuous s).continuousAt

/-- The subgroup topology and the two product projections supply the chart functions. -/
def parameterModel_on_subgroup (D : AddSubgroup RealPair) (a : Orbit D)
    (generator : (a.generator : RealPair)=diagonalGenerator) : ParameterModel a := by
  let π : ∀ s : Bool,D →+ EmbeddedPoint (place s) := fun s => match s with
    | false => (AddMonoidHom.fst _ _).comp D.subtype
    | true => (AddMonoidHom.snd _ _).comp D.subtype
  apply parameterModel_of_hom a π
  · intro s
    cases s
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val
  · intro s
    cases s
    · exact congrArg Prod.fst generator
    · exact congrArg Prod.snd generator

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.parameter_agrees
#print axioms Sun28.RealCharts.embedded_chart_continuous
#print axioms Sun28.RealCharts.parameterModel_of_hom
#print axioms Sun28.RealCharts.parameterModel_on_subgroup
