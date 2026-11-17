import EmbeddedExceptions

/-! The real values of the literal degree-64 polynomial on a signed orbit. -/
namespace Sun28.RealWindows
open Filter Set NumberField ZInQ Sun28.RealRatio Sun28.Scalar Sun28.Ordinary Sun28.Forward
open Sun28.FixedPreparation Sun28.WitnessIndices
open scoped Topology
noncomputable section

private def embeddingIndex (σ : K0 →+* ℝ) : Bool := by
  classical
  exact if σ=K0.embPlus then false else true

private theorem embeddingIndex_spec (σ : K0 →+* ℝ) : place (embeddingIndex σ)=σ := by
  classical
  unfold embeddingIndex
  split_ifs with h
  · rw [h]; rfl
  · obtain d|d:=embedding_cases σ
    · contradiction
    · rw [d];rfl

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] {a : Orbit G}

def parameterAt (model : ParameterModel a) (σ : K0 →+* ℝ) : G→ℝ :=
  model.z (embeddingIndex σ)

theorem parameterAt_multiple (model : ParameterModel a) (σ : K0 →+* ℝ) (m : ℤ) :
    parameterAt model σ (m • a.generator)=σ (zAt m) := by
  rw [parameterAt,model.value,embeddingIndex_spec]

theorem parameterAt_continuousAt (model : ParameterModel a) (σ : K0 →+* ℝ) (m : ℤ) :
    ContinuousAt (parameterAt model σ) (m • a.generator) := by
  by_cases h : m=0
  · subst m
    simpa [parameterAt] using model.zero_continuous (embeddingIndex σ)
  · exact model.affine_continuous (embeddingIndex σ) m h

def realTrunc (model : ParameterModel a) (σ : K0 →+* ℝ) (x : G) : ℝ :=
  logTrunc (shortDifferential (σ (-(3-sqrt2)^2))) 64 (parameterAt model σ x)

theorem realTrunc_multiple (model : ParameterModel a) (σ : K0 →+* ℝ) (m : ℤ) :
    realTrunc model σ (m • a.generator)=σ (truncAt (m • P)) := by
  rw [realTrunc,parameterAt_multiple,truncAt,scalar_index,map_shortTrunc]
  rfl

theorem realTrunc_continuousAt (model : ParameterModel a) (σ : K0 →+* ℝ) (m : ℤ) :
    ContinuousAt (realTrunc model σ) (m • a.generator) := by
  unfold realTrunc logTrunc
  have p := parameterAt_continuousAt model σ m
  fun_prop (disch := assumption)

theorem realTrunc_multiple_ne (model : ParameterModel a) (σ : K0 →+* ℝ)
    {m : ℤ} (nz : m≠0) : realTrunc model σ (m • a.generator)≠0 := by
  rw [realTrunc_multiple]
  exact (map_ne_zero σ).2 (truncAt_multiple_nonzero m nz)

theorem relativeAt_multiple (model : ParameterModel a) (σ : K0 →+* ℝ) (n m : ℤ) :
    realTrunc model σ (n • (m • a.generator)) / realTrunc model σ (m • a.generator) =
      σ (ordinaryRatio (paperGenerator sqrt2_sq) (n*m) m) := by
  rw [←mul_smul,realTrunc_multiple,realTrunc_multiple,multiple_ratio,pointRatio,map_div₀]

variable [IsTopologicalAddGroup G]

theorem relativeAt_continuousAt (model : ParameterModel a) (σ : K0 →+* ℝ) (n m : ℤ) (nz : m≠0) :
    ContinuousAt (fun x => realTrunc model σ (n • x)/realTrunc model σ x) (m • a.generator) := by
  apply ContinuousAt.div _ (realTrunc_continuousAt model σ m) (realTrunc_multiple_ne model σ nz)
  apply ContinuousAt.comp (g:=realTrunc model σ)
  · rw [←mul_smul]
    exact realTrunc_continuousAt model σ (n*m)
  · exact (continuous_zsmul n).continuousAt

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.parameterAt_multiple
#print axioms Sun28.RealWindows.parameterAt_continuousAt
#print axioms Sun28.RealWindows.realTrunc_multiple
#print axioms Sun28.RealWindows.realTrunc_continuousAt
#print axioms Sun28.RealWindows.realTrunc_multiple_ne
#print axioms Sun28.RealWindows.relativeAt_multiple
#print axioms Sun28.RealWindows.relativeAt_continuousAt
