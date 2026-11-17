import PlanarShell

namespace Sun28.ConeReal
open MeasureTheory Set Real Sun28.QuadricSieve Filter Topology
open scoped ENNReal
noncomputable section

def tube (κ ε : ℝ) : Set (Coordinates ℝ) := {x | |form κ x|≤ε}
theorem tube_measurable (κ ε : ℝ) : MeasurableSet (tube κ ε) := by
  change MeasurableSet ((fun x => |form κ x|) ⁻¹' Iic ε)
  apply measurableSet_Iic.preimage
  unfold form rad;fun_prop

def tubeMass (κ ε : ℝ) (ψ : Coordinates ℝ → ℝ) : ℝ :=
  (∫⁻ x in tube κ ε, ENNReal.ofReal (ψ x)).toReal / (2*ε)

def rowConstant : ℝ := 8*π^2

theorem tube_integral (κ : ℝ) (j : ℕ) {ε:ℝ} (he:0<ε) :
    (∫⁻ x in tube κ ε, ENNReal.ofReal (weight j x)) ≤
      ENNReal.ofReal (rowConstant*width j*(2*ε)) := by
  let K₁ : Set (ℝ×ℝ) := {z|rad z≤2}
  let K₂ := Icc (-2*width j) (2*width j)
  let K := K₁ ×ˢ K₂
  let D := tube κ ε ∩ (Prod.snd ⁻¹' K)
  have m₁ : MeasurableSet K₁ := by
    change MeasurableSet (rad ⁻¹' Iic 2)
    apply measurableSet_Iic.preimage;unfold rad;fun_prop
  have mK : MeasurableSet K := m₁.prod measurableSet_Icc
  have mD : MeasurableSet D := (tube_measurable κ ε).inter (mK.preimage measurable_snd)
  have vK : volume K = ENNReal.ofReal ((π*2)*(4*width j)) := by
    change volume (K₁ ×ˢ K₂) = _
    rw [Measure.volume_eq_prod,Measure.prod_prod]
    dsimp only [K₁,K₂]
    rw [area_closed,Real.volume_Icc,←ENNReal.ofReal_mul (by positivity)]
    congr 1;ring
  let c := ENNReal.ofReal (π*(2*ε))
  have slice (y : (ℝ×ℝ)×ℝ) :
      volume ((fun z : ℝ×ℝ => (z,y)) ⁻¹' D) ≤ K.indicator (fun _ => c) y := by
    by_cases hy:y∈K
    · rw [indicator_of_mem hy]
      calc _ ≤ volume {z : ℝ×ℝ | |rad z-(rad y.1+κ*y.2^2)|≤ε} := by
             apply measure_mono
             intro z hz
             have b:=hz.1
             change |rad z-rad y.1-κ*y.2^2|≤ε at b
             change |rad z-(rad y.1+κ*y.2^2)|≤ε
             rwa [sub_add_eq_sub_sub]
           _ ≤ _ := shell_area _ he.le
    · rw [indicator_of_notMem hy]
      have e : (fun z : ℝ×ℝ => (z,y)) ⁻¹' D=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz;exact hy hz.2
      simp [e]
  rw [←lintegral_indicator (tube_measurable κ ε)]
  calc
    _ ≤ ∫⁻ x, D.indicator (fun _ => (1:ℝ≥0∞)) x := by
      apply lintegral_mono;intro x
      by_cases ht:x∈tube κ ε
      · rw [indicator_of_mem ht]
        by_cases hs : weight j x=0
        · simp [hs]
        · obtain ⟨_,b,v⟩:=support_bounds j (subset_closure (show x∈Function.support (weight j) from hs))
          have inside : x∈D := ⟨ht,show rad x.2.1≤2 ∧ x.2.2∈K₂ from
            ⟨by linarith [b.2],by simpa [K₂,neg_mul] using abs_le.mp v⟩⟩
          rw [indicator_of_mem inside]
          simpa using ENNReal.ofReal_le_ofReal (weight_bounds j x).2
      · simp [indicator_of_notMem ht]
    _ = volume D := by rw [lintegral_indicator mD];simp
    _ = ∫⁻ y, volume ((fun z : ℝ×ℝ => (z,y)) ⁻¹' D) := Measure.prod_apply_symm mD
    _ ≤ ∫⁻ y, K.indicator (fun _ => c) y := lintegral_mono slice
    _ = c * volume K := by rw [lintegral_indicator mK];simp
    _ = _ := by
      rw [vK];dsimp [c,rowConstant]
      rw [←ENNReal.ofReal_mul (by positivity)]
      congr 1;ring

theorem tube_bound (κ : ℝ) (j : ℕ) {ε:ℝ} (he:0<ε) :
    tubeMass κ ε (weight j) ≤ rowConstant*width j := by
  rw [tubeMass,div_le_iff₀ (by positivity : 0<2*ε)]
  apply ENNReal.toReal_le_of_le_ofReal _ (tube_integral κ j he)
  dsimp [rowConstant];positivity [width_pos j]

/-- The ordinary Lebesgue integral in Heath-Brown (1.3). -/
theorem tubeMass_eq_real (κ ε : ℝ) (j : ℕ) :
    tubeMass κ ε (weight j) = (∫ x in tube κ ε, weight j x) / (2*ε) := by
  unfold tubeMass
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => (weight_bounds j x).1))
    (smooth_weight j).continuous.aestronglyMeasurable]

theorem density_le (κ : ℝ) (j : ℕ) {σ : ℝ}
    (h : Tendsto (fun ε => tubeMass κ ε (weight j)) (𝓝[>] 0) (𝓝 σ)) :
    σ ≤ rowConstant*width j :=
  le_of_tendsto h (mem_of_superset self_mem_nhdsWithin fun _ he=>tube_bound κ j he)

end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.tube_integral
#print axioms Sun28.ConeReal.tube_bound
#print axioms Sun28.ConeReal.tubeMass_eq_real
#print axioms Sun28.ConeReal.density_le
