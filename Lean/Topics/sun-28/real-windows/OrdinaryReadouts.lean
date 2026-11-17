import RealTruncation

/-! On the simultaneous witness indices m_i=h n_i the nontrivial ordinary real
expressions are continuous at every sufficiently large signed orbit point.
The other ten are globally bounded on all signed multiples. -/
namespace Sun28.RealWindows
open Filter Set NumberField ZInQ ZInQ.Mult Sun28.RealRatio Sun28.Scalar Sun28.Ordinary Sun28.Forward
open Sun28.FixedPreparation Sun28.WitnessIndices
open scoped Topology
noncomputable section
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {a : Orbit G}

def ratioOn (model : ParameterModel a) (σ : K0 →+* ℝ) (n : ℤ) (x : G) : ℝ :=
  realTrunc model σ (n • x)/realTrunc model σ x

def starPlace (σ : K0 →+* ℝ) : K0 →+* ℝ := σ.comp conjugation.toRingHom

def shiftedOn (model : ParameterModel a) (σ : K0 →+* ℝ) (n anchor : ℤ) (x : G) : ℝ :=
  ratioOn model (starPlace σ) n (x-anchor • a.generator)

omit [IsTopologicalAddGroup G] in
theorem shiftedOn_multiple (model : ParameterModel a) (σ : K0 →+* ℝ) (n anchor m : ℤ) :
    shiftedOn model σ n anchor (m • a.generator)=
     σ (conjugation (ordinaryRatio (paperGenerator sqrt2_sq) (m*n-anchor*n) (m-anchor))) := by
  unfold shiftedOn ratioOn
  rw [sub_eq_add_neg,←sub_zsmul,relativeAt_multiple]
  rw [show n*(m-anchor)=m*n-anchor*n by ring]
  rfl

theorem shiftedOn_continuousAt (model : ParameterModel a) (σ : K0 →+* ℝ) (n anchor m : ℤ)
    (nz : m-anchor≠0) : ContinuousAt (shiftedOn model σ n anchor) (m • a.generator) := by
  change ContinuousAt ((ratioOn model (starPlace σ) n) ∘ (fun x : G => x-anchor • a.generator)) _
  apply ContinuousAt.comp
  · rw [sub_eq_add_neg,←sub_zsmul]
    exact relativeAt_continuousAt model (starPlace σ) n _ nz
  · exact (continuous_id.sub continuous_const).continuousAt

/-- Only the six tests involving logarithms need local real continuity.
Every discarded entry is estimated separately by inverse_abscissa. -/
def varyingReadout (model : ParameterModel a) (σ : K0 →+* ℝ) (anchor : ℤ)
    (n : Fin 4→ℤ) (β : ℚ) (t : OrdinaryTest) (x : G) : ℝ :=
  let R := fun i => ratioOn model σ (n i) x
  match t with
  | .difference i => R i - shiftedOn model σ (n i) anchor x
  | .delta => lucas (R 1) (R 2) (R 3)
  | .beta => R 0-(β:ℝ)
  | _ => 0

theorem varyingReadout_continuousAt (model : ParameterModel a) (σ : K0 →+* ℝ) (anchor : ℤ)
    (n : Fin 4→ℤ) (β : ℚ) (t : OrdinaryTest) (m : ℤ) (late : max anchor 0 < m) :
    ContinuousAt (varyingReadout model σ anchor n β t) (m • a.generator) := by
  have mn : m≠0 := by omega
  have ma : m-anchor≠0 := by omega
  have r (i : Fin 4) : ContinuousAt (ratioOn model σ (n i)) (m • a.generator) :=
    relativeAt_continuousAt model σ _ _ mn
  cases t with
  | h | u | v₀ | v => exact continuousAt_const
  | difference i => exact (r i).sub (shiftedOn_continuousAt model σ _ _ _ ma)
  | beta => exact (r 0).sub continuousAt_const
  | delta =>
    unfold varyingReadout lucas
    fun_prop (disch := assumption)

/-- The same global reciprocal bound holds after either embedding and after conjugation. -/
theorem reciprocal_bound (σ : K0 →+* ℝ) (m : ℤ) :
    |σ (reciprocal (m • paperGenerator sqrt2_sq))|≤1 := by
  obtain rfl|rfl:=embedding_cases σ
  · exact inverse_abscissa _ _ embPlus_delta_mem.1
  · exact inverse_abscissa _ _ embMinus_delta_mem.1

omit [IsTopologicalAddGroup G] in
/-- Convert the six varying functions and the ten unconditional bounds into
the original, field-valued, sixteen ordinary tests at one signed index. -/
theorem ordinary_from_readouts (model : ParameterModel a) (σ : K0 →+* ℝ) (anchor h : ℤ)
    (n : Fin 4→ℤ) (β : ℚ) {B : ℝ} (one : 1≤B)
    (readout : ∀ i, |varyingReadout model σ anchor n β i (h • a.generator)| < B) :
    ∀ i, |σ (ordinaryTests sqrt2_sq conjugation anchor h n (fun j=>h*n j) β i)| ≤ B := by
  have r (i : Fin 4) : ratioOn model σ (n i) (h • a.generator)=
      σ (ordinaryRatio (paperGenerator sqrt2_sq) (h*n i) h) := by
    simpa [ratioOn,mul_comm (n i) h] using relativeAt_multiple model σ (n i) h
  have s (i : Fin 4) := shiftedOn_multiple model σ (n i) anchor h
  intro i
  cases i with
  | h => exact (reciprocal_bound σ h).trans one
  | u i => exact (reciprocal_bound σ _).trans one
  | v₀ => exact (reciprocal_bound (starPlace σ) _).trans one
  | v i => exact (reciprocal_bound (starPlace σ) _).trans one
  | difference i =>
    simpa only [varyingReadout,ordinaryTests,map_sub,r,s] using (readout (.difference i)).le
  | beta =>
    simpa [varyingReadout,ordinaryTests,map_sub,r] using (readout .beta).le
  | delta =>
    simpa only [varyingReadout,ordinaryTests,lucas,map_sub,map_add,map_mul,map_pow,map_one,map_ofNat,r]
      using (readout .delta).le

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.shiftedOn_multiple
#print axioms Sun28.RealWindows.shiftedOn_continuousAt
#print axioms Sun28.RealWindows.varyingReadout_continuousAt
#print axioms Sun28.RealWindows.reciprocal_bound
#print axioms Sun28.RealWindows.ordinary_from_readouts
