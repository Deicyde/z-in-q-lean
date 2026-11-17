import InvariantDifferential

/-! The interface with the published formal group uses the invariant differential
dx/(2y), rather than an assertion about any ordinary ratio or its accuracy. -/
namespace Sun28.Ordinary
open Sun28.Scalar Sun28.ScalarTrace NumberField IsDedekindDomain Filter Topology
open PowerSeries
open scoped NumberField PowerSeries
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- VII.2.2, IV.5.2, IV.5.5 and IV.6.3–6.4 in the short coordinate.
U=x*z² is regular at the identity. The normalized differential F dz=dx/(2y)
and the chart equation are the two exact displayed series identities below. -/
def OrdinaryFormalChart (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := by
  classical
  let L:=w.adicCompletion K
  let v:=completionOrder w
  exact ∀ b : L, 65<p → v (p:L)=1 → 0≤v b → v (curve b).Δ=0 →
    ∃ T : EllipticKernelChart v b, ∃ A : T.F →+ L, ∃ U F : PowerSeries L,
      coeff 0 U=1 ∧ U^2-U+C b*X^4=0 ∧ 2*U*F=2*U-X*derivative U ∧
      ∀ Y : T.F, Tendsto (fun n => logTrunc (fun j => coeff (j-1) F) n (T.coordinate Y))
        atTop (𝓝 (A Y))

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
theorem ordinaryLogarithms_of_chart {p : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (classicalInput : OrdinaryFormalChart p w) : OrdinaryLogarithms p w := by
  classical
  let _ : CharZero (w.adicCompletion K) := charZero_of_injective_ringHom (algebraMap K (w.adicCompletion K)).injective
  intro b hp up bi good
  obtain ⟨T,A,U,F,init,model,inv,converges⟩ := classicalInput b hp up bi good
  have coefficients := short_chart_differential_coefficients b U F init model inv
  refine ⟨T,A,fun Y => ?_⟩
  have trunc (n:ℕ) : logTrunc (shortDifferential b) n (T.coordinate Y)=
      logTrunc (fun j => coeff (j-1) F) n (T.coordinate Y) := by
    unfold logTrunc
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.add_sub_cancel,coefficients]
  simpa only [trunc] using converges Y

/-- Sun's two ordinary ratios follow at once from the published local-field theorem.
All signs, zero numerators, and nonintegral un-cleared integer ratios are allowed. -/
theorem ordinary_pair64 {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (classicalInput : OrdinaryFormalChart p w) (σ : K ≃ₐ[ℚ] K)
    (m h c n : ℤ) (h0 : h≠0) (hc : h-c≠0)
    (fm : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (reciprocal (m • paperGenerator root)))
    (fh : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (reciprocal (h • paperGenerator root)))
    (fmc : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (σ (reciprocal ((m-c*n) • paperGenerator root))))
    (fhc : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (σ (reciprocal ((h-c) • paperGenerator root)))) :
    let u:=discreteOrder (w.valuation K)
    let L:=ordinaryRatio (paperGenerator root) m h
    let L' := σ (ordinaryRatio (paperGenerator root) (m-c*n) (h-c))
    (u L=u ((m:K)/h) ∧ (64:WithTop ℤ)≤u ((h:K)*L-m)) ∧
    (u L'=u (((m-c*n:ℤ):K)/((h-c:ℤ):K)) ∧ (64:WithTop ℤ)≤u (((h-c:ℤ):K)*L'-((m-c*n:ℤ):K))) := by
  have analytic := ordinaryLogarithms_of_chart w classicalInput
  exact ⟨ordinary_index_ratio64 large w root analytic 1 m h h0 fm fh,
    ordinary_index_ratio64 large w root analytic σ (m-c*n) (h-c) hc fmc fhc⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.ordinaryLogarithms_of_chart
#print axioms Sun28.Ordinary.ordinary_pair64
