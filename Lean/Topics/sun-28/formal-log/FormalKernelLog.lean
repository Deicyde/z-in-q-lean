import MinimalModelLog

/-! The two classical local theorems live on the same formal group. Keep
the coordinate chart and the logarithm on that group explicit. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField

universe u
variable {L : Type u} [Field L] [DecidableEq L]

/-- The local parameter chart for the reduction kernel. Its source is an
actual subgroup of the elliptic curve and its target has the formal group law.
Silverman VII.2.2 identifies its coordinate with -x/y. -/
structure EllipticKernelChart (v : AddValuation L (WithTop ℤ)) (b : L) where
  kernel : AddSubgroup (curve b).Point
  membership {Q : (curve b).Point} : 0<v (reciprocal Q) → parameter Q≠0 → Q∈kernel
  F : Type u
  [addGroup : AddCommGroup F]
  coordinate : F → L
  integral (X : F) : (1:WithTop ℤ)≤v (coordinate X)
  chart : kernel ≃+ F
  chart_parameter (Q : kernel) : coordinate (chart Q)=parameter Q.1

attribute [instance] EllipticKernelChart.addGroup

/-- The same formal logarithm is an additive homomorphism and induces a
bijection on the underlying sets of all positive layers. This is IV.6.4(a,b)
when p>2 and v(p)=1. -/
structure LogarithmOnLayers (v : AddValuation L (WithTop ℤ)) {b : L} (T : EllipticKernelChart v b) where
  log : T.F →+ L
  bijOn (r : ℕ) (positive : 0<r) : Set.BijOn log
    {X | ((r:ℤ):WithTop ℤ)≤v (T.coordinate X)} {y | ((r:ℤ):WithTop ℤ)≤v y}

/-- Surjectivity on layer r and injectivity on layer one give the inverse-image
identity on layer r without any additional isometry assumption. -/
noncomputable def filteredLogarithm_of_formal_chart (v : AddValuation L (WithTop ℤ))
    {b : L} (T : EllipticKernelChart v b) (A : LogarithmOnLayers v T) : FilteredLogarithm v v b where
  kernel := T.kernel
  formal := T.membership
  log := A.log.comp T.chart.toAddMonoidHom
  level Q r hr := by
    change _ ≤ v (A.log (T.chart Q)) ↔ _ ≤ v (parameter Q.1)
    rw [←T.chart_parameter]
    constructor
    · intro h
      obtain ⟨X,hX,e⟩ := (A.bijOn r hr).surjOn h
      have eq : X=T.chart Q := (A.bijOn 1 (by decide)).injOn
        (by simpa using T.integral X) (by simpa using T.integral (T.chart Q)) e
      exact eq ▸ hX
    · intro h
      exact (A.bijOn r hr).mapsTo h

variable {K : Type u} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- The two published statements specialized to the same minimal equation and
completion. No global points or indices enter the statement. -/
def MinimalFormalGroupTheorems (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := by
  classical
  let L' := w.adicCompletion K
  let v := completionOrder w
  exact ∀ b : L', 2<p → v (p:L')=1 → 0≤v b → (curve b).Δ≠0 →
    (∀ C : WeierstrassCurve.VariableChange L', 0≤v (C • curve b).Δ → v (curve b).Δ≤v (C • curve b).Δ) →
    ∃ T : EllipticKernelChart v b, Nonempty (LogarithmOnLayers v T)

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
theorem minimalModelLogarithms_of_formal_group_theorems {p : ℕ} {w : HeightOneSpectrum (𝓞 K)}
    (classicalInputs : MinimalFormalGroupTheorems p w) : MinimalModelLogarithms p w := by
  classical
  intro b hp unram integral nonzero minimal
  obtain ⟨T,⟨A⟩⟩ := classicalInputs b hp unram integral nonzero minimal
  exact ⟨filteredLogarithm_of_formal_chart (completionOrder w) T A⟩

/-- Every odd prime, including 7, and Sun's actual point. -/
theorem odd_prime_scalar48_of_formal_group_theorems {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (classicalInputs : MinimalFormalGroupTheorems p w)
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D₀ : ℕ)
    (hr : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (hgn : Γ≠0) (unit : padicValRat p Γ=0)
    (live : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)) ≠ 0)
    (pole : 0≤padicValRat p (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)))) :
    (p:ℤ)^48 ∣ s-1 :=
  odd_prime_scalar48_of_minimal_log hp w root (minimalModelLogarithms_of_formal_group_theorems classicalInputs)
    hh D₀ hr odd hgn unit live pole

end Sun28.Scalar
#print axioms Sun28.Scalar.filteredLogarithm_of_formal_chart
#print axioms Sun28.Scalar.minimalModelLogarithms_of_formal_group_theorems
#print axioms Sun28.Scalar.odd_prime_scalar48_of_formal_group_theorems
