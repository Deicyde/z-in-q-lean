import SunIndex
import QuadraticAverage

/-! Application of the two-entry normalized trace at an odd scalar contact. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]

/-- At a scalar odd contact the pole bound on the normalized trace gives divisibility.
The comparison hypothesis is the formal-parameter lemma at the two primes above p. -/
theorem trace_scalar48 {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[ℚ] K) (hσ : σ≠1)
    {ρ : K} (root : ρ^2=2) (h2 : w (2:K)=0)
    (P : (curve (-(3-ρ)^2)).Point) (hinf : ∀ j : ℤ, j≠0 → j • P≠0)
    (comp₁ : FormalComparison p w P) (comp₂ : FormalComparison p (w.comap σ.toRingHom) P)
    {h s : ℤ} (hh : h≠0) {r Γ D₀ : ℚ} {α : ℤ}
    (hr : w (algebraMap ℚ K r)=(α:WithTop ℤ)) (ho : Odd α)
    (front : w (algebraMap ℚ K (Γ/(1+D₀*r^2)))=0)
    (nonzero : scalarTheta r (reciprocal (h • P))
      (parameter ((s-1) • P)/parameter (h • P))≠0)
    (pole : 0 ≤ w (algebraMap ℚ K (scalarValue r Γ D₀ (reciprocal (h • P))
      (parameter ((s-1) • P)/parameter (h • P))))) : (p:ℤ)^48 ∣ s-1 := by
  obtain ⟨_,hval⟩ := two_tests_one_branch w σ hσ hr ho h2 front nonzero pole
  rcases hval with ⟨f₁,f₂⟩|⟨f₁,f₂⟩
  · exact cyclic_scalar48 hp w root h2 P hinf comp₁ hh f₁ f₂
  · have two : w.comap σ.toRingHom (2:K)=0 := by
      change w (σ 2)=0
      simpa only [map_ofNat] using h2
    exact cyclic_scalar48 hp (w.comap σ.toRingHom) root two P hinf comp₂ hh f₁ f₂

#print axioms trace_scalar48
end
end Sun28.Scalar
