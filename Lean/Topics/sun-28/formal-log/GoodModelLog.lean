import GoodScalarReduction
import LocalPointMap

/-! The published local-field result has an explicit statement on the actual
completed model and makes no reference to Sun's point, indices or detector. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- Restriction of Silverman VII.2.2 and IV.6.4(b) to short elliptic models of unit
discriminant over this complete local field. -/
def GoodModelLogarithms (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := by
  classical
  let L := w.adicCompletion K
  let u := completionOrder w
  exact ∀ b : L, 2<p → u (p:L)=1 → 0≤u b → u (curve b).Δ=0 → Nonempty (FilteredLogarithm u u b)

/-- Transport the complete-field theorem along the actual conjugate field embedding.
The local discriminant and the ramification hypotheses hold for every p outside 2 and 7. -/
theorem completedFilteredLog_of_goodModel {p : ℕ} [Fact p.Prime] (hp : 2<p) (h7 : p≠7)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (published : GoodModelLogarithms p w) (τ : K ≃ₐ[ℚ] K) :
    CompletedFilteredLog w τ (-(3-ρ)^2) := by
  classical
  let L := w.adicCompletion K
  let v := completionOrder w
  let u := (discreteOrder (w.valuation K)).comap τ.toRingHom
  let f : K →+* L := (algebraMap K L).comp τ.toRingHom
  let b : K := -(3-ρ)^2
  have agrees (x : K) : v (f x)=u x := completionOrder_algebraMap w (τ x)
  obtain ⟨unram,bint,dunit⟩ := good_scalar_prime hp h7 w τ root
  have delta : (curve (f b)).Δ=f (curve b).Δ := by
    simp [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈,map_ofNat]
  have dlocal : v (curve (f b)).Δ=0 := by rw [delta,agrees]; exact dunit
  have blocal : 0≤v (f b) := (agrees b).symm ▸ bint
  obtain ⟨C⟩ := published (f b) hp unram blocal dlocal
  exact ⟨pullback_filteredLog f agrees C⟩

/-- The scalar divisibility conclusion from rational contact, numerator, and pole orders.
The prime above p is arbitrary. -/
theorem odd_prime_scalar48_of_local_log {p : ℕ} [Fact p.Prime] (hp : 2<p) (h7 : p≠7)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2)
    (published : GoodModelLogarithms p w)
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D₀ : ℕ)
    (hr : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (hgn : Γ≠0) (unit : padicValRat p Γ=0)
    (live : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)) ≠ 0)
    (pole : 0≤padicValRat p (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)))) :
    (p:ℤ)^48 ∣ s-1 :=
  odd_prime_scalar48_of_filteredLog hp w root
    (completedFilteredLog_of_goodModel hp h7 w root published) hh D₀ hr odd hgn unit live pole

end Sun28.Scalar
#print axioms Sun28.Scalar.completedFilteredLog_of_goodModel
#print axioms Sun28.Scalar.odd_prime_scalar48_of_local_log
