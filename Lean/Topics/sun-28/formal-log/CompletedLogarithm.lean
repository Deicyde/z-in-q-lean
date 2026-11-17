import FilteredLogarithm

/-! The actual completion at a prime of the quadratic field and Sun's
elliptic model. All ramification and integer-valuation hypotheses are derived. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace NumberField IsDedekindDomain WithZero
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- Integral additive order on the complete local field at a height-one prime. -/
noncomputable def completionOrder (w : HeightOneSpectrum (𝓞 K)) :
    AddValuation (w.adicCompletion K) (WithTop ℤ) :=
  discreteOrder (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
theorem completionOrder_algebraMap (w : HeightOneSpectrum (𝓞 K)) (q : K) :
    completionOrder w (algebraMap K (w.adicCompletion K) q) = discreteOrder (w.valuation K) q := by
  unfold completionOrder discreteOrder
  simp only [AddValuation.of_apply]
  congr 1
  exact w.valuedAdicCompletion_eq_valuation' q

/-- The published elliptic formal logarithm on the kernel of reduction,
restricted along the specified embedding of the global points. -/
def CompletedFilteredLog (w : HeightOneSpectrum (𝓞 K)) (τ : K ≃ₐ[ℚ] K) (b : K) : Prop :=
  Nonempty (FilteredLogarithm ((discreteOrder (w.valuation K)).comap τ.toRingHom) (completionOrder w) b)

/-- The integer normalization and the comparison hold simultaneously for each
conjugate of the global embedding into the same complete local field. -/
theorem formalComparison_at_prime {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (τ : K ≃ₐ[ℚ] K) (C : CompletedFilteredLog w τ (-(3-ρ)^2))
    (P : (curve (-(3-ρ)^2)).Point) :
    FormalComparison p ((discreteOrder (w.valuation K)).comap τ.toRingHom) P := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name hp
  let u := discreteOrder (w.valuation K)
  have rat {q : ℚ} (hq : q≠0) : u (algebraMap ℚ K q) = ((padicValRat p q:ℤ):WithTop ℤ) := by
    simpa [u,unram,name] using (prime_order_rat v w hq)
  have h2 : u.comap τ.toRingHom (2:K)=0 := by
    change u (τ 2)=0
    have dv : ¬p ∣ 2 := fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) hp
    have ht : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd dv] using (padicValRat.of_nat (p:=p) (n:=2))
    simpa only [map_ofNat,ht,WithTop.coe_zero] using (rat (q:=2) (by norm_num))
  obtain ⟨C⟩ := C
  apply formalComparison_of_filteredLogarithm (u.comap τ.toRingHom) (completionOrder w) C
    (paper_coefficient _ root h2) _ P
  intro n hn
  have int := rat (q:=(n:ℚ)) (by exact_mod_cast hn)
  rw [map_intCast,padicValRat.of_int] at int
  rw [←map_intCast (algebraMap K (w.adicCompletion K)), completionOrder_algebraMap]
  exact int

/-- The scalar divisibility conclusion from rational contact, numerator, and pole orders.
The prime above p is arbitrary. -/
theorem odd_prime_scalar48_of_filteredLog {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2)
    (logs : ∀ τ : K ≃ₐ[ℚ] K, CompletedFilteredLog w τ (-(3-ρ)^2))
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D₀ : ℕ)
    (hr : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (hgn : Γ≠0) (unit : padicValRat p Γ=0)
    (live : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)) ≠ 0)
    (pole : 0≤padicValRat p (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)))) :
    (p:ℤ)^48 ∣ s-1 :=
  odd_prime_scalar48_of_formalComparison hp w root
    (fun τ => formalComparison_at_prime hp w root τ (logs τ) (paperGenerator root)) hh D₀ hr odd hgn unit live pole

end Sun28.Scalar
#print axioms Sun28.Scalar.completionOrder_algebraMap
#print axioms Sun28.Scalar.formalComparison_at_prime
#print axioms Sun28.Scalar.odd_prime_scalar48_of_filteredLog
