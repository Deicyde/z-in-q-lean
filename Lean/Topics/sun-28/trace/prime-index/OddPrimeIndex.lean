import SqrtTwoUnramified
import SunPublishedScalar

/-! Sun's published generator, the normalized trace and an actual finite prime. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace IsDedekindDomain NumberField
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- The scalar divisibility conclusion from rational contact, numerator, and pole orders.
The prime above p is arbitrary. -/
theorem odd_prime_scalar48 {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2)
    (infinite : addOrderOf (paperGenerator root)=0)
    (comparison : ∀ τ : K ≃ₐ[ℚ] K,
       FormalComparison p ((discreteOrder (w.valuation K)).comap τ.toRingHom) (paperGenerator root))
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D₀ : ℕ)
    (hr : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (hgn : Γ≠0) (unit : padicValRat p Γ=0)
    (live : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)) ≠ 0)
    (pole : 0≤padicValRat p (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)))) :
    (p:ℤ)^48 ∣ s-1 := by
  classical
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unramified := sqrtTwo_unramified root v w name hp
  have hcard : 1 < Fintype.card (K ≃ₐ[ℚ] K) := by
    rw [←Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]
    decide
  have _ : Nontrivial (K ≃ₐ[ℚ] K) := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨σ,hσ⟩ := exists_ne (1:K ≃ₐ[ℚ] K)
  let P := paperGenerator root
  let u := discreteOrder (w.valuation K)
  have hinf (j : ℤ) (hj : j≠0) : j • P≠0 := by
    intro z
    have d := addOrderOf_dvd_iff_zsmul_eq_zero.mpr z
    change (addOrderOf (paperGenerator root) : ℤ) ∣ j at d
    rw [infinite] at d
    simp [hj] at d
  have h2 : u (2:K)=0 := by
    have nd : ¬p ∣ 2 := fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) hp
    have ht : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd] using (padicValRat.of_nat (p:=p) (n:=2))
    simpa [u,name,unramified,ht,map_ofNat] using prime_order_rat v w (q:=2) (by norm_num)
  obtain hu | hu := unramified_two_tests v w unramified name hp σ hσ D₀ hr odd hgn unit live pole
  all_goals obtain ⟨first,second⟩ := hu.orders hr
  · exact cyclic_scalar48 hp u root h2 P hinf (comparison 1) hh first second
  · have h2' : u.comap σ.toRingHom (2:K)=0 := by
      change u (σ 2)=0
      simpa only [map_ofNat] using h2
    exact cyclic_scalar48 hp (u.comap σ.toRingHom) root h2' P hinf (comparison σ) hh first second

end Sun28.Scalar
#print axioms Sun28.Scalar.odd_prime_scalar48
