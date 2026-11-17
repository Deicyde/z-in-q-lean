import CompletedLogarithm

/-! The fixed model has unit discriminant for p outside 2 and 7.
The finite-prime specialization verifies the hypotheses of the textbook logarithm theorem. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

omit [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
theorem sun_discriminant {ρ : K} : (curve (-(3-ρ)^2)).Δ = (2:K)^6*(3-ρ)^6 := by
  simp [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
theorem conjugate_discriminant_unit (u : AddValuation K (WithTop ℤ)) {ρ : K} (root : ρ^2=2)
    (h2 : u (2:K)=0) (h7 : u (7:K)=0) : u (curve (-(3-ρ)^2)).Δ=0 := by
  have positiveNat (n:ℕ) : 0≤u (n:K) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact u.map_le_add ih (by simp)
  have rn : ρ≠0 := by rintro rfl; norm_num at root
  obtain ⟨d,hd⟩ := finite_order u rn
  have hh := congrArg u root
  rw [u.map_pow,hd,h2] at hh
  have ed : 2*d=0 := by exact_mod_cast hh
  have int : 0≤u ρ := hd ▸ WithTop.coe_le_coe.mpr (show 0≤d by omega)
  have a : 0≤u (3-ρ) := u.map_le_sub (positiveNat 3) int
  have b : 0≤u (3+ρ) := u.map_le_add (positiveNat 3) int
  have eq : (3-ρ)*(3+ρ)=7 := by linear_combination -root
  have va := congrArg u eq
  rw [u.map_mul,h7] at va
  have unit : u (3-ρ)=0 := le_antisymm ((le_add_of_nonneg_right b).trans va.le) a
  rw [sun_discriminant,u.map_mul,u.map_pow,u.map_pow,unit,h2,nsmul_zero,zero_add]

omit [DecidableEq K] in
/-- For every chosen embedding over a rational prime p outside 2 and 7, both the
rational ramification index and the Weierstrass discriminant orders are as required. -/
theorem good_scalar_prime {p : ℕ} [Fact p.Prime] (hp : 2<p) (h7 : p≠7)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    (τ : K ≃ₐ[ℚ] K) {ρ : K} (root : ρ^2=2) :
    let u := (discreteOrder (w.valuation K)).comap τ.toRingHom
    completionOrder w (p:w.adicCompletion K)=1 ∧ 0≤u (-(3-ρ)^2) ∧ u (curve (-(3-ρ)^2)).Δ=0 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name hp
  let u := (discreteOrder (w.valuation K)).comap τ.toRingHom
  have onRat {q : ℚ} (n : q≠0) :
      discreteOrder (w.valuation K) (algebraMap ℚ K q)=((padicValRat p q:ℤ):WithTop ℤ) := by
    simpa [unram,name] using prime_order_rat v w n
  have nat_unit {k : ℕ} (nk : k≠0) (nd : ¬p∣k) : u (k:K)=0 := by
    have hz : padicValRat p (k:ℚ)=0 := by
      rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd,Int.natCast_zero]
    have eq := onRat (q:=k) (by exact_mod_cast nk)
    change discreteOrder (w.valuation K) (τ (k:K))=0
    simpa only [map_natCast,hz,WithTop.coe_zero] using eq
  have nd2 : ¬ p∣2 := fun nd => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) nd)) hp
  have nd7 : ¬p∣7 := by
    intro h
    have eq := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h
    rcases eq with h|h <;> omega
  have two : u (2:K)=0 := nat_unit (k:=2) (by decide) nd2
  have seven : u (7:K)=0 := nat_unit (k:=7) (by decide) nd7
  refine ⟨?_,paper_coefficient u root two,conjugate_discriminant_unit u root two seven⟩
  have pn : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := onRat (q:=p) pn
  rw [padicValRat.self (Fact.out : p.Prime).one_lt,map_natCast] at h
  rw [←map_natCast (algebraMap K (w.adicCompletion K)),completionOrder_algebraMap]
  exact h

end Sun28.Scalar
#print axioms Sun28.Scalar.sun_discriminant
#print axioms Sun28.Scalar.conjugate_discriminant_unit
#print axioms Sun28.Scalar.good_scalar_prime
