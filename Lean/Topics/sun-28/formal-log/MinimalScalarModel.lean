import GoodModelLog

/-! The formal kernel at an odd prime of bad reduction is still covered by
Silverman's theorem for a minimal integral equation. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField

/-- An integral discriminant of order less than twelve has smallest order
even among coordinate changes whose discriminant alone is integral. -/
theorem minimal_discriminant_of_lt_twelve {L : Type*} [Field L]
    (u : AddValuation L (WithTop ℤ)) (W : WeierstrassCurve L) {d : ℤ}
    (vd : u W.Δ=(d:WithTop ℤ)) (small : d<12)
    (C : WeierstrassCurve.VariableChange L) (integral : 0≤u (C • W).Δ) : u W.Δ≤u (C • W).Δ := by
  obtain ⟨s,hs⟩ := finite_order u (Units.ne_zero C.u)
  rw [WeierstrassCurve.variableChange_Δ,u.map_mul,u.map_pow,Units.val_inv_eq_inv_val,u.map_inv,hs,vd] at integral ⊢
  have bound : 0 ≤ 12 * (-s) + d := by exact_mod_cast integral
  have h : d ≤ 12 * (-s) + d := by omega
  exact_mod_cast h

/-- At the bad rational prime the discriminant has order at most six for either embedding. -/
theorem seventh_discriminant_bound {K : Type*} [Field K] [CharZero K]
    (u : AddValuation K (WithTop ℤ)) {ρ : K} (root : ρ^2=2)
    (two : u (2:K)=0) (seven : u (7:K)=1) :
    ∃ d : ℤ, u (curve (-(3-ρ)^2)).Δ=(d:WithTop ℤ) ∧ 0≤d ∧ d≤6 := by
  have intNat (n:ℕ) : 0≤u (n:K) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact u.map_le_add ih (by simp)
  have rn : ρ≠0 := by rintro rfl; norm_num at root
  obtain ⟨d,hd⟩ := finite_order u rn
  have hh := congrArg u root
  rw [u.map_pow,hd,two] at hh
  have ed : 2*d=0 := by exact_mod_cast hh
  have int : 0≤u ρ := hd ▸ WithTop.coe_le_coe.mpr (show 0≤d by omega)
  have a : 0≤u (3-ρ) := u.map_le_sub (intNat 3) int
  have b : 0≤u (3+ρ) := u.map_le_add (intNat 3) int
  have product : (3-ρ)*(3+ρ)=7 := by linear_combination -root
  have h := congrArg u product
  rw [u.map_mul,seven] at h
  have nz : 3-ρ≠0 := by
    intro z
    rw [z,zero_mul] at product
    norm_num at product
  obtain ⟨s,hs⟩ := finite_order u nz
  have low : 0≤s := WithTop.coe_le_coe.mp (hs ▸ a)
  have high : s≤1 := WithTop.coe_le_coe.mp (hs ▸ ((le_add_of_nonneg_right b).trans h.le))
  refine ⟨6*s,?_,by omega,by omega⟩
  rw [sun_discriminant,u.map_mul,u.map_pow,u.map_pow,two,nsmul_zero,zero_add,hs]
  norm_cast

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

omit [DecidableEq K] in
/-- Every odd place has ramification index one, integral coefficient and
a discriminant of order below 12 for both conjugate embeddings. -/
theorem small_discriminant_at_odd_prime {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    (τ : K ≃ₐ[ℚ] K) {ρ : K} (root : ρ^2=2) :
    let u := (discreteOrder (w.valuation K)).comap τ.toRingHom
    completionOrder w (p:w.adicCompletion K)=1 ∧ 0≤u (-(3-ρ)^2) ∧
      ∃ d : ℤ, u (curve (-(3-ρ)^2)).Δ=(d:WithTop ℤ) ∧ 0≤d ∧ d<12 := by
  by_cases h7 : p=7
  · subst p
    let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨7,Fact.out⟩
    have name : (Rat.HeightOneSpectrum.primesEquiv v).1=7 :=
      congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨7,Fact.out⟩)
    have unram := sqrtTwo_unramified root v w name hp
    let u := (discreteOrder (w.valuation K)).comap τ.toRingHom
    have rational {q : ℚ} (hq : q≠0) : discreteOrder (w.valuation K) (algebraMap ℚ K q) =
        ((padicValRat 7 q:ℤ):WithTop ℤ) := by
      simpa [unram,name] using prime_order_rat v w hq
    have seven := rational (q:=7) (by norm_num)
    have two := rational (q:=2) (by norm_num)
    have twoVal : padicValRat 7 (2:ℚ)=0 := by
      simpa [padicValNat.eq_zero_of_not_dvd (by decide : ¬ 7∣2)] using (padicValRat.of_nat (p:=7) (n:=2))
    rw [twoVal,map_ofNat] at two
    have sevenVal : padicValRat 7 (7:ℚ)=1 := by simpa using (padicValRat.self (p:=7) (by decide : 1<7))
    rw [sevenVal,map_ofNat] at seven
    have seven' : u (7:K)=1 := by change discreteOrder _ (τ 7)=1; simpa only [map_ofNat,WithTop.coe_one] using seven
    have two' : u (2:K)=0 := by change discreteOrder _ (τ 2)=0; simpa only [map_ofNat,WithTop.coe_zero] using two
    obtain ⟨d,hd,low,high⟩ := seventh_discriminant_bound u root two' seven'
    refine ⟨?_,paper_coefficient u root two',d,hd,low,by omega⟩
    have ord := completionOrder_algebraMap w (7:K)
    rw [map_ofNat] at ord
    simpa using ord.trans seven
  · obtain ⟨one,int,unit⟩ := good_scalar_prime hp h7 w τ root
    exact ⟨one,int,0,unit,by decide,by decide⟩

end Sun28.Scalar
#print axioms Sun28.Scalar.minimal_discriminant_of_lt_twelve
#print axioms Sun28.Scalar.seventh_discriminant_bound
#print axioms Sun28.Scalar.small_discriminant_at_odd_prime
