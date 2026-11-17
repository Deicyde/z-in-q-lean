import OrdinaryTrace
import OrdinaryDivisibility
import OrdinaryIndex

/-! Sun's literal sixteen tests at an ordinary contact, including conjugation,
trace selection and descent to the rational numerator. -/
open Sun28.Scalar Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField
namespace Sun28.Ordinary

inductive OrdinaryTest
  | h | u (i : Fin 4) | v₀ | v (i : Fin 4) | difference (i : Fin 4) | delta | beta
  deriving DecidableEq, Fintype

def orderRequired : OrdinaryTest → ℕ
  | .h | .u _ | .v₀ | .v _ => 1
  | .difference _ | .delta => 64
  | .beta => 16

theorem sixteen_orders : Fintype.card OrdinaryTest = 16 ∧ ∀ i, 1 ≤ orderRequired i := by
  refine ⟨by decide,?_⟩
  intro i
  cases i <;> norm_num [orderRequired]

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

noncomputable def ordinaryTests {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β : ℚ) : OrdinaryTest → K :=
  let P := paperGenerator root
  let L := fun i => ordinaryRatio P (m i) h
  let L' := fun i => σ (ordinaryRatio P (m i-c*n i) (h-c))
  fun test => match test with
  | .h => reciprocal (h • P)
  | .u i => reciprocal (m i • P)
  | .v₀ => σ (reciprocal ((h-c) • P))
  | .v i => σ (reciprocal ((m i-c*n i) • P))
  | .difference i => L i-L' i
  | .delta => lucas (L 1) (L 2) (L 3)
  | .beta => L 0-algebraMap ℚ K β

/-- Section 3 of Sun. All local tests are imposed at the same embedding. -/
theorem sixteen_test_outputs {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (classicalInput : OrdinaryLogarithms p w) (σ τ : K ≃ₐ[ℚ] K)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β : ℚ) (anchor : ¬(p:ℤ) ∣ c)
    (hh : h≠0) (hc : h-c≠0)
    (tests : ∀ i, (orderRequired i : WithTop ℤ) ≤
      discreteOrder (w.valuation K) (τ (ordinaryTests root σ c h n m β i))) :
    (p:ℤ)^64 ∣ lucas (n 1) (n 2) (n 3) ∧ (p:ℤ)^16 ∣ (β-n 0).num := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name (by omega)
  let u := discreteOrder (w.valuation K)
  have unit : u (c:K)=0 := by
    have cn : c≠0 := fun hz => anchor (hz ▸ dvd_zero _)
    have eq := prime_order_rat v w (q:=(c:ℚ)) (by exact_mod_cast cn)
    simpa [u,name,unram,padicValInt.eq_zero_of_not_dvd anchor] using eq
  let P := paperGenerator root
  let L := fun i => τ (ordinaryRatio P (m i) h)
  let L' := fun i => τ (σ (ordinaryRatio P (m i-c*n i) (h-c)))
  have first (i : Fin 4) := (ordinary_index_ratio64 large w root classicalInput τ (m i) h hh
    (tests (.u i)) (tests .h)).2
  have second (i : Fin 4) := (ordinary_index_ratio64 large w root classicalInput (σ.trans τ)
    (m i-c*n i) (h-c) hc (tests (.v i)) (tests .v₀)).2
  have comp (i : Fin 4) : (64:WithTop ℤ) ≤ u (L i-L' i) := by
    simpa only [ordinaryTests,orderRequired,Nat.cast_ofNat,map_sub] using tests (.difference i)
  have td : (64:WithTop ℤ) ≤ u (lucas (L 1) (L 2) (L 3)) := by
    simpa only [ordinaryTests,orderRequired,Nat.cast_ofNat,lucas,map_sub,map_add,map_mul,map_pow,map_one,map_ofNat] using tests .delta
  have tb : (16:WithTop ℤ) ≤ u (L 0-algebraMap ℚ K β) := by
    simpa only [ordinaryTests,orderRequired,Nat.cast_ofNat,map_sub,AlgEquiv.commutes] using tests .beta
  obtain ⟨outD,outB⟩ := ordinary_precisions (L:=L) (L':=L') u unit first second comp td tb
  exact rational_outputs v w name unram outD outB

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
/-- Normalization by powers of a local unit leaves every test order unchanged. -/
theorem scale_test_orders {I : Type*} (v : AddValuation K (WithTop ℤ)) (τ : K ≃ₐ[ℚ] K)
    (s : ℚ) (unit : v (algebraMap ℚ K s)=0) (D : I → K) (k : I → ℕ)
    (tests : ∀ i, (k i : WithTop ℤ) ≤ v (τ (D i/(algebraMap ℚ K s)^(k i+1)))) :
    ∀ i, (k i : WithTop ℤ) ≤ v (τ (D i)) := by
  intro i
  simpa only [map_div₀,map_pow,AlgEquiv.commutes,v.map_div,v.map_pow,unit,nsmul_zero,sub_zero] using tests i

/-- The ordinary pole of section 4 gives the two divisibilities at one prime.
The detector order may initially be negative. -/
theorem ordinary_contact_divides {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (classicalInput : OrdinaryLogarithms p w)
    (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β r s : ℚ) (anchor : ¬(p:ℤ) ∣ c)
    (hh : h≠0) (hc : h-c≠0)
    {α : ℤ} (odd : Odd α)
    (hr : discreteOrder (w.valuation K) (algebraMap ℚ K r)=(α:WithTop ℤ))
    (unit : discreteOrder (w.valuation K) (algebraMap ℚ K s)=0)
    (live : ordinaryTrace r (fun i => ordinaryTests root σ c h n m β i/(algebraMap ℚ K s)^(orderRequired i+1)) orderRequired≠0)
    (pole : 0 ≤ discreteOrder (w.valuation K) (algebraMap ℚ K
      (r/(ordinaryTrace r (fun i => ordinaryTests root σ c h n m β i/(algebraMap ℚ K s)^(orderRequired i+1)) orderRequired)^2))) :
    0 < α ∧ (p:ℤ)^64 ∣ lucas (n 1) (n 2) (n 3) ∧ (p:ℤ)^16 ∣ (β-n 0).num := by
  let u := discreteOrder (w.valuation K)
  let D := ordinaryTests root σ c h n m β
  obtain ⟨ha,τ,selected⟩ := ordinaryTrace_orders u σ hs r
    (fun i => D i/(algebraMap ℚ K s)^(orderRequired i+1)) orderRequired sixteen_orders.2 hr odd live pole
  have original := scale_test_orders u τ s unit D orderRequired selected
  exact ⟨ha,sixteen_test_outputs large w root classicalInput σ τ c h n m β anchor hh hc original⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.sixteen_orders
#print axioms Sun28.Ordinary.sixteen_test_outputs
#print axioms Sun28.Ordinary.scale_test_orders
#print axioms Sun28.Ordinary.ordinary_contact_divides
