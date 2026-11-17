import QuadraticAverage
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! The split-place interface in ordinary rational p-adic valuations. -/
namespace Sun28.ScalarTrace
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A quadratic extension embedded in Q_p has the ordinary additive order
on nonzero rational elements, with no factor of the ramification index. -/
theorem split_order_rat {p : ℕ} [Fact p.Prime] (ι : K →ₐ[ℚ] ℚ_[p]) {q : ℚ} (hq : q≠0) :
    (AddValuation.comap ι.toRingHom Padic.addValuation) (algebraMap ℚ K q) =
      ((padicValRat p q:ℤ):WithTop ℤ) := by
  change Padic.addValuation (ι (algebraMap ℚ K q)) = _
  rw [ι.commutes]
  change Padic.addValuation (q:ℚ_[p]) = _
  rw [Padic.addValuation.apply (by exact_mod_cast hq),Padic.valuation_ratCast]

/-- At a split odd prime the hypotheses on the scalar are ordinary rational
p-adic orders. Both normalized test orders occur in the same embedding. -/
theorem split_two_tests [Algebra.IsQuadraticExtension ℚ K] {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (ι : K →ₐ[ℚ] ℚ_[p]) (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1)
    {r Γ D₀ : ℚ} {x y : K}
    (ho : Odd (padicValRat p r)) (hA : Γ/(1+D₀*r^2) ≠ 0)
    (hfront : padicValRat p (Γ/(1+D₀*r^2))=0) (hn : scalarTheta r x y ≠ 0)
    (hB : 0 ≤ padicValRat p (scalarValue r Γ D₀ x y)) :
    0 < padicValRat p r ∧
    ((1:WithTop ℤ) ≤ Padic.addValuation (ι x) ∧ (48:WithTop ℤ) ≤ Padic.addValuation (ι y) ∨
     (1:WithTop ℤ) ≤ Padic.addValuation (ι (σ x)) ∧ (48:WithTop ℤ) ≤ Padic.addValuation (ι (σ y))) := by
  let v : AddValuation K (WithTop ℤ) := AddValuation.comap ι.toRingHom Padic.addValuation
  have hr : r≠0 := by
    rintro rfl
    simp at ho
  have hb : scalarValue r Γ D₀ x y ≠ 0 := by
    unfold scalarValue
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hA) hr) (pow_ne_zero _ hn)
  have htwo : v (2:K)=0 := by
    have hv := split_order_rat ι (q := 2) (by norm_num)
    have h2p : ¬ p ∣ 2 := by
      exact fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) hp
    have hz : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd h2p] using
        (padicValRat.of_nat (p:=p) (n:=2))
    simpa [v,hz,map_ofNat] using hv
  have fa : v (algebraMap ℚ K (Γ/(1+D₀*r^2)))=0 := by
    rw [show v (algebraMap ℚ K (Γ/(1+D₀*r^2))) = _ from split_order_rat ι hA,hfront]
    rfl
  have fb : (0:WithTop ℤ) ≤ v (algebraMap ℚ K (scalarValue r Γ D₀ x y)) := by
    rw [show v (algebraMap ℚ K (scalarValue r Γ D₀ x y)) = _ from split_order_rat ι hb]
    exact WithTop.coe_le_coe.mpr hB
  exact two_tests_one_branch v σ hσ (split_order_rat ι hr) ho htwo fa hn fb

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.split_order_rat
#print axioms Sun28.ScalarTrace.split_two_tests
