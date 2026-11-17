import FormalKernelLog

/-! Integral logarithmic series, their truncations, and valuation of the tail. -/
namespace Sun28.Ordinary
open Sun28.Scalar Sun28.ScalarTrace NumberField IsDedekindDomain Filter Topology WithZero
open scoped NumberField BigOperators

/-- The coefficient bound used in the ordinary degree-k test. -/
theorem denominator_bound {p k n : ℕ} [Fact p.Prime] (large : k+1<p) (tail : k<n) :
    k+1+padicValNat p n≤n := by
  rcases lt_trichotomy n p with h | rfl | h
  · rw [padicValNat.eq_zero_of_not_dvd (fun dv => (Nat.not_lt_of_ge (Nat.le_of_dvd (by omega) dv)) h)]
    omega
  · rw [padicValNat_self]
    omega
  · have := padicValNat_add_le_self (p:=p) h
    omega

/-- The first k terms are taken from the same
normalized invariant differential; index n is the exponent in the logarithm. -/
def logTrunc {L : Type*} [Field L] (a : ℕ → L) (k : ℕ) (z : L) : L :=
  ∑ i ∈ Finset.range k, a (i+1)*z^(i+1)/(i+1:ℕ)

theorem logTrunc_zero {L : Type*} [Field L] (a : ℕ→L) (k : ℕ) : logTrunc a k 0=0 := by
  simp [logTrunc]

/-- Every individual discarded monomial has valuation at least d+k when
the parameter has order d≥1. The coefficient integral here is the derivative coefficient. -/
theorem log_term_bound {L : Type*} [Field L] (v : AddValuation L (WithTop ℤ))
    {p k n : ℕ} [Fact p.Prime] (large : k+1<p) (tail : k<n)
    {a z : L} (integral : 0≤v a) {d : ℤ} (positive : 0<d) (hz : v z=(d:WithTop ℤ))
    (hn : v (n:L)=((padicValNat p n:ℤ):WithTop ℤ)) :
    ((d+k:ℤ):WithTop ℤ) ≤ v (a*z^n/(n:L)) := by
  have e := denominator_bound large tail
  have en : ((k:ℤ)+1+(padicValNat p n:ℤ)) ≤ n := by exact_mod_cast e
  have npos : 1≤(n:ℤ) := by exact_mod_cast (show 1≤n by omega)
  have ar : d+(k:ℤ) ≤ (n:ℤ)*d-(padicValNat p n:ℤ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr npos) (show 0≤d-1 by omega)]
  rw [v.map_div,v.map_mul,v.map_pow,hz,hn]
  calc
    ((d+k:ℤ):WithTop ℤ) ≤ ((n:ℤ)*d-(padicValNat p n:ℤ):ℤ) := WithTop.coe_le_coe.mpr ar
    _ = 0 + n • (d:WithTop ℤ) - ((padicValNat p n:ℤ):WithTop ℤ) := by norm_cast; ring
    _ ≤ _ := by
      rw [sub_eq_add_neg,sub_eq_add_neg]
      exact add_le_add (add_le_add integral le_rfl) le_rfl

/-- The closed balls for the actual discrete order of the completion. -/
theorem isClosed_order_ball {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (s : ℤ) :
    IsClosed {x : w.adicCompletion K | (s:WithTop ℤ)≤completionOrder w x} := by
  rw [←isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro x hx
  have nx : x≠0 := by
    rintro rfl
    simp [Set.mem_compl_iff] at hx
  have ne : (Valued.v x : ℤᵐ⁰)≠0 := ((Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰).ne_zero_iff).mpr nx
  filter_upwards [Valued.locally_const ne] with y hy
  have eq : completionOrder w y=completionOrder w x := by
    change _ = _ at hy
    unfold completionOrder discreteOrder
    simp only [AddValuation.of_apply]
    rw [show (Valued.v y : ℤᵐ⁰)=Valued.v x from hy]
  simpa only [Set.mem_compl_iff,Set.mem_ofPred_eq,eq] using hx

/-- Passage from the coefficients to the analytic error. Only convergence
of the complete logarithm is supplied, with no rate imposed. -/
theorem log_trunc_error {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {p k : ℕ} [Fact p.Prime] (large : k+1<p)
    (a : ℕ→w.adicCompletion K) (integral : ∀ n, 0≤completionOrder w (a n))
    (intOrder : ∀ n : ℕ, n≠0 → completionOrder w (n:w.adicCompletion K)=((padicValNat p n:ℤ):WithTop ℤ))
    {z S : w.adicCompletion K} {d : ℤ} (positive : 0<d) (hz : completionOrder w z=(d:WithTop ℤ))
    (series : Tendsto (fun n => logTrunc a n z) atTop (𝓝 S)) :
    ((d+k:ℤ):WithTop ℤ) ≤ completionOrder w (S-logTrunc a k z) := by
  let v := completionOrder w
  have tail (j : ℕ) : ((d+k:ℤ):WithTop ℤ) ≤ v (logTrunc a (k+j) z - logTrunc a k z) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := log_term_bound v large (n:=k+j+1) (by omega) (integral (k+j+1)) positive hz
        (intOrder _ (by omega))
      have split : logTrunc a (k+(j+1)) z - logTrunc a k z =
          (logTrunc a (k+j) z-logTrunc a k z) + a (k+j+1)*z^(k+j+1)/(k+j+1:ℕ) := by
        unfold logTrunc
        rw [show k+(j+1)=k+j+1 by omega,Finset.sum_range_succ]
        abel
      rw [split]
      exact v.map_le_add ih h
  apply (isClosed_order_ball w (d+k)).mem_of_tendsto (series.sub tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop k] with n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact tail j

end Sun28.Ordinary
#print axioms Sun28.Ordinary.denominator_bound
#print axioms Sun28.Ordinary.logTrunc_zero
#print axioms Sun28.Ordinary.log_term_bound
#print axioms Sun28.Ordinary.isClosed_order_ball
#print axioms Sun28.Ordinary.log_trunc_error
