import SixUnitHeight
import PublicMargin

/-! A height criterion on actual rational points of the six-contact twist. -/
namespace ZInQBlueprint.SixUnitCharts
open Sun28.Ordinary Sun28.FiveMarkUnits Height ZInQ
open ZInQBlueprint.OddSupport ZInQBlueprint.TwistDescent

/-- The product of the distinct primes in the chosen three rows and in 6. -/
def conductor (i j k : Fin 6) (a b : ℤ) : ℕ :=
  primeProduct (fixedPrimes ∪ triplePrimes i j k a b)

/-- Every row is nonzero on the nonbranch locus of the twist. -/
theorem twist_rows {d : ℤ} {x y : ℚ} (hd : d≠0) (hy : y≠0)
    (point : 30*(d:ℚ)*y^2=quintic x) : ∀ i,row i x.num x.den≠0 := by
  have dn : (x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  have aa : (x.num:ℚ)=x*(x.den:ℚ) := (div_eq_iff dn).mp x.num_div_den
  have nz : quintic x≠0 := by
    rw [←point]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hd)) (pow_ne_zero _ hy)
  have off (c : ℤ) (hc : quintic (c:ℚ)=0) : x.num+c*(-(x.den:ℤ))≠0 := by
    intro he
    have eqQ : (x.num:ℚ)+(c:ℚ)*(-(x.den:ℚ))=0 := by exact_mod_cast he
    rw [aa] at eqQ
    have prod : (x-(c:ℚ))*(x.den:ℚ)=0 := by linarith only [eqQ]
    exact nz (((sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right dn)) ▸ hc))
  have h0 := off 0 (by norm_num [quintic])
  have h1 := off 1 (by norm_num [quintic])
  have hn1 := off (-1) (by norm_num [quintic])
  have h3 := off 3 (by norm_num [quintic])
  have hn3 := off (-3) (by norm_num [quintic])
  intro i
  fin_cases i <;> simp [row,coeffA,coeffB] at * <;> omega

theorem chart_estimate (published : PublishedCorollary72) {x : ℚ}
    {i j k : Fin 6} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (off : ∀ n,row n x.num x.den≠0) :
    let N : ℝ := conductor i j k x.num x.den
    ratHeight x ≤ (3/2)*(128*N)*Real.log (128*N)^2+65+Real.log 18 := by
  let S := fixedPrimes ∪ triplePrimes i j k x.num x.den
  let u := crossRatio i j k x.num x.den
  have prime (p : ℕ) (hp : p∈S) : p.Prime := by
    rcases Finset.mem_union.mp hp with f|t
    · simp only [fixedPrimes,Finset.mem_insert,Finset.mem_singleton] at f
      rcases f with rfl|rfl
      exact Nat.prime_two
      exact Nat.prime_three
    · exact support_prime t
  have h := localised_pair ij ik jk _ _ off
  have src := (supported_corollary published S prime u (1-u) h.1 h.2 (by ring)).1
  have prim : Int.gcd x.num (x.den:ℤ)=1 := by simpa [Int.gcd] using x.reduced
  have changeHeight := crossRatio_height i j k ij ik jk prim off
  have base := signed_height (B:=(x.den:ℤ)) (by exact_mod_cast x.den_nz) prim
  rw [Int.cast_natCast,Rat.num_div_den] at base
  rw [ZInQ.Mult.ratHeight_eq_logHeight₁,base]
  exact changeHeight.trans (add_le_add_left (by simpa only [u,S,conductor,show (2:ℝ)^7=128 by norm_num] using src) _)

theorem chart_height (published : PublishedCorollary72) {x : ℚ} {D : ℕ} (dpos : 0<D)
    {i j k : Fin 6} (ij : i≠j) (ik : i≠k) (jk : j≠k) (off : ∀ n,row n x.num x.den≠0)
    (small : conductor i j k x.num x.den ≤ (100*D)^23) :
    ratHeight x ≤ 10^54*(D:ℝ)^24 := by
  let N := conductor i j k x.num x.den
  have np : 0<N := by
    unfold N conductor primeProduct
    apply Finset.prod_pos
    intro p hp
    rcases Finset.mem_union.mp hp with f|t
    · simp only [fixedPrimes,Finset.mem_insert,Finset.mem_singleton] at f
      omega
    · exact (support_prime t).pos
  have dr : 1≤(D:ℝ) := by exact_mod_cast dpos
  have nr : (1:ℝ)≤N := by exact_mod_cast np
  have smallR : (N:ℝ)≤(100*(D:ℝ))^23 := by exact_mod_cast small
  have est := analytic_absorption nr (by linarith only [dr] : (1:ℝ)≤100*D) smallR
  have h := chart_estimate published ij ik jk off
  change ratHeight x ≤ (3/2)*(128*(N:ℝ))*Real.log (128*(N:ℝ))^2+65+Real.log 18 at h
  have d24 : (1:ℝ)≤(D:ℝ)^24 := one_le_pow₀ dr
  have l := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<18)
  rw [mul_pow] at est
  linarith only [h,est,d24,l]

/-- Only twist points for which every three-row conductor is large remain. -/
def LargeTriples (H : ℝ) : Prop :=
  ∀ (d : ℤ) (x y : ℚ), Squarefree d → y≠0 → x≠5 → 30*(d:ℚ)*y^2=quintic x →
    (∀ i j k : Fin 6, i<j → j<k → (100*d.natAbs)^23<conductor i j k x.num x.den) →
    ratHeight x≤H*(d.natAbs:ℝ)^24

theorem twistBound_iff_large_triples (published : PublishedCorollary72)
    {H : ℝ} (margin : 10^54≤H) : TwistBound H ↔ LargeTriples H := by
  constructor
  · exact fun all d x y sf hy ex pt _ => all d x y sf hy ex pt
  · intro residual d x y sf hy ex pt
    by_cases large : ∀ i j k : Fin 6,i<j → j<k → (100*d.natAbs)^23<conductor i j k x.num x.den
    · exact residual d x y sf hy ex pt large
    push Not at large
    obtain ⟨i,j,k,ij,jk,small⟩ := large
    exact (chart_height published (Int.natAbs_pos.mpr sf.ne_zero) ij.ne (ij.trans jk).ne jk.ne
      (twist_rows sf.ne_zero hy pt) small).trans (mul_le_mul_of_nonneg_right margin (by positivity))

theorem sixContact_of_large_triples (published : PublishedCorollary72)
    (remaining : LargeTriples publicTwistConstant) : SixContactMin :=
  sixContactMin_of_twistBound ((twistBound_iff_large_triples published
    ((by norm_num : (10:ℝ)^54≤10^60).trans public_margin)).mpr remaining)

end ZInQBlueprint.SixUnitCharts
#print axioms ZInQBlueprint.SixUnitCharts.twist_rows
#print axioms ZInQBlueprint.SixUnitCharts.chart_estimate
#print axioms ZInQBlueprint.SixUnitCharts.chart_height
#print axioms ZInQBlueprint.SixUnitCharts.twistBound_iff_large_triples
#print axioms ZInQBlueprint.SixUnitCharts.sixContact_of_large_triples
