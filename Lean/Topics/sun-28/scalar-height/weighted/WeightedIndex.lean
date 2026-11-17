import TreeDepth
import CommonScalarChart

open NumberField IsDedekindDomain Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary
open scoped NumberField
namespace Sun28.ScalarDepth
open Sun28.ScalarHeight
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- At every positive odd scalar contact its full order enters the elliptic index. -/
theorem weighted_order_at_prime {p : ℕ} [Fact p.Prime] (big : 65<p) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (chart : OrdinaryFormalChart p w)
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D : ℕ) (M : Finset ℚ)
    (positive : 0<padicValRat p r) (odd : Odd (padicValRat p r)) (gn : Γ≠0)
    (gu : padicValRat p Γ=0) (multipliers : ∀ μ∈M,padicValRat p μ=0)
    (certificate : TreeCertificate root h s r Γ D M) : (p:ℤ)^(47*(padicValRat p r).toNat+1) ∣ s-1 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name (by omega)
  let u := discreteOrder (w.valuation K)
  let t := u.comap (algebraMap ℚ K)
  have base {q : ℚ} (nz : q≠0) : t q=((padicValRat p q:ℤ):WithTop ℤ) := by
    change u (algebraMap ℚ K q)=_
    simpa [u,name,unram] using prime_order_rat v w nz
  obtain ⟨δ,g,sgn,c,live,accept⟩ := certificate
  have depth := pole_tree_bound (by omega) M multipliers t base D sgn positive odd gn gu live accept
  have rn : r≠0 := by rintro rfl; simp at positive
  obtain ⟨a,b,e,f⟩ := weighted_tree t g (base rn) positive odd depth
  have two : u (2:K)=0 := by
    have nd : ¬p∣2 := fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) (by omega)
    have ht : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd] using (padicValRat.of_nat (p:=p) (n:=2))
    have e : u (algebraMap ℚ K 2)=((padicValRat p 2:ℤ):WithTop ℤ) := base (q:=2) (by norm_num)
    simpa [ht,map_ofNat] using e
  have rhon : ρ≠0 := by rintro rfl; norm_num at root
  obtain ⟨i,vi⟩ := finite_order u rhon
  have eq := congrArg u root
  rw [u.map_pow,vi,two] at eq
  have twice : 2*i=0 := by exact_mod_cast eq
  have ru : u ρ=0 := by rw [vi,show i=0 by omega];rfl
  have linear {a b : ℚ} {k : WithTop ℤ} (l : k≤t a) (r' : k≤t b) : k≤u (pair ρ a b) := by
    apply u.map_le_add l
    rw [u.map_mul,ru,zero_add]
    exact r'
  have compare := formalComparison_at_prime (p:=p) (by omega) w root 1
    (completedFilteredLog_of_goodModel (by omega) (by omega) w root (goodModel_of_ordinary_chart big w root chart) 1)
    (paperGenerator root)
  have infinite (j : ℤ) (hj : j≠0) : j • paperGenerator root≠0 := by
    intro z
    have dvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr z
    rw [paperGenerator_infinite root] at dvd
    simp [hj] at dvd
  by_cases hs : s-1=0
  · rw [hs]; exact dvd_zero _
  apply scalar_index_dvd (p:=p) (by omega) u (paper_coefficient u root two) two
    (paperGenerator root) compare hs hh (cyclic_middle_nonzero _ infinite hh).1
    (cyclic_middle_nonzero _ infinite hs).2
  · rw [c.first]; exact linear a b
  · rw [c.quotient]
    have order : ((47*(padicValRat p r).toNat+1:ℕ):WithTop ℤ)=
        ((47*padicValRat p r+1:ℤ):WithTop ℤ) := by
      have e0 : ((47*(padicValRat p r).toNat+1:ℕ):ℤ) = 47*padicValRat p r+1 := by
        push_cast
        rw [Int.toNat_of_nonneg positive.le]
      change ((((47*(padicValRat p r).toNat+1:ℕ):ℤ):WithTop ℤ))=_
      rw [e0]
    rw [order]
    exact linear e f

end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.weighted_order_at_prime
