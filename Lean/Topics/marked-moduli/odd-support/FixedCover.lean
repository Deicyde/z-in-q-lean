import SignedKernel

/-! Explicit rational points on the quadratic twists of the fixed genus-two
cover and the inverse change of the marked parameter. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section

def quintic {K : Type*} [CommRing K] (x : K) : K := x*(x^2-1)*(x^2-9)

def X (u : ℚ) : ℚ := 5+120/u

theorem transform (u : ℚ) (hu : u ≠ 0) :
    quintic (X u) * u^6 = 1920*contactPoly u := by
  simp only [quintic,X,contactPoly]
  field_simp [hu]
  ring

theorem reconstruct {u : ℚ} (hu : u≠0) : X u ≠ 5 ∧ 120/(X u-5)=u := by
  have nz : (120:ℚ)/u ≠ 0 := div_ne_zero (by norm_num) hu
  unfold X
  constructor
  · intro e; apply nz; linarith
  · field_simp [hu]
    ring

/-- The ordinate is rational on the signed twist even when the primitive
sextic value, and hence d, is negative. -/
theorem twist_point {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e) :
    let Y : ℚ := 8*(e:ℚ)/(u.num:ℚ)^3
    30*(d:ℚ)*Y^2 = quintic (X u) ∧ Y ≠ 0 ∧ X u ≠ 5 ∧ 120/(X u-5)=u := by
  dsimp only
  have h0 : u ≠ 0 := fun he => hu (by simp [he,contactSet])
  have hn : (u.num:ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr h0
  have hb : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have he : (e:ℚ) ≠ 0 := by exact_mod_cast (Kernel_nonzero hu h).2
  have k : (d:ℚ)*(e:ℚ)^2=contactPoly u*(u.den:ℚ)^6 := by
    rw [← binary_identity]; exact_mod_cast h.2
  have q := transform u h0
  have n : (u.num:ℚ) = u*(u.den:ℚ) := (div_eq_iff hb).mp u.num_div_den
  refine ⟨?_,div_ne_zero (mul_ne_zero (by norm_num) he) (pow_ne_zero _ hn),reconstruct h0⟩
  rw [n]
  field_simp [h0,hb]
  linear_combination 1920*k-(u.den:ℚ)^6*q

/-- Every unmarked input supplies a rational point on a twist of one fixed
quintic. The twisting integer divides the genuine public conductor product. -/
theorem fixed_twist_reduction {u : ℚ} (hu : u ∉ contactSet) (S : Finset ℕ) :
    ∃ (d : ℤ) (x y : ℚ), Squarefree d ∧ d ≠ 0 ∧
      d.natAbs ∣ (∏ p ∈ S, p)*contactSupport S u ∧
      30*(d:ℚ)*y^2 = quintic x ∧ y≠0 ∧ x≠5 ∧ 120/(x-5)=u ∧
      (∀ p : ℕ, p.Prime → p ∉ S → 5<p → (p ∣ d.natAbs ↔ p ∣ contactSupport S u)) := by
  obtain ⟨d,e,k⟩ := exists_kernel u
  obtain ⟨point,hn,h5,inv⟩ := twist_point hu k
  exact ⟨d,X u,_,k.1,(Kernel_nonzero hu k).1,kernel_dvd hu k S,point,hn,h5,inv,
    fun p hp hS h5 => kernel_prime_iff hu k S hp hS h5⟩

#print axioms transform
#print axioms reconstruct
#print axioms twist_point
#print axioms fixed_twist_reduction
end
end ZInQBlueprint.OddSupport
