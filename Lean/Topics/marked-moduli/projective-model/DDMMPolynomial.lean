import ValuationStalks
import Mathlib.Algebra.Polynomial.Mirror

/-! The ordinary affine DDMM sextic and its reciprocal at infinity, with no reduction hypotheses. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
open DirectCharts LeadingOrders GlobalTwist GoodReductionCharts
noncomputable section

/-- Rescaling by a nonzero scalar in the equation preserves regularity of its radicand. -/
private theorem regular_scale {K : Type*} [Field K] {a : K} (ha : a ≠ 0) {f : K[X]} :
    (0 < (C a*f).natDegree ∧ (C a*f).Separable) ↔ (0 < f.natDegree ∧ f.Separable) := by
  have h := associated_unit_mul_left f (C a) (isUnit_C.mpr ha.isUnit)
  rw [natDegree_C_mul ha]
  exact and_congr_right fun _ => ⟨h.separable,h.symm.separable⟩

private theorem fixed_regular {K : Type} [Field K] [CharZero K] {u : ℚ} (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    0 < (fixed K u i).natDegree ∧ (fixed K u i).Separable := by
  have h := paper_chart_regular K hu i
  rw [paper_eq,← map_pow] at h
  exact (regular_scale (pow_ne_zero 2 (by exact_mod_cast CurveChart.yScale_ne hu))).mp h

/-- Every admissible local equation has degree six and is separable over the base Q_p. -/
theorem ddmm_sextic_regular {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    (GoodReductionCharts.polynomial p u v a t).natDegree = 6 ∧
    (GoodReductionCharts.polynomial p u v a t).Separable := by
  let f := GoodReductionCharts.polynomial p u v a t
  have H : 0 < f.natDegree ∧ f.Separable := by
    rcases local_chart_equations p u v a t hc with h | h
    · change f = _ at h
      rw [h]
      exact fixed_regular (K := ℚ_[p]) hu false
    · let e := dilate (sixUnit p)
      change e f = _ at h
      have hs : 0 < (e f).natDegree ∧ (e f).Separable := by
        rw [h,← map_pow]
        exact (regular_scale (by norm_num : (6:ℚ_[p])^6 ≠ 0)).mpr (fixed_regular hu true)
      simpa only [AlgEquiv.symm_apply_apply] using regular_image e.symm hs.1 hs.2
  let ι := algebraMap ℤ_[p] ℚ_[p]
  let s : ℤ_[p] := -6*(delta u : ℤ_[p])*(RationalClusters.G p u)*(v : ℤ_[p])*(a : ℤ_[p])^2
  have he : f = C (ι s) * monicSextic (ι t) := by
    change (C s * monicSextic t).map ι = _
    simp only [Polynomial.map_mul,map_C,monic_coeffs,Polynomial.map_add,Polynomial.map_X,Polynomial.map_pow]
    simp [map_ofNat]
  have hs : ι s ≠ 0 := by
    intro hz
    have h0 : f = 0 := by rw [he,hz,map_zero,zero_mul]
    simp [h0] at H
  refine ⟨?_,H.2⟩
  change f.natDegree = 6
  rw [he,natDegree_C_mul hs,(monic_six _).2]

section Reverse
variable {K : Type} [Field K] {f : K[X]}

private def mirrorEquiv : K[X] ≃* K[X] where
  toFun := Polynomial.mirror
  invFun := Polynomial.mirror
  left_inv := mirror_mirror
  right_inv := mirror_mirror
  map_mul' := fun x y => mirror_mul_of_domain x y

/-- Reversal discards a power of X and preserves squarefreeness. -/
theorem squarefree_reverse (hf : Squarefree f) : Squarefree f.reverse := by
  let e := mirrorEquiv (K := K)
  have hm : Squarefree (e f) := by
    intro x hx
    have h' : e.symm x * e.symm x ∣ f := by simpa only [map_mul,MulEquiv.symm_apply_apply] using map_dvd e.symm hx
    exact (isUnit_map_iff e.symm x).mp (hf _ h')
  change Squarefree (f.reverse * X^f.natTrailingDegree) at hm
  exact hm.squarefree_of_dvd (dvd_mul_right f.reverse (X ^ f.natTrailingDegree))

/-- For a squarefree sextic, the reversed polynomial has degree five or six and is separable. -/
theorem reverse_sextic_regular [CharZero K] (hd : f.natDegree = 6) (hs : f.Separable) :
    (5 ≤ f.reverse.natDegree ∧ f.reverse.natDegree ≤ 6) ∧ f.reverse.Separable := by
  have ht : f.natTrailingDegree ≤ 1 := by
    by_contra! h
    have hx : (X : K[X])^2 ∣ f := X_pow_dvd_iff.mpr fun n hn =>
      coeff_eq_zero_of_lt_natTrailingDegree (by omega)
    exact not_isUnit_X (hs.squarefree X (by simpa only [sq] using hx))
  refine ⟨?_,PerfectField.separable_iff_squarefree.mpr (squarefree_reverse hs.squarefree)⟩
  rw [reverse_natDegree,hd]
  omega

/-- The two literal sextic charts glue by x=1/z, y=w/z³. -/
theorem reverse_sextic_overlap (hd : f.natDegree = 6) : SexticOverlap K f f.reverse := by
  unfold SexticOverlap
  rw [LaurentPolynomial.toLaurent_reverse,hd]
  ring_nf
  simp only [LaurentPolynomial.T_pow]
  norm_num

end Reverse
end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.ddmm_sextic_regular
#print axioms ZInQBlueprint.BinaryCover.squarefree_reverse
#print axioms ZInQBlueprint.BinaryCover.reverse_sextic_regular
#print axioms ZInQBlueprint.BinaryCover.reverse_sextic_overlap
