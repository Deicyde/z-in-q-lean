import RamifiedMaximal

/-! Away from Y=0 the base parameter itself generates the maximal ideal.
The reciprocal chart proves this also over the point at infinity. -/
open Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
variable {K : Type} [Field K] (f : K[X]) (p : AffineCoords K f)

private abbrev A := algebraMap K[X] (Cover f)

theorem pointIdeal_pair :
    pointIdeal f p = Ideal.span {A f (X-C p.1.1), QuadraticAlgebra.omega - A f (C p.1.2)} := by
  apply le_antisymm
  · intro z hz
    have he : (z.re + C p.val.2 * z.im).IsRoot p.val.1 := by
      change (aeval p.val.1) z.re + (aeval p.val.1) z.im*p.val.2 = 0 at hz
      simpa [Polynomial.IsRoot,aeval_def,mul_comm] using hz
    obtain ⟨q,hq⟩ := (Polynomial.dvd_iff_isRoot).mpr he
    apply Ideal.mem_span_pair.mpr
    refine ⟨A f q,A f z.im,?_⟩
    rw [←map_mul,mul_comm q,←hq,mul_sub,←map_mul]
    have reim := QuadraticAlgebra.re_smul_add_im_smul z
    simp only [Algebra.smul_def,mul_one] at reim
    rw [map_add,mul_comm (C p.1.2)]
    refine Eq.trans ?_ reim
    abel
  · apply Ideal.span_le.mpr
    intro v hv
    rcases hv with h | h
    · subst v
      change (aeval p.1.1) (X-C p.1.1) + (aeval p.1.1) 0 * p.1.2 = 0
      simp
    · have e : v = QuadraticAlgebra.omega - A f (C p.1.2) := h
      subst v
      change coordAlg K f p (_ - _) = 0
      rw [map_sub]
      change ((aeval p.1.1) 0 + (aeval p.1.1) 1*p.1.2) -
        ((aeval p.1.1) (C p.1.2) + (aeval p.1.1) 0*p.1.2) = 0
      simp

theorem regular_local_parameter [CharZero K] (hn : p.1.2 ≠ 0) :
    let J := localMap f p
    Ideal.span {J (A f (X-C p.1.1))} = IsLocalRing.maximalIdeal (pointLocal f p) := by
  let J := localMap f p
  let W : Cover f := QuadraticAlgebra.omega
  let D := A f (C p.1.2)
  have H : (pointIdeal f p).map J = Ideal.span {J (A f (X-C p.1.1)), J (W-D)} := by
    have hh := congrArg (Ideal.map J) (pointIdeal_pair f p)
    simpa [Ideal.map_span,W,D] using hh
  change Ideal.span {J (A f (X-C p.1.1))} = _
  rw [←Localization.AtPrime.map_eq_maximalIdeal (I:=pointIdeal f p),H]
  symm
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  have hU : IsUnit (J (W+D)) := by
    apply IsLocalization.map_units (M := (pointIdeal f p).primeCompl) (pointLocal f p) ⟨W+D,?_⟩
    change coordAlg K f p (W+D) ≠ 0
    rw [map_add]
    change ((aeval p.1.1) 0 + (aeval p.1.1) 1*p.1.2) +
      ((aeval p.1.1) (C p.1.2) + (aeval p.1.1) 0*p.1.2) ≠ 0
    simpa [←two_mul] using mul_ne_zero (by norm_num : (2:K)≠0) hn
  have he : (f - C (p.1.2^2)).IsRoot p.1.1 := by
    simpa [Polynomial.IsRoot,aeval_def] using sub_eq_zero.mpr p.2.symm
  obtain ⟨q,hq⟩ := (Polynomial.dvd_iff_isRoot).mpr he
  have hw : W^2 = A f f := by
    change (QuadraticAlgebra.omega : Cover f)^2 = A f f
    rw [QuadraticAlgebra.omega_pow_two_eq_add,zero_smul,add_zero,←Algebra.algebraMap_eq_smul_one]
  have hf : (W-D)*(W+D)=A f ((X-C p.1.1)*q) := by
    rw [← hq,map_sub]
    calc
      _ = W^2-D^2 := by ring
      _ = _ := by rw [hw]; simp [D,A]
  have hd : J (A f (X - C p.1.1)) ∣ J (W-D) * J (W+D) :=
    ⟨J (A f q), by rw [←map_mul,hf,map_mul,map_mul]⟩
  exact (IsUnit.dvd_mul_right hU).mp hd

theorem paper_regular_local_parameter [CharZero K] (u : ℚ) (i : Bool)
    (p : AffineCoords K (paper K u i)) (hn : p.1.2≠0) :
    Ideal.span {localMap _ p (algebraMap K[X] (Cover (paper K u i)) (X-C p.1.1))} =
      IsLocalRing.maximalIdeal (pointLocal _ p) := regular_local_parameter _ p hn
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.pointIdeal_pair
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_regular_local_parameter
