import RamificationParameter

/-! The pullback of a base uniformizer at a simple branch root generates the
square of the maximal ideal in the actual affine local ring. -/
open Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
variable {K : Type} [Field K] (f : K[X])

theorem branch_pointIdeal (x : K) (hx : f.IsRoot x) :
    pointIdeal f (branchCoords f x hx) =
      Ideal.span {algebraMap K[X] (Cover f) (X-C x), QuadraticAlgebra.omega} := by
  apply le_antisymm
  · intro z hz
    have he : z.re.IsRoot x := by
      change (aeval x) z.re + (aeval x) z.im * 0 = 0 at hz
      simpa [aeval_def,Polynomial.IsRoot] using hz
    obtain ⟨q,hq⟩ := (Polynomial.dvd_iff_isRoot).mpr he
    apply Ideal.mem_span_pair.mpr
    refine ⟨algebraMap _ _ q,algebraMap _ _ z.im,?_⟩
    rw [←map_mul,mul_comm q,←hq]
    simpa only [Algebra.smul_def,mul_one] using QuadraticAlgebra.re_smul_add_im_smul z
  · apply Ideal.span_le.mpr
    intro v hv
    rcases hv with h | h
    · subst v
      change (aeval x) (X-C x) + (aeval x) 0 * 0 = 0
      simp
    · have h' : v = QuadraticAlgebra.omega := h
      subst v
      change (aeval x) 0 + (aeval x) 1 * 0 = 0
      simp

theorem branch_maximal (hf : f.Separable) (x : K) (hx : f.IsRoot x) :
    let p := branchCoords f x hx
    IsLocalRing.maximalIdeal (pointLocal f p) =
      Ideal.span {localMap f p QuadraticAlgebra.omega} := by
  let p := branchCoords f x hx
  let J := localMap f p
  obtain ⟨e,he⟩ := branch_local_parameter f hf x hx
  have H : (pointIdeal f p).map J =
      Ideal.span {J (algebraMap K[X] (Cover f) (X-C x)), J QuadraticAlgebra.omega} := by
    have hh := congrArg (Ideal.map J) (branch_pointIdeal f x hx)
    simpa [Ideal.map_span] using hh
  change IsLocalRing.maximalIdeal (pointLocal f p) = Ideal.span {J QuadraticAlgebra.omega}
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I:=pointIdeal f p), H]
  apply Ideal.span_pair_eq_span_right_iff_dvd.mpr
  exact ⟨(e : pointLocal f p)*J QuadraticAlgebra.omega, by rw [he]; ring⟩

theorem paper_ramification_two [CharZero K] {u : ℚ} (hu : u∉ZInQ.contactSet)
    (i : Bool) (x : K) (hx : (paper K u i).IsRoot x) :
    let f := paper K u i
    let p := branchCoords f x hx
    Ideal.span {localMap f p (algebraMap K[X] (Cover f) (X-C x))} =
      (IsLocalRing.maximalIdeal (pointLocal f p)) ^ 2 := by
  let f := paper K u i
  let p := branchCoords f x hx
  have hs := (paper_chart_regular K hu i).2
  obtain ⟨e,he⟩ := branch_local_parameter f hs x hx
  change Ideal.span {localMap f p (algebraMap K[X] (Cover f) (X-C x))} =
      (IsLocalRing.maximalIdeal (pointLocal f p))^2
  rw [branch_maximal f hs x hx, Ideal.span_singleton_pow,he,Ideal.span_singleton_mul_left_unit e.isUnit]
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.branch_pointIdeal
#print axioms ZInQBlueprint.WeightedCurvePoints.branch_maximal
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_ramification_two
