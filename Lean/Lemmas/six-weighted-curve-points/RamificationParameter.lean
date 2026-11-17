import SexticAffinePoints
import ValuationStalks
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! The ramification identity in the actual local ring at a branch point. -/
open Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
variable {K : Type} [Field K] (f : K[X])

def pointIdeal (p : AffineCoords K f) : Ideal (Cover f) := RingHom.ker (coordAlg K f p).toRingHom
instance (p : AffineCoords K f) : (pointIdeal f p).IsPrime :=
  RingHom.ker_isPrime _
abbrev pointLocal (p : AffineCoords K f) := Localization.AtPrime (pointIdeal f p)
abbrev localMap (p : AffineCoords K f) := algebraMap (Cover f) (pointLocal f p)

def branchCoords (x : K) (hx : f.IsRoot x) : AffineCoords K f :=
  ⟨(x,0),by simpa [Polynomial.aeval_def] using hx.symm⟩

theorem local_factor_unit (p : AffineCoords K f) (r : K[X]) (hn : r.eval p.val.1 ≠ 0) :
    IsUnit (localMap f p (algebraMap K[X] (Cover f) r)) := by
  apply IsLocalization.map_units (M := (pointIdeal f p).primeCompl) (pointLocal f p)
    ⟨algebraMap K[X] (Cover f) r, ?_⟩
  change (aeval p.val.1) r + (aeval p.val.1) 0 * p.val.2 ≠ 0
  simpa [aeval_def] using hn

/-- At a simple zero, the base parameter is the square of the curve ordinate
times a unit in the local ring at (x,0). -/
theorem branch_local_parameter (hf : f.Separable) (x : K) (hx : f.IsRoot x) :
    let p := branchCoords f x hx
    ∃ e : (pointLocal f p)ˣ,
      localMap f p (algebraMap K[X] (Cover f) (X - C x)) =
        (e : pointLocal f p) * (localMap f p QuadraticAlgebra.omega)^2 := by
  let p := branchCoords f x hx
  obtain ⟨q,hq⟩ := (Polynomial.dvd_iff_isRoot).mpr hx
  have hder : f.derivative.eval x ≠ 0 := by
    have := Polynomial.aeval_ne_zero_of_isCoprime hf x
    simpa [aeval_def, hx.eq_zero] using this
  have hqx : q.eval x ≠ 0 := by
    have hd := congrArg (fun t : K[X] => t.derivative.eval x) hq
    have eq : f.derivative.eval x = q.eval x := by simpa using hd
    rwa [←eq]
  let A := algebraMap K[X] (Cover f)
  let J := localMap f p
  have hJ : IsUnit (J (A q)) := local_factor_unit f p q hqx
  have hw : (QuadraticAlgebra.omega : Cover f)^2 = A f := by
    rw [QuadraticAlgebra.omega_pow_two_eq_add,zero_smul,add_zero,←Algebra.algebraMap_eq_smul_one]
  have hr : (J QuadraticAlgebra.omega)^2 = J (A (X-C x))*J (A q) := by
    rw [←map_pow,hw]
    exact (congrArg (fun t => J (A t)) hq).trans (by rw [map_mul,map_mul])
  refine ⟨hJ.unit⁻¹,?_⟩
  change J (A (X-C x)) = _ * (J QuadraticAlgebra.omega)^2
  have unit_eq : (↑hJ.unit⁻¹ : pointLocal f p) * J (A q) = 1 :=
    (congrArg (fun t => (↑hJ.unit⁻¹ : pointLocal f p) * t) hJ.unit_spec.symm).trans (Units.inv_mul hJ.unit)
  rw [hr,mul_left_comm,unit_eq,mul_one]

theorem paper_branch_local_parameter [CharZero K] {u : ℚ} (hu : u∉ZInQ.contactSet)
    (i : Bool) (x : K) (hx : (paper K u i).IsRoot x) :
    let f := paper K u i
    let p := branchCoords f x hx
    ∃ e : (pointLocal f p)ˣ,
      localMap f p (algebraMap K[X] (Cover f) (X - C x)) =
        (e : pointLocal f p) * (localMap f p QuadraticAlgebra.omega)^2 :=
  branch_local_parameter _ (paper_chart_regular K hu i).2 x hx
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.local_factor_unit
#print axioms ZInQBlueprint.WeightedCurvePoints.branch_local_parameter
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_branch_local_parameter
