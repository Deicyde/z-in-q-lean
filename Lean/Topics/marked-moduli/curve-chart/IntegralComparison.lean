import LocalChanges
import IntegralSextic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Real.Sqrt

/-! Equality of the rational coefficient polynomials of the normalized
Baba–Granath pullback and the three-term integral equation. -/
noncomputable section
namespace ZInQBlueprint.CurveChart
open IntegralSextic ResidualFactors CoarseConic SixContact

def homogeneousG (u : ℚ) : ℚ := poleForm (u.num:ℚ) (u.den:ℚ)
def yScale (u : ℚ) := 768*(h u)^3/(homogeneousG u)^2

def integralPolynomial (u : ℚ) : Pol :=
  integralEquation 1 (MvPolynomial.C (u.num:ℚ)) (MvPolynomial.C (u.den:ℚ))
    (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem rational_parameters (u : ℚ) :
    homogeneousG u ≠ 0 ∧
    (homogeneousG u)^3*r u = 240*contactProduct (u.num:ℚ) (u.den:ℚ) ∧
    (homogeneousG u)^3*h u = hForm (u.num:ℚ) (u.den:ℚ) := by
  have hb : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have rat : (u.num:ℚ)/(u.den:ℚ) = u := Rat.num_div_den u
  obtain ⟨hf,hg⟩ := ClusterParameters.homogenize (u.num:ℚ) (u.den:ℚ) hb
  rw [rat] at hf hg
  have hp : homogeneousG u ≠ 0 := by
    rw [homogeneousG, ← hg]
    exact mul_ne_zero (positive_denominator u).ne' (pow_ne_zero _ hb)
  have hH (A B : ℚ) (hb : B ≠ 0) : H (A/B)*B^6 = hForm A B := by
    unfold H hForm
    field_simp
  have hz := hH (u.num:ℚ) (u.den:ℚ) hb
  rw [rat] at hz
  refine ⟨hp,?_,?_⟩
  · rw [homogeneousG,← hg,← hf,CoarseConic.r]
    field_simp [(positive_denominator u).ne']
  · rw [homogeneousG,← hg,← hz,CoarseConic.h]
    field_simp [(positive_denominator u).ne']

theorem yScale_ne {u : ℚ} (hu : u ∉ ZInQ.contactSet) : yScale u ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (radical_units hu).2))
    (pow_ne_zero _ (rational_parameters u).1)

variable {K : Type*} [Field K] [CharZero K]

theorem integral_eval (u : ℚ) (v : K × K) : evalAt v (integralPolynomial u) =
    (-6:K)*(homogeneousG u:K)*
      form ((m (u.num:ℚ) (u.den:ℚ):ℚ):K) ((n (u.num:ℚ) (u.den:ℚ):ℚ):K) v.1 v.2 := by
  have hi : MvPolynomial.eval₂ (Rat.castHom K) ![v.1,v.2] (u.num : Pol) = (u.num:K) :=
    map_intCast (evalAt v) u.num
  simp [integralPolynomial,integralEquation,evalAt,homogeneousG,form,alpha,beta,gamma,m,n,
    poleForm,hi]

private theorem lifted_clear (u : ℚ) (d : K) (hd : d^2=6) (v : K × K) :
    (homogeneousG u:K)^3 * evalAt v (RationalModel.rationalSextic u) =
    2^25*54*(h u:K)^6*form ((m (u.num:ℚ) (u.den:ℚ):ℚ):K) ((n (u.num:ℚ) (u.den:ℚ):ℚ):K) v.1 v.2 := by
  obtain ⟨_,hr,hh⟩ := rational_parameters u
  have hr' : (poleForm (u.num:K) (u.den:K))^3*(r u:K)=240*contactProduct (u.num:K) (u.den:K) := by
    unfold homogeneousG poleForm contactProduct at hr
    unfold poleForm contactProduct
    exact_mod_cast hr
  have hh' : (poleForm (u.num:K) (u.den:K))^3*(h u:K)=hForm (u.num:K) (u.den:K) := by
    unfold homogeneousG poleForm hForm at hh
    unfold poleForm hForm
    exact_mod_cast hh
  rw [rationalSextic_eval u d hd]
  have he := cleared hd (sextic_parameters u hd).2 hr' hh' v.1 v.2
  simpa [homogeneousG,poleForm,m,n] using he

theorem normalized_eval (u : ℚ) (d : K) (hd : d^2=6) (v : K × K) :
    evalAt v (paperSextic u) = (yScale u:K)^2*evalAt v (integralPolynomial u) := by
  have hG : (homogeneousG u:K) ≠ 0 := by exact_mod_cast (rational_parameters u).1
  have he := lifted_clear u d hd v
  have hnorm : evalAt v (MvPolynomial.C (-1/512 : ℚ)) = (-1/512:K) := by
    simp [evalAt]
  rw [paperSextic,map_mul,hnorm,integral_eval]
  simp only [yScale,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  field_simp [hG]
  linear_combination -he

/-- Literal equality of rational coefficient polynomials at the numerator and
denominator of u, before any choice of a field containing √6. -/
theorem paper_integral_polynomial (u : ℚ) :
    paperSextic u = (MvPolynomial.C (yScale u))^2*integralPolynomial u := by
  apply MvPolynomial.map_injective (Rat.castHom ℝ) (Rat.castHom ℝ).injective
  apply MvPolynomial.funext
  intro z
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  let v : ℝ × ℝ := (z 0,z 1)
  have hz : z = ![v.1,v.2] := by funext i; fin_cases i <;> rfl
  rw [hz]
  change evalAt v (paperSextic u) = evalAt v ((MvPolynomial.C (yScale u))^2*integralPolynomial u)
  rw [map_mul,map_pow,show evalAt v (MvPolynomial.C (yScale u)) = (yScale u:ℝ) by simp [evalAt]]
  exact normalized_eval u (Real.sqrt 6) (Real.sq_sqrt (by norm_num)) v

/-- An equivalence defined over Q itself and over every characteristic-zero field.
The base point is fixed and only its Y-coordinate is rescaled. -/
def paper_integral_equiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) :
    Points (fun v : K × K => (δ:K)*evalAt v (integralPolynomial u)) ≃
    Points (fun v : K × K => (δ:K)*evalAt v (paperSextic u)) := by
  have hn : (yScale u:K) ≠ 0 := by exact_mod_cast yScale_ne hu
  apply coordinateEquiv (LinearEquiv.refl K _) (Units.mk0 (yScale u:K) hn)
  intro v
  simp only [LinearEquiv.refl_apply]
  rw [paper_integral_polynomial,map_mul,map_pow]
  change (δ:K)*(evalAt v (MvPolynomial.C (yScale u))^2*_) = (yScale u:K)^2*((δ:K)*_)
  rw [show evalAt v (MvPolynomial.C (yScale u)) = (yScale u:K) by simp [evalAt]]
  ring

end ZInQBlueprint.CurveChart
#print axioms ZInQBlueprint.CurveChart.rational_parameters
#print axioms ZInQBlueprint.CurveChart.yScale_ne
#print axioms ZInQBlueprint.CurveChart.integral_eval
#print axioms ZInQBlueprint.CurveChart.normalized_eval
#print axioms ZInQBlueprint.CurveChart.paper_integral_polynomial
#print axioms ZInQBlueprint.CurveChart.paper_integral_equiv
