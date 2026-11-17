import DDMMCompletion
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The common affine open in the signed curve and the printed Baba--Granath
curve. Translating the two finite coordinates reduces the fractional linear
map to inversion of a Laurent variable. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.PrintedModel
open BinaryCover CurveChart SexticConjugation CoarseConic
noncomputable section
variable {K : Type} [Field K] [CharZero K]

def slope (u : ℚ) (d : K) := 4*(h u : K)*(2+d)
def factor (u : ℚ) (d : K) := (GlobalTwist.delta u : K)*((4*(2+d))⁻¹)^3
def argument (u : ℚ) (d : K) := d*(r u : K)
def changed (u : ℚ) (d : K) : K[X] :=
  binary (C (argument u d)) (C (slope u d) * (X + C (2*d))) X
def translated (u : ℚ) (d : K) : K[X] :=
  (SexticCalibration.sextic (argument u d)).comp (C (2*d*slope u d)*X + C (slope u d))

theorem units {u : ℚ} (hu : u ∉ ZInQ.contactSet) {d : K} (hd : d^2=6) :
    2*d*slope u d ≠ 0 ∧ factor u d ≠ 0 := by
  have hn : d ≠ 0 := by rintro rfl; norm_num at hd
  have hp : 2+d ≠ 0 := by
    intro e
    have : (2:K)=0 := by linear_combination (d-2)*e-hd
    norm_num at this
  have hh : (h u : K) ≠ 0 := by exact_mod_cast (radical_units hu).2
  have ht : (GlobalTwist.delta u : K) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  exact ⟨mul_ne_zero (mul_ne_zero (by norm_num) hn) (mul_ne_zero (mul_ne_zero (by norm_num) hh) hp),
    mul_ne_zero ht (pow_ne_zero _ (inv_ne_zero (mul_ne_zero (by norm_num) hp)))⟩

/-- On x=w+d the homogeneous base change becomes (b(w+2d),w).
The factor in the signed equation includes the prescribed squarefree twist. -/
theorem paper_translation (u : ℚ) {d : K} (hd : d^2=6) :
    algEquivAevalXAddC d (paper K u false) = C (factor u d)*changed u d := by
  apply Polynomial.funext
  intro w
  change ((paper K u false).comp (X+C d)).eval w = _
  rw [eval_comp]
  have he (v : K) : (paper K u false).eval v =
      (GlobalTwist.delta u : K)*evalAt (v,1) (paperSextic u) := by
    unfold paper evalAt
    simp only [Bool.false_eq_true, ite_false, eval_mul, eval_C]
    change _ * ((evalRingHom v).comp (MvPolynomial.eval₂Hom _ _)) _ = _ * _
    congr 1
    apply DFunLike.congr_fun (f := (evalRingHom v).comp (MvPolynomial.eval₂Hom _ _))
    apply MvPolynomial.ringHom_ext
    · intro x; simp
    · intro i; fin_cases i <;> simp
  rw [he, paperSextic_eval u d hd]
  simp only [factor, changed, slope, argument, binary, eval_mul, eval_sub, eval_neg, eval_add,
    eval_pow, eval_C, eval_X, eval_ofNat, mul_one]
  ring

theorem translated_formula (u : ℚ) (d : K) :
    translated u d = binary (C (argument u d)) (C (2*d*slope u d)*X+C (slope u d)) 1 := by
  apply Polynomial.funext
  intro x
  rw [translated, eval_comp]
  rw [← affine]
  simp [binary]

private theorem map_binary {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (s x z : R) :
    φ (binary s x z) = binary (φ s) (φ x) (φ z) := by simp [binary, map_ofNat]

private theorem homogeneous {R : Type*} [CommRing R] (s c x z : R) :
    binary s (c*x) (c*z) = c^6 * binary s x z := by unfold binary; ring

/-- On the common open put W=x−d and V=(X'−b)/(2db). Then WV=1.
The ordinate acquires precisely the factor W³. -/
theorem overlap (u : ℚ) (d : K) :
    SexticOverlap K (changed u d) (translated u d) := by
  rw [SexticOverlap, translated_formula]
  let L := LaurentPolynomial K
  let c : L := LaurentPolynomial.T (-1)
  let x : L := LaurentPolynomial.T 1
  let C' := LaurentPolynomial.C (R := K)
  have unit : c*x=1 := by
    change LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 = (1 : L)
    rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  have weight : (LaurentPolynomial.T (-3) : L)^2 = c^6 := by
    change (LaurentPolynomial.T (-3) : LaurentPolynomial K)^2 = (LaurentPolynomial.T (-1))^6
    rw [LaurentPolynomial.T_pow, LaurentPolynomial.T_pow]
    norm_num
  have base : C' (slope u d) * (c+C' (2*d)) =
      c * (C' (2*d*slope u d)*x + C' (slope u d)) := by
    calc _ = c * C' (slope u d) + (C' (2*d)*C' (slope u d))*(c*x) := by rw [unit]; ring
         _ = _ := by rw [show C' (2*d*slope u d) = C' (2*d)*C' (slope u d) from map_mul ..]; ring
  simp only [changed, map_binary, map_add, map_mul, map_one, toLaurent_C, toLaurent_X]
  change LaurentPolynomial.invert.toRingHom (binary _ _ _) = _
  rw [map_binary]
  have HC (a : K) : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.C a) =
      LaurentPolynomial.C a := LaurentPolynomial.invert_C a
  have HT : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.T 1 : L) = c :=
    LaurentPolynomial.invert_T 1
  simp only [map_mul, map_add, HC, HT]
  rw [weight, ← homogeneous, mul_one]
  simpa only [map_mul] using congrArg (fun z => binary (C' (argument u d)) z c) base

end
end ZInQBlueprint.PrintedModel
#print axioms ZInQBlueprint.PrintedModel.units
#print axioms ZInQBlueprint.PrintedModel.paper_translation
#print axioms ZInQBlueprint.PrintedModel.translated_formula
#print axioms ZInQBlueprint.PrintedModel.overlap
