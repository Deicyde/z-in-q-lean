import PrintedSexticOpen
import ProjectiveSextic

/-! The affine polynomial printed in Baba--Granath, Theorem 3.14, is a
separable sextic on every rational specialization outside the contact set. -/
open Polynomial
namespace ZInQBlueprint.PrintedModel
open BinaryCover SexticEmbedding CoarseConic
noncomputable section
variable {K : Type} [Field K] [CharZero K] {u : ℚ} {d : K}

private theorem leading_ne (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) : -4+3*argument u d ≠ 0 := by
  have nr := (radical_units hu).1
  intro eq
  have e : ((4 / (3*r u) : ℚ) : K) = d := by
    push_cast
    apply (div_eq_iff (mul_ne_zero (by norm_num) (by exact_mod_cast nr))).mpr
    dsimp [argument] at eq
    linear_combination -eq
  have h : (4/(3*r u) : ℚ)^2 = 6 := by
    exact_mod_cast (show ((4 / (3*r u) : ℚ) : K)^2 = 6 by rw [e,hd])
  have sq6 : IsSquare (6:ℚ) := ⟨_,by simpa only [sq] using h.symm⟩
  change IsSquare ((6:ℕ):ℚ) at sq6
  rw [Rat.isSquare_natCast_iff] at sq6
  rcases sq6 with ⟨w,hw⟩
  by_cases l : w≤2
  · nlinarith [Nat.mul_le_mul l l]
  · have g : 3≤w := by omega
    nlinarith [Nat.mul_le_mul g g]

theorem printed_degree (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    (SexticCalibration.sextic (argument u d)).natDegree = 6 := by
  have bound (a b c e f g h : K) :
      (C a*X^6+C b*X^5+C c*X^4-C e*X^3+C f*X^2+C g*X-C h).natDegree ≤ 6 := by
    compute_degree!
  have top (a b c e f g h : K) :
      (C a*X^6+C b*X^5+C c*X^4-C e*X^3+C f*X^2+C g*X-C h).coeff 6 = a := by
    simp [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]
  apply natDegree_eq_of_le_of_coeff_ne_zero (bound ..)
  exact ((top ..).symm ▸ (leading_ne hu hd))

theorem changed_regular (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    (changed u d).natDegree=6 ∧ (changed u d).Separable := by
  have eq := paper_translation u hd
  have hn := (units hu hd).2
  have degree := congrArg natDegree eq
  rw [natDegree_algEquiv, paper_degree_six hu false, natDegree_C_mul hn] at degree
  obtain ⟨pos,sep⟩ := paper_chart_regular K hu false
  have hs := (regular_image (algEquivAevalXAddC d) pos sep).2
  rw [eq] at hs
  exact ⟨degree.symm, (associated_unit_mul_left _ (C (factor u d)) (isUnit_C.mpr hn.isUnit)).separable hs⟩

theorem translated_eq_reverse (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    translated u d = (changed u d).reverse := by
  have e₁ := overlap u d
  have e₂ := reverse_sextic_overlap (changed_regular hu hd).1
  unfold SexticOverlap at e₁ e₂
  apply Polynomial.toLaurent_injective
  exact (IsUnit.mul_right_inj ((LaurentPolynomial.isUnit_T (-3) (R := K)).pow 2)).mp (e₁.symm.trans e₂)

/-- Separability comes from reversal of a squarefree polynomial and an affine
change of variable. It requires no second discriminant calculation. -/
theorem printed_separable (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    (SexticCalibration.sextic (argument u d)).Separable := by
  let : Invertible (2*d*slope u d) := invertibleOfNonzero (units hu hd).1
  let e := algEquivCMulXAddC (2*d*slope u d) (slope u d)
  have he : e (SexticCalibration.sextic (argument u d)) = translated u d := rfl
  have ⟨hdeg,hs⟩ := changed_regular hu hd
  obtain ⟨⟨h5,_⟩,sep⟩ := reverse_sextic_regular hdeg hs
  rw [← translated_eq_reverse hu hd, ← he] at h5 sep
  simpa only [AlgEquiv.symm_apply_apply] using (regular_image e.symm (by omega) sep).2

end
end ZInQBlueprint.PrintedModel
#print axioms ZInQBlueprint.PrintedModel.printed_degree
#print axioms ZInQBlueprint.PrintedModel.changed_regular
#print axioms ZInQBlueprint.PrintedModel.translated_eq_reverse
#print axioms ZInQBlueprint.PrintedModel.printed_separable
