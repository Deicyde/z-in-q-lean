import MarkDeterminant
import ProjectiveStabilizer

/-! All characteristic-zero projective symmetries of the literal rational binary sextic. -/
namespace ZInQBlueprint.MarkedForm
open CurveChart IntegralSextic SexticIgusaChart
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def paperForm (u : ℚ) (δ : K) (p : K×K) := δ*evalAt p (paperSextic u)

def paperScale (u : ℚ) (δ : K) :=
  δ*(yScale u:K)^2*(-6)*(homogeneousG u:K)*(left u:K)^2

theorem paper_formula {u : ℚ} (hu : u∉ZInQ.contactSet) (δ x z : K) :
    paperForm u δ (x,z)=paperScale u δ * form 1 (parameter u:K) x z := by
  rw [paperForm,paper_integral_polynomial,map_mul,map_pow,integral_eval]
  have yc : evalAt (x,z) (MvPolynomial.C (yScale u))=(yScale u:K) := by simp [evalAt]
  rw [yc]
  have hL : (left u:K)≠0 := by exact_mod_cast (parameters hu).1
  change δ*((yScale u:K)^2*(-6*(homogeneousG u:K)*
    form (left u:K) (right u:K) x z))=_
  simp only [parameter,Rat.cast_div,paperScale,form]
  field_simp [hL]

theorem paperScale_ne {u : ℚ} (hu : u∉ZInQ.contactSet) {δ : K} (hd : δ≠0) :
    paperScale u δ≠0 := by
  have h₁ : (yScale u:K)≠0 := by exact_mod_cast yScale_ne hu
  have h₂ : (homogeneousG u:K)≠0 := by exact_mod_cast (rational_parameters u).1
  have h₃ : (left u:K)≠0 := by exact_mod_cast (parameters hu).1
  unfold paperScale
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ h₁)) (by norm_num)) h₂)
    (pow_ne_zero _ h₃)

theorem paper_stabilizer [Infinite K] {u : ℚ} (hu : u∉ZInQ.contactSet) {δ : K} (hd : δ≠0)
    {a b c d μ : K} (hM : a*d-b*c≠0)
    (act : ∀ x z, paperForm u δ (a*x+b*z,c*x+d*z)=μ*paperForm u δ (x,z)) :
    b=0 ∧ c=0 ∧ a=d := by
  apply trivial_stabilizer (coeffs (parameter u:K)) (paper_det_ne (K:=K) u hu) hM
  intro x z
  rw [coeffs_eval,coeffs_eval]
  have eq := act x z
  simp only [paper_formula hu] at eq
  have sh := paperScale_ne hu hd
  have hc := (mul_left_cancel₀ sh)
    (show paperScale u δ*form 1 (parameter u:K) (a*x+b*z) (c*x+d*z)=
      paperScale u δ*(μ*form 1 (parameter u:K) x z) by linear_combination eq)
  rw [hc]; ring

/-- Both weighted coordinates share one scalar; the residual action on Y is a sign. -/
theorem paper_matrix_signs [Infinite K] {u : ℚ} (hu : u∉ZInQ.contactSet) {δ : K} (hd : δ≠0)
    {a b c d e : K} (hM : a*d-b*c≠0)
    (act : ∀ x z, paperForm u δ (a*x+b*z,c*x+d*z) = e^2*paperForm u δ (x,z)) :
    b=0 ∧ c=0 ∧ a=d ∧ a≠0 ∧ (e=a^3 ∨ e= -a^3) := by
  obtain ⟨hb,hc,hpair⟩ := paper_stabilizer hu hd hM act
  subst b; subst c; subst d
  have ha : a≠0 := by intro h; simp [h] at hM
  have h := act 1 0
  simp only [paper_formula hu,add_zero,mul_zero,mul_one] at h
  have sh := paperScale_ne hu hd
  have s : a^6=e^2 := by
    apply (mul_left_cancel₀ sh)
    simp [form,alpha,beta,gamma] at h
    linear_combination h
  have prod : (e-a^3)*(e+a^3)=0 := by linear_combination -s
  exact ⟨rfl,rfl,rfl,ha,(mul_eq_zero.mp prod).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left⟩

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.paper_formula
#print axioms ZInQBlueprint.MarkedForm.paper_stabilizer
#print axioms ZInQBlueprint.MarkedForm.paper_matrix_signs
