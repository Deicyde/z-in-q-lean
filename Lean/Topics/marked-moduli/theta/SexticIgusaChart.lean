import IntegralComparison

/-! Specialization of the two-variable Igusa calculation to every unmarked
rational input, for every nonzero scalar twist of the integral sextic. -/
namespace ZInQBlueprint.SexticIgusaChart
open IntegralSextic CoarseConic CurveChart SixContact
noncomputable section

def left (u : ℚ) := m (u.num:ℚ) (u.den:ℚ)
def right (u : ℚ) := n (u.num:ℚ) (u.den:ℚ)
def parameter (u : ℚ) := right u / left u
def scalar (u δ : ℚ) := -6 * δ * homogeneousG u * (left u)^2

theorem parameters {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    left u ≠ 0 ∧ right u ≠ 0 ∧ (homogeneousG u)^3 = 27*(left u)^2 + (right u)^2 ∧
      (homogeneousG u)^3 * r u = 8*left u*right u := by
  obtain ⟨hG,hr,_⟩ := rational_parameters u
  obtain ⟨hp,hg,_⟩ := parameter_identities (u.num:ℚ) (u.den:ℚ)
  have h : (homogeneousG u)^3 * r u = 8*left u*right u := by
    unfold left right
    linear_combination hr - 8*hp
  have hnon := mul_ne_zero (pow_ne_zero 3 hG) (radical_units hu).1
  rw [h] at hnon
  exact ⟨fun he => hnon (by rw [he]; ring),fun he => hnon (by rw [he]; ring),hg,h⟩

theorem unmarked {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) :
    parameter u ≠ 0 ∧ scalar u δ ≠ 0 ∧ (parameter u)^2+27 ≠ 0 ∧
      J u = -64*(parameter u)^2 / ((parameter u)^2+27)^2 := by
  obtain ⟨hm,hn,hg,hr⟩ := parameters hu
  have ht := div_ne_zero hn hm
  have hd : 0 < (parameter u)^2+27 := by linarith [sq_nonneg (parameter u)]
  have hscale : scalar u δ ≠ 0 := by
    unfold scalar
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hδ) (rational_parameters u).1)
      (pow_ne_zero _ hm)
  refine ⟨ht,hscale,hd.ne',?_⟩
  have hden : (parameter u)^2+27 = (homogeneousG u)^3/(left u)^2 := by
    unfold parameter
    field_simp [hm]
    linarith
  have hr' : r u = 8*left u*right u/(homogeneousG u)^3 :=
    (eq_div_iff (pow_ne_zero _ (rational_parameters u).1)).2 (by linarith)
  rw [first_square,hr',hden]
  unfold parameter
  field_simp [hm,(rational_parameters u).1]
  ring

theorem equation {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ x z : ℚ) :
    integralEquation δ (u.num:ℚ) (u.den:ℚ) x z =
      scalar u δ * form 1 (parameter u) x z := by
  obtain ⟨hm,_,_,_⟩ := parameters hu
  change -6*δ*homogeneousG u * form (left u) (right u) x z = _
  unfold scalar form parameter
  field_simp [hm]

end
end ZInQBlueprint.SexticIgusaChart
#print axioms ZInQBlueprint.SexticIgusaChart.parameters
#print axioms ZInQBlueprint.SexticIgusaChart.unmarked
#print axioms ZInQBlueprint.SexticIgusaChart.equation
