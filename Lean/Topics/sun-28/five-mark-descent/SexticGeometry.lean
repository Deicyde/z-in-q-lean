import SexticChart

/-! A monic sextic defining the same affine equation and its six simple branch roots. -/
namespace Sun28.FiveDescent
open Polynomial
noncomputable section

def quadratic (r : ℚ) : Polynomial ℚ := X^2-C r

def alpha₁ (d : ℚ) := 1/d
def alpha₂ (d : ℚ) := 2400/(2401*d)
def alpha₃ (d : ℚ) := 375/(343*d)

def monicSextic (d : ℚ) :=
  quadratic (alpha₁ d)*quadratic (alpha₂ d)*quadratic (alpha₃ d)

private theorem quad_deg (r : ℚ) : (quadratic r).natDegree=2 := Polynomial.natDegree_X_pow_sub_C

private theorem quad_ne (r : ℚ) : quadratic r≠0 := by
  intro z
  have h := quad_deg r
  rw [z,natDegree_zero] at h
  omega

private theorem quad_coprime {r s : ℚ} (ne : r≠s) : IsCoprime (quadratic r) (quadratic s) := by
  refine ⟨C ((s-r)⁻¹),-C ((s-r)⁻¹),?_⟩
  calc
    C (s-r)⁻¹*quadratic r+-C (s-r)⁻¹*quadratic s=C (s-r)⁻¹*(C s-C r) := by unfold quadratic;ring
    _=1 := by rw [←map_sub,←map_mul,inv_mul_cancel₀ (sub_ne_zero.mpr ne.symm),map_one]

theorem monicSextic_properties {d : ℚ} (nz : d≠0) :
    (monicSextic d).Monic ∧ (monicSextic d).natDegree=6 ∧ (monicSextic d).Separable := by
  have mn (a : ℚ) : (quadratic a).Monic := monic_X_pow_sub_C a (by decide)
  have nn (a b : ℚ) (an : a≠0) (bn : b≠0) : a/(b*d)≠0 := div_ne_zero an (mul_ne_zero bn nz)
  have sep (r : ℚ) (n : r≠0) : (quadratic r).Separable := separable_X_pow_sub_C r (by norm_num) n
  have n₁ : alpha₁ d≠0 := div_ne_zero one_ne_zero nz
  have n₂ : alpha₂ d≠0 := nn _ _ (by norm_num) (by norm_num)
  have n₃ : alpha₃ d≠0 := nn _ _ (by norm_num) (by norm_num)
  have e₁₂ : alpha₁ d≠alpha₂ d := by unfold alpha₁ alpha₂;intro h;field_simp [nz] at h;linarith
  have e₁₃ : alpha₁ d≠alpha₃ d := by unfold alpha₁ alpha₃;intro h;field_simp [nz] at h;linarith
  have e₂₃ : alpha₂ d≠alpha₃ d := by unfold alpha₂ alpha₃;intro h;field_simp [nz] at h;linarith
  refine ⟨((mn _).mul (mn _)).mul (mn _),?_,?_⟩
  · unfold monicSextic
    rw [natDegree_mul (mul_ne_zero (quad_ne _) (quad_ne _)) (quad_ne _),
      natDegree_mul (quad_ne _) (quad_ne _),quad_deg,quad_deg,quad_deg]
  · exact ((sep _ n₁).mul (sep _ n₂) (quad_coprime e₁₂)).mul (sep _ n₃)
      ((quad_coprime e₁₃).mul_left (quad_coprime e₂₃))

theorem sextic_eq_eval {d : ℤ} (nz : d≠0) (x : ℚ) :
    sextic d x=823543*(d:ℚ)^3*(monicSextic d).eval x := by
  have n : (d:ℚ)≠0 := by exact_mod_cast nz
  simp [sextic,cubic,monicSextic,quadratic,alpha₁,alpha₂,alpha₃]
  field_simp [n]
  ring

end
end Sun28.FiveDescent
#print axioms Sun28.FiveDescent.monicSextic_properties
#print axioms Sun28.FiveDescent.sextic_eq_eval
