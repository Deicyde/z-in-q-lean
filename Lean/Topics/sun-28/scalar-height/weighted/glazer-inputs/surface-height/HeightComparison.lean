import MetricCalculus
import VerticalOrders
import ModularBudget
import PellRows
import Mathlib.Analysis.Real.Pi.Bounds

namespace ZInQBlueprint.FiveMetric
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
noncomputable section
set_option exponentiation.threshold 130

/-- The reciprocal curvature bound, in the coordinate t=32s, away from the branch points. -/
def MetricCertificate (C : ℝ) := ∀ z : ℂ, (∀ i,0<radius z i) →
    let G := (∑ i,partialX z i)^2+(∑ i,partialY z i)^2
    2*(mass z)^3≤C*((mass z*(∑ i : Fin 4,1/radius z i)-G)*(∏ i : Fin 4,radius z i))

/-- The order inequalities for both relative bicanonical sections of a reduced fibre. -/
def VerticalCertificate (L : ℕ) := ∀ p : ℕ, ∀ [Fact p.Prime], ∀ (r:Fin 4→ℤ) (d t:ℤ),
    ContactOrders p r → (∀ i,r i≤d) → (0≤t ∨ ∀ i,r i=t) →
    -(padicValInt p (L:ℤ):ℤ) ≤ 2*d-∑i,r i ∧ -(padicValInt p (L:ℤ):ℤ) ≤ t+2*d-∑i,r i

def comparisonError (C : ℝ) (L : ℕ) := 2*Real.log Real.pi + Real.log 210 +
    Real.log L + Real.log (4*C) + Real.log 32

theorem certified_constants : MetricCertificate 2048 ∧ VerticalCertificate 823200 := by
  refine ⟨fun z off=>?_,fun _ _ _ _ _ h d t=>section_pair h d t⟩
  let G := (∑ i,partialX z i)^2+(∑ i,partialY z i)^2
  have g : G≤16 := gradient_sq z off
  have h := curvature_numerator z off (G:=G) g
  change 2*(mass z)^3≤2048*((mass z*(∑ i : Fin 4,1/radius z i)-G)*(∏ i : Fin 4,radius z i))
  exact (curvature_bound z).trans ((mul_assoc (2048:ℝ) 65536 (triples z)).le.trans
    (mul_le_mul_of_nonneg_left h (by norm_num)))

theorem comparison_error : comparisonError 2048 823200 ≤ 35 := by
  have pi:=Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  have eqn : 2*Real.log 4+Real.log 210+Real.log 823200+Real.log (4*2048)+Real.log 32=
      Real.log (4^2*210*823200*(4*2048)*32) := by
    conv_rhs => rw [Real.log_mul (by positivity) (by norm_num),Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by norm_num),Real.log_mul (by positivity) (by norm_num),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have logcap:=Real.log_le_log (by norm_num : (0:ℝ)<4^2*210*823200*(4*2048)*32)
    (by norm_num : (4^2*210*823200*(4*2048)*32:ℝ)≤2^50)
  rw [Real.log_pow] at logcap
  unfold comparisonError
  norm_num only [Nat.cast_ofNat] at *
  linarith only [pi,eqn,logcap,Real.log_two_lt_d9]

def levelScale (R:ℝ) := (210:ℝ)^300*R^2

/-- The geometric applications which have to be furnished for a particular primitive pair.
The two alternatives state respectively the modular transfer data and the CM isogeny bound. -/
structure SurfaceComparison (A B : ℤ) where
  height : ℝ
  sections : ∀ C : ℝ, ∀ L : ℕ, 0<C → 0<L → MetricCertificate C → VerticalCertificate L →
      pairLogHeight A B≤2*height+comparisonError C L
  branches :
    let R:ℝ:=heightRadical A B
    Nonempty (ModularData (levelScale R) height) ∨
      height≤6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R)))

def SurfaceApplications := ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    Nonempty (SurfaceComparison A B)

private theorem large_power : (2:ℝ)^24*(210:ℝ)^3600≤(4608:ℝ)^165888 := calc
  _ ≤ (2:ℝ)^24*((2:ℝ)^8)^3600 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)
  _ = (2:ℝ)^28824 := by rw [←pow_mul,←pow_add]
  _ ≤ 2^165888 := pow_le_pow_right₀ (by norm_num) (by decide)
  _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _

theorem five_height_of_surface (inputs : SurfaceApplications) :
    OriginalFiveHeight glazerConstant24 oldCutoff := by
  intro A B cop off
  obtain ⟨F⟩:=inputs A B cop off
  let R:ℝ:=heightRadical A B
  have posR : 1≤R:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have R24 : 0≤R^24:=pow_nonneg (by linarith) _
  let M:ℝ:=(4608:ℝ)^165888
  let N:ℝ:=(6:ℝ)^100
  have pM : 0≤M:=pow_nonneg (by norm_num) _
  have pN : 0≤N:=pow_nonneg (by norm_num) _
  have height : F.height≤(M+N)*R^24 := by
    have cases : Nonempty (ModularData (levelScale R) F.height) ∨
        F.height≤6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R))) := F.branches
    rcases cases with hm|cm
    · obtain ⟨D⟩:=hm
      have u : 1≤levelScale R:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ posR)
      have mod := modular_height u D
      have id : (2:ℝ)^24*(levelScale R)^12=(2^24*210^3600)*R^24 := by
        simp only [levelScale,mul_pow,←pow_mul,mul_assoc]
      rw [id] at mod
      exact mod.trans (mul_le_mul_of_nonneg_right (large_power.trans (le_add_of_nonneg_right pN)) R24)
    · exact (cm_height posR cm).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left pM) R24)
  have geo:=F.sections 2048 823200 (by norm_num) (by decide) certified_constants.1 certified_constants.2
  have bound : pairLogHeight A B≤2*(M+N)*R^24+35:=by
    rw [mul_assoc]
    exact geo.trans (add_le_add (mul_le_mul_of_nonneg_left height (by norm_num)) comparison_error)
  have odd : (1:ℝ)≤(oddProduct A B:ℝ)^24 := one_le_pow₀ (Nat.one_le_cast.mpr (pos_odd A B))
  have coeff : glazerConstant24=2*(M+N)*(cutoffProduct:ℝ)^24+128:=by
    simp only [glazerConstant24,cutoffProduct,primeProduct,Nat.cast_prod,M,N]
  have radical : R^24=(cutoffProduct:ℝ)^24*(oddProduct A B:ℝ)^24:=by
    simp only [R,heightRadical,Nat.cast_mul,mul_pow]
  rw [radical] at bound
  rw [coeff,←Nat.cast_prod]
  change _≤(2*(M+N)*(cutoffProduct:ℝ)^24+128)*(oddProduct A B:ℝ)^24
  rw [add_mul,mul_assoc (2*(M+N))]
  exact bound.trans (add_le_add (le_refl _) ((show (35:ℝ)≤128 by norm_num).trans (le_mul_of_one_le_right (by norm_num) odd)))

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.certified_constants
#print axioms ZInQBlueprint.FiveMetric.comparison_error
#print axioms ZInQBlueprint.FiveMetric.five_height_of_surface
