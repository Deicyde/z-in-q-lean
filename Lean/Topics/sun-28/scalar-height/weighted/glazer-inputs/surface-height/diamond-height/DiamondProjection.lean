import DiamondHeight
import SelectedMenus28
import OneSignPolynomial

namespace ZInQBlueprint.DiamondHeight
open Sun28 Sun28.Concrete Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open Sun28.MultiplierChoice ZInQBlueprint.FiveMetric ZInQBlueprint.WildLevel
noncomputable section
set_option exponentiation.threshold 250
set_option maxRecDepth 12000

/-- These are pointwise applications to a primitive marked slope. The curve
and field degrees refer to the same newform and surface as the stable height. -/
def MarkedQuotients (C K : ℝ) : Prop := ∀ A B : ℤ, Int.gcd A B=1 → (∀ i, oldForm i A B≠0) →
  ∃ h:ℝ, pairLogHeight A B≤2*max 0 h+K ∧
    (let R:=heightRadical A B
     (∃ F : QuotientFibre R h, (F.level:ℝ)≤C*(R:ℝ)^2) ∨
      h≤6*(R:ℝ)+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*(R:ℝ)))))

def coefficient18 (C K : ℝ) := 2^103*C^6*(cutoffProduct:ℝ)^18+K

theorem marked_height18 {C K : ℝ} (c : 1≤C) (k : 0≤K) (marked : MarkedQuotients C K)
    (A B:ℤ) (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤coefficient18 C K*(oddProduct A B:ℝ)^18 := by
  let R:=heightRadical A B
  have rp : 0<R:=Nat.mul_pos pos_cutoff (pos_odd A B)
  have r : (1:ℝ)≤R:=by exact_mod_cast rp
  have cpos : 0≤C:=by linarith
  obtain ⟨h,sections,hm|cm⟩:=marked A B cop off
  all_goals
    suffices bound : h≤2^102*C^6*(R:ℝ)^18 by
      have h0:=max_le (by positivity : (0:ℝ)≤2^102*C^6*(R:ℝ)^18) bound
      have b:=sections.trans (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0:ℝ)≤2)) (le_refl K))
      have radical : (R:ℝ)^18=(cutoffProduct:ℝ)^18*(oddProduct A B:ℝ)^18 := by
        simp only [R,heightRadical,Nat.cast_mul,mul_pow]
      rw [radical] at b
      have km : K≤K*(oddProduct A B:ℝ)^18 := le_mul_of_one_le_right k
        (one_le_pow₀ (Nat.one_le_cast.mpr (pos_odd A B)))
      unfold coefficient18
      rw [add_mul]
      linarith only [b,km]
  · obtain ⟨F,level⟩:=hm
    exact noncm_height18 rp c F level
  · have hcm:=cm_linear r cm
    have u : (854:ℝ)≤2^102*C^6 :=
      (by norm_num : (854:ℝ)≤2^102).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ c))
    exact hcm.trans (mul_le_mul u (by simpa only [pow_one] using pow_le_pow_right₀ r (show 1≤18 by decide))
      (by positivity) (by positivity))

/-- The original conductor constant and comparison error already suffice to
feed the improved estimate to both inverse witness loci. -/
theorem original_height_of_quotients (marked : MarkedQuotients (210^300) 128) :
    OriginalFiveHeight glazerConstant24 oldCutoff := by
  have c : (1:ℝ)≤210^300:=one_le_pow₀ (by norm_num)
  have large : (2:ℝ)^103*(210^300)^6 ≤ 4608^165888 := calc
    _ ≤ (2:ℝ)^103*((2^8)^300)^6 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (pow_le_pow_left₀ (by norm_num) (by norm_num) _) _) (by positivity)
    _ = (2:ℝ)^14503 := by rw [← pow_mul,←pow_mul,←pow_add]
    _ ≤ 2^165888 := pow_le_pow_right₀ (by norm_num) (by decide)
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have major : (2:ℝ)^103*(210^300)^6 ≤ 2*(4608^165888+6^100) := by
    have M : (0:ℝ)≤4608^165888:=pow_nonneg (by norm_num) _
    have Z : (0:ℝ)≤6^100:=pow_nonneg (by norm_num) _
    exact large.trans ((le_add_of_nonneg_right Z).trans
      (le_mul_of_one_le_left (add_nonneg M Z) (by norm_num)))
  have coeff : coefficient18 (210^300) 128≤glazerConstant24 := by
    unfold coefficient18 glazerConstant24
    rw [←Nat.cast_prod]
    change _≤2*(4608^165888+6^100)*(cutoffProduct:ℝ)^24+128
    exact add_le_add (mul_le_mul major
      (pow_le_pow_right₀ (Nat.one_le_cast.mpr pos_cutoff) (show 18≤24 by decide))
      (by positivity) (by positivity)) (le_refl _)
  intro A B cop off
  rw [← Nat.cast_prod]
  change _≤glazerConstant24*(oddProduct A B:ℝ)^24
  exact (marked_height18 c (by norm_num) marked A B cop off).trans
    (mul_le_mul coeff (pow_le_pow_right₀ (Nat.one_le_cast.mpr (pos_odd A B)) (show 18≤24 by decide))
      (by positivity) (by unfold glazerConstant24; positivity))

theorem polynomial_of_quotients (marked : MarkedQuotients (210^300) 128)
    (points : JointSelectedMenus) (x:ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  refine ⟨WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
    (original_height_of_quotients marked)) x,?_⟩
  rintro ⟨k,rfl⟩
  exact root_of_selected_menus (points k)

theorem one_sign_of_quotients (marked : MarkedQuotients (210^300) 128)
    (points : JointSelectedMenus) (x:ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 oneSignPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  (compiled_one_sign x).trans (polynomial_of_quotients marked points x)

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.marked_height18
#print axioms ZInQBlueprint.DiamondHeight.original_height_of_quotients
#print axioms ZInQBlueprint.DiamondHeight.polynomial_of_quotients
#print axioms ZInQBlueprint.DiamondHeight.one_sign_of_quotients
