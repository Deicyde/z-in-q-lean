import DiamondProjection
import CutoffScalar

namespace ZInQBlueprint.DiamondHeight
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
noncomputable section
set_option exponentiation.threshold 500
set_option maxRecDepth 12000
attribute [local irreducible] oldCutoff cutoffProduct oddSupport oddProduct

/-- Stable height for the newform attached to a cochain with the reduced
auxiliary-field degree. The primitive level must be that of this newform. -/
theorem cutoff_noncm_height {a b:ℤ} {h C:ℝ} (c:1≤C) (F:QuotientFibre (heightRadical a b) h)
    (level:(F.level:ℝ)≤C*(heightRadical a b:ℝ)^2)
    (short:F.tower.fieldDegree≤1152*2^17*largeUnitOrders (oddSupport a b)) :
    h≤2^300*C^6*(cutoffProduct:ℝ)^12*(oddProduct a b:ℝ)^18 := by
  let B:ℝ:=cutoffProduct
  let M:ℝ:=oddProduct a b
  let U:ℝ:=largeUnitOrders (oddSupport a b)
  let e:=eulerFactor F.level.primeFactors
  have bo : 1≤B:=Nat.one_le_cast.mpr pos_cutoff
  have mo : 1≤M:=Nat.one_le_cast.mpr (pos_odd a b)
  have cp : 0≤C:=by linarith
  have ep : 0≤e := Finset.prod_nonneg (fun _ _=>by positivity)
  have one_e : 1≤e:= (show 1=eulerFactor ∅ by simp [eulerFactor]).trans_le (euler_mono (Finset.empty_subset _))
  have mu : U*e≤2^17*M:=paired_large a b F.support
  have d : (F.tower.fieldDegree:ℝ)≤(1152*2^17)*U := by
    dsimp only [U]
    exact_mod_cast short
  have te : (F.tower.determinant.ker.index:ℝ)*e ≤ 2^46*M := calc
    _ ≤ (2*((1152*2^17)*U))*e := by
      have ix : (F.tower.determinant.ker.index:ℝ)≤2*(F.tower.fieldDegree:ℝ):=by exact_mod_cast determinant_index F.tower
      exact mul_le_mul_of_nonneg_right (ix.trans (mul_le_mul_of_nonneg_left d (by norm_num))) ep
    _ = (2*(1152*2^17))*(U*e) := by ring
    _ ≤ (2*(1152*2^17))*(2^17*M) := mul_le_mul_of_nonneg_left mu (by norm_num)
    _ ≤ _ := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
  have du : (F.tower.fieldDegree:ℝ)≤2^46*M := d.trans <| calc
    _ ≤ (1152*2^17)*(U*e) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact le_mul_of_one_le_right (by positivity) one_e
    _ ≤ (1152*2^17)*(2^17*M) := mul_le_mul_of_nonneg_left mu (by norm_num)
    _ ≤ _ := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
  have nbound : (F.level:ℝ)≤C*(B*M)^2:=by simpa only [heightRadical,Nat.cast_mul] using level
  let T:ℝ:=2^46*C*B^2*M^3
  have oneT : 1≤T:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) c) (one_le_pow₀ bo)) (one_le_pow₀ mo)
  have dt : (F.tower.fieldDegree:ℝ)≤T:=du.trans <| mul_le_mul
    (le_mul_of_one_le_right (by positivity : (0:ℝ)≤2^46) (one_le_mul_of_one_le_of_one_le c (one_le_pow₀ bo)) |>.trans_eq (mul_assoc ..).symm)
    (by simpa only [pow_one] using pow_le_pow_right₀ mo (show 1≤3 by decide)) (by linarith) (by positivity)
  have cap : (F.coverDegree:ℝ)≤T := (degree_formula F).trans <| calc
    _ = (F.level:ℝ)*((F.tower.determinant.ker.index:ℝ)*e) := mul_assoc ..
    _ ≤ (C*(B*M)^2)*(2^46*M) := mul_le_mul nbound te (mul_nonneg (by positivity) ep) (by positivity)
    _ = _ := by dsimp only [T];ring
  calc
    _ ≤ 2^24*T^6:=jacobian_height oneT (by exact_mod_cast field_degree_pos F.tower) dt cap F.comparison
    _ = _ := by simp only [T,B,M,mul_pow,←pow_mul];ring

/-- The sharper coefficient retains twelfth power dependence on the fixed primorial. -/
theorem parameter_height_of_short_field {a b:ℤ} {C h K:ℝ} (c:1≤C) (kp:0≤K)
    (sections:pairLogHeight a b≤2*max 0 h+K)
    (branch:(∃F:QuotientFibre (heightRadical a b) h, (F.level:ℝ)≤C*(heightRadical a b:ℝ)^2 ∧
       F.tower.fieldDegree≤1152*2^17*largeUnitOrders (oddSupport a b)) ∨
       h≤6*(heightRadical a b:ℝ)+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*(heightRadical a b:ℝ))))) :
    pairLogHeight a b ≤ (2^301*C^6*(cutoffProduct:ℝ)^12+K)*(oddProduct a b:ℝ)^18 := by
  have bo : (1:ℝ)≤cutoffProduct:=Nat.one_le_cast.mpr pos_cutoff
  have mo : (1:ℝ)≤oddProduct a b:=Nat.one_le_cast.mpr (pos_odd a b)
  have rp: (1:ℝ)≤heightRadical a b:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd a b))
  have hB : h≤2^300*C^6*(cutoffProduct:ℝ)^12*(oddProduct a b:ℝ)^18 := by
    rcases branch with ⟨F,l,s⟩|cm
    · exact cutoff_noncm_height c F l s
    · have cm' := cm_linear rp cm
      rw [heightRadical,Nat.cast_mul] at cm'
      have k : (854:ℝ)≤2^300*C^6 :=
        (by norm_num : (854:ℝ)≤2^300).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ c))
      have bm := mul_le_mul
        (by simpa only [pow_one] using pow_le_pow_right₀ bo (show 1≤12 by decide))
        (by simpa only [pow_one] using pow_le_pow_right₀ mo (show 1≤18 by decide))
        (Nat.cast_nonneg _) (by positivity)
      exact cm'.trans ((mul_le_mul k bm (by positivity) (by positivity)).trans_eq (mul_assoc ..).symm)
  have bnd:=sections.trans (add_le_add (mul_le_mul_of_nonneg_left (max_le (by positivity) hB) (by norm_num : (0:ℝ)≤2)) (le_refl K))
  have km : K≤K*(oddProduct a b:ℝ)^18:=le_mul_of_one_le_right kp (one_le_pow₀ mo)
  rw [add_mul]
  calc
    _ ≤ _ := bnd
    _ ≤ 2*(2^300*C^6*(cutoffProduct:ℝ)^12*(oddProduct a b:ℝ)^18)+K*(oddProduct a b:ℝ)^18 := add_le_add (le_refl _) km
    _ = _ := by ring

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.cutoff_noncm_height
#print axioms ZInQBlueprint.DiamondHeight.parameter_height_of_short_field
