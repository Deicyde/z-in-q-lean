import PairedEuler
import DiamondIndex
import HeightBudget18
import InertiaLevel

namespace ZInQBlueprint.DiamondHeight
open ZInQBlueprint.WildLevel
noncomputable section
set_option exponentiation.threshold 250

/-- The fields and modular curve used at a single marked slope. The field
degree is computed from the scalar character on the marking subgroup. -/
structure QuotientFibre (R : ℕ) (h : ℝ) where
  level : ℕ
  support : level.primeFactors ⊆ R.primeFactors
  tower : ScalarTower R
  coverDegree : ℕ
  positive : 0<level
  primitiveRoot : AlgebraicClosure ℚ
  primitive : IsPrimitiveRoot primitiveRoot level
  nebentypus : (ZMod level)ˣ →* ℂˣ
  determinant_eq : let _ : NeZero level := ⟨positive.ne'⟩
                   tower.determinant=nebentypus.comp (cyclotomicQuotient primitive)
  cover_index : coverDegree≤(gammaChar nebentypus).index
  gamma_zero_index : ((CongruenceSubgroup.Gamma0 level).index:ℝ)≤(level:ℝ)*eulerFactor level.primeFactors
  comparison : JacobianComparison coverDegree tower.fieldDegree h

theorem degree_formula {R:ℕ} {h:ℝ} (F : QuotientFibre R h) :
    (F.coverDegree:ℝ)≤(F.level:ℝ)*F.tower.determinant.ker.index*eulerFactor F.level.primeFactors := by
  let : NeZero F.level := ⟨F.positive.ne'⟩
  have a:= F.cover_index.trans (gamma_index F.primitive F.nebentypus)
  rw [←F.determinant_eq] at a
  have b : (F.coverDegree:ℝ)≤(F.tower.determinant.ker.index:ℝ)*(CongruenceSubgroup.Gamma0 F.level).index :=
    by exact_mod_cast a
  calc
    _ ≤ _ := b
    _ ≤ (F.tower.determinant.ker.index:ℝ)*((F.level:ℝ)*eulerFactor F.level.primeFactors) :=
      mul_le_mul_of_nonneg_left F.gamma_zero_index (by positivity)
    _ = _ := by ring

theorem character_times_index_factor {R : ℕ} {h : ℝ} (rp : 0<R) (F : QuotientFibre R h) :
    (F.tower.determinant.ker.index:ℝ)*eulerFactor F.level.primeFactors ≤ 4608*R := by
  have t := (determinant_index F.tower).trans (Nat.mul_le_mul_left 2 (scalar_field_degree F.tower))
  have tn : F.tower.determinant.ker.index≤4608*unitOrders R := by linarith only [t]
  have tr : (F.tower.determinant.ker.index:ℝ)≤4608*(unitOrders R:ℝ) := by exact_mod_cast tn
  have ep : 0≤eulerFactor F.level.primeFactors := Finset.prod_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ (4608*(unitOrders R:ℝ))*eulerFactor F.level.primeFactors := mul_le_mul_of_nonneg_right tr ep
    _ ≤ 4608*(R:ℝ) := by rw [mul_assoc];gcongr;exact paired_euler rp F.support

/-- Valid for every conductor constant C≥1, including the original 210^300. -/
theorem noncm_height18 {R : ℕ} {h C : ℝ} (rp : 0<R) (one : 1≤C) (F : QuotientFibre R h)
    (level : (F.level:ℝ)≤C*(R:ℝ)^2) : h≤(2:ℝ)^102*C^6*(R:ℝ)^18 := by
  have Rone : (1:ℝ)≤R:=by exact_mod_cast rp
  have cp : 0≤C:=by linarith
  let T : ℝ := 2^13*C*(R:ℝ)^3
  have rcube : (R:ℝ)≤(R:ℝ)^3:=by simpa using pow_le_pow_right₀ Rone (show 1≤3 by decide)
  have base : (8192:ℝ)≤2^13*C := by norm_num;linarith
  have OT : 1≤T := one_le_mul_of_one_le_of_one_le (by linarith only [base]) (one_le_pow₀ Rone)
  have d := (scalar_field_degree F.tower).trans (Nat.mul_le_mul_left 2304 (unitOrders_le rp))
  have dR : (F.tower.fieldDegree:ℝ)≤2304*(R:ℝ) := by exact_mod_cast d
  have dT : (F.tower.fieldDegree:ℝ)≤T := dR.trans (mul_le_mul (by linarith only [base]) rcube (by positivity) (by positivity))
  have cover : (F.coverDegree:ℝ)≤T := (degree_formula F).trans <| calc
    _ = (F.level:ℝ)*((F.tower.determinant.ker.index:ℝ)*eulerFactor F.level.primeFactors) := mul_assoc ..
    _ ≤ (C*(R:ℝ)^2)*(4608*(R:ℝ)) :=
      mul_le_mul level (character_times_index_factor rp F)
        (mul_nonneg (by positivity) (Finset.prod_nonneg (fun _ _ => by positivity))) (by positivity)
    _ ≤ T := by dsimp [T];nlinarith only [mul_nonneg cp (pow_nonneg (Nat.cast_nonneg R : (0:ℝ)≤R) 3)]
  have dp : (1:ℝ)≤F.tower.fieldDegree:=by exact_mod_cast field_degree_pos F.tower
  calc
    _ ≤ 2^24*T^6 := jacobian_height OT dp dT cover F.comparison
    _ = _ := by simp only [T,mul_pow,←pow_mul];ring

/-- The separate dyadic conductor argument specializes the constant to 2^162. -/
theorem sharp_noncm_height18 {R : ℕ} {h : ℝ} (rp : 0<R) (F : QuotientFibre R h)
    (localData : ConductorRealizations F.level R) : h≤2^162*(R:ℝ)^18 := by
  have z:=Nat.le_of_dvd (by positivity : 0<2^10*R^2) (primitive_level_dvd rp localData)
  have level : (F.level:ℝ)≤(2:ℝ)^10*(R:ℝ)^2 := by exact_mod_cast z
  have bound:=noncm_height18 rp (by norm_num : (1:ℝ)≤2^10) F level
  rwa [←pow_mul,←pow_add] at bound

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.degree_formula
#print axioms ZInQBlueprint.DiamondHeight.character_times_index_factor
#print axioms ZInQBlueprint.DiamondHeight.noncm_height18
#print axioms ZInQBlueprint.DiamondHeight.sharp_noncm_height18
