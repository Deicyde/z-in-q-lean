import InertiaLevel
import MarkedSurfaceEndpoint

namespace ZInQBlueprint.WildLevel
open ZInQBlueprint.FiveMetric Sun28.HeightFibres Sun28.Ordinary Sun28.FiveMarkUnits
noncomputable section
set_option exponentiation.threshold 250

/-- The modular transfer is monotone in an upper bound for the primitive level. -/
def monotone_modular {u v h : ℝ} (uPos:0≤u) (uv:u≤v) (D : ModularData u h) :
    ModularData v h where
  genus := D.genus
  fieldDegree := D.fieldDegree
  jacHeight := D.jacHeight
  complementHeight := D.complementHeight
  genus_pos := D.genus_pos
  genus_bound := D.genus_bound.trans (by gcongr)
  degree_pos := D.degree_pos
  degree_bound := D.degree_bound.trans (by gcongr)
  height_bound := D.height_bound.trans (by gcongr)
  isogeny_bound := D.isogeny_bound
  lower_bound := D.lower_bound

/-- The analytic transfer uses the actual primitive level, with the fibre
field bounded by 576. This expresses all three estimates before substituting
a bound in terms of the contact radical. -/
structure NewformFibre (R : ℕ) (h : ℝ) where
  level : ℕ
  conductor : ConductorRealizations level R
  transfer : ModularData (level:ℝ) h

/-- The smaller scale retains exponent 24 for the full-level Jacobian route. -/
theorem noncm_height {R : ℕ} {h : ℝ} (rp:0<R) (F : NewformFibre R h) :
    h≤(2:ℝ)^144*(R:ℝ)^24 := by
  have N := Nat.le_of_dvd (by positivity : 0<2^10*R^2) (primitive_level_dvd rp F.conductor)
  have small : (F.level:ℝ)≤(2:ℝ)^10*(R:ℝ)^2 := by exact_mod_cast N
  have one : 1≤(F.level:ℝ) := by exact_mod_cast F.conductor.positive
  calc h ≤ (2:ℝ)^24*(F.level:ℝ)^12 := modular_height one F.transfer
       _ ≤ (2:ℝ)^24*((2:ℝ)^10*(R:ℝ)^2)^12 := by gcongr
       _ = _ := by rw [mul_pow,←pow_mul,←pow_mul,←mul_assoc,←pow_add]

def LevelApplications := ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
  ∃ h : ℝ, (∀ C : ℝ, ∀ L : ℕ, 0<C → 0<L → MetricCertificate C → VerticalCertificate L →
      pairLogHeight A B≤2*h+comparisonError C L) ∧
    (Nonempty (NewformFibre (heightRadical A B) h) ∨
       let R:ℝ:=heightRadical A B
       h≤6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R))))

/-- Reuse the declared surface projection for the same marked pair. -/
theorem surface_of_level (input : LevelApplications) : SurfaceApplications := by
  intro A B cop off
  obtain ⟨h,sections,hm|cm⟩:=input A B cop off
  · obtain ⟨F⟩:=hm
    let R:=heightRadical A B
    have rp : 0<R:=Nat.mul_pos pos_cutoff (pos_odd A B)
    have z := Nat.le_of_dvd (by positivity : 0<2^10*R^2) (primitive_level_dvd rp F.conductor)
    have bound : (F.level:ℝ)≤(2:ℝ)^10*(R:ℝ)^2 := by exact_mod_cast z
    have big : (2:ℝ)^10≤(210:ℝ)^300 := by
      exact (pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ)≤210) 10).trans
        (pow_le_pow_right₀ (by norm_num) (by decide : 10≤300))
    exact ⟨⟨h,sections,Or.inl ⟨monotone_modular (by positivity) (bound.trans
      (mul_le_mul_of_nonneg_right big (sq_nonneg _))) F.transfer⟩⟩⟩
  · exact ⟨⟨h,sections,Or.inr cm⟩⟩

theorem polynomial_of_local_conductors (realCurves : Sun28.RealComponents.PublishedProposition72)
    (quadric : Sun28.ConeCount.PublishedQuadricCount) (input : LevelApplications)
    (moments : Sun28.PrimeValues.FirstMomentInputs) (points : RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Sun28.Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  polynomial_of_surface realCurves quadric (surface_of_level input) moments points x

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.monotone_modular
#print axioms ZInQBlueprint.WildLevel.noncm_height
#print axioms ZInQBlueprint.WildLevel.surface_of_level
#print axioms ZInQBlueprint.WildLevel.polynomial_of_local_conductors
