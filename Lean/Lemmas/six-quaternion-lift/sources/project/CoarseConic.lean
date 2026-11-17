import HeightSix
import ZInQKernel.Hypotheses.Height
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic

/-! The fibre of the Baba–Granath conic on the chart X = 4.
Here j = 16 Y²/(9 X²), so the coordinates satisfy Y² = 9j and Z² = −27j−16. -/

namespace ZInQBlueprint.CoarseConic
open ZInQBlueprint.SixContact
open QuadraticAlgebra
noncomputable section

def r (u : ℚ) := 240 * F u / (G u)^3
def h (u : ℚ) := H u / (G u)^3

theorem first_square (u : ℚ) : J u = -(r u)^2 := by
  unfold J r
  field_simp [(positive_denominator u).ne']
  ring

theorem second_square (u : ℚ) : -27*J u-16 = -(4*h u)^2 := by
  unfold h
  linear_combination -16 * pullback_square u

theorem radical_units {u : ℚ} (hu : u ∉ ZInQ.contactSet) : r u ≠ 0 ∧ h u ≠ 0 := by
  have hz : ∀ c ∈ ZInQ.contactSet, u-c ≠ 0 :=
    fun c hc => sub_ne_zero.mpr (fun e => hu (e ▸ hc))
  have hf : F u ≠ 0 := by simpa [ZInQ.contactSet,F,and_assoc] using hz
  exact ⟨div_ne_zero (mul_ne_zero (by norm_num) hf) (pow_ne_zero _ (positive_denominator u).ne'),
    div_ne_zero (third_fibre_empty u) (pow_ne_zero _ (positive_denominator u).ne')⟩

/-- The six-contact family avoids every finite exceptional value in the Mestre
determinant of Baba–Granath, Proposition 3.12. -/
theorem unmarked_range {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    -(16/27) < J u ∧ J u < 0 := by
  obtain ⟨hr,hh⟩ := radical_units hu
  constructor
  · have he := pullback_square u
    change 1+27*J u/16=(h u)^2 at he
    nlinarith [sq_pos_of_ne_zero hh]
  · rw [first_square]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero hr)

theorem mestre_factors {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    J u * (64*J u-81) * (27*J u+16) ≠ 0 := by
  obtain ⟨hlo,hhi⟩ := unmarked_range hu
  exact mul_ne_zero (mul_ne_zero hhi.ne (by linarith)) (by linarith)

/-- The sextic parameter and its discriminating factor over Q(√6). -/
theorem sextic_parameters {K : Type*} [Field K] [CharZero K] (u : ℚ) {d : K} (hd : d^2=6) :
    (d*(r u : K))^2 = -6*(J u : K) ∧
    9*(d*(r u : K))^2-32 = -32*(h u : K)^2 := by
  have h1 : (J u : K) = -(r u : K)^2 := by exact_mod_cast first_square u
  have h2 : -27*(J u : K)-16 = -(4*(h u : K))^2 := by exact_mod_cast second_square u
  rw [mul_pow, hd]
  constructor
  · linear_combination 6*h1
  · linear_combination 2*h2 + 54*h1

/-- The rational quadratic field with distinguished generator i. -/
abbrev Gaussian := QuadraticAlgebra ℚ (-1) 0

local instance : Fact (¬ IsSquare (-1 : ℚ)) :=
  ⟨by rintro ⟨x,hx⟩; nlinarith [sq_nonneg x]⟩

/-- First adjoin Y, then Z, using the equations on the chart X = 4. -/
abbrev First (u : ℚ) := QuadraticAlgebra ℚ (9*J u) 0
abbrev FibreAlgebra (u : ℚ) :=
  QuadraticAlgebra (First u) (algebraMap ℚ (First u) (-27*J u-16)) 0

def firstEquiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) : First u ≃ₐ[ℚ] Gaussian :=
  changeGeneratorEquiv (-1) 0 (Units.mk0 (3*r u) (mul_ne_zero (by norm_num) (radical_units hu).1)) 0
    (by simp [first_square]; ring) (by simp)

/-- Evaluation at two distinct roots, with inverse given by linear interpolation. -/
def splitQuadratic {K : Type*} [Field K] [CharZero K] {a d : K}
    (hd : d^2 = a) (hn : d ≠ 0) : QuadraticAlgebra K a 0 ≃ₐ[K] K × K where
  toFun z := (z.re + z.im*d, z.re - z.im*d)
  invFun z := ⟨(z.1+z.2)/2, (z.1-z.2)/(2*d)⟩
  left_inv z := by ext <;> simp; field_simp; ring
  right_inv z := by ext <;> simp <;> field_simp <;> ring
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp [← hd] <;> ring
  commutes' x := by ext <;> simp

/-- The whole unlevelled fibre along the six-contact pullback is two copies of Q(i). -/
def coarseFibreEquiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    FibreAlgebra u ≃ₐ[ℚ] Gaussian × Gaussian := by
  letI : Fact (¬ IsSquare (9*J u)) := ⟨by
    rintro ⟨a,ha⟩
    rw [first_square] at ha
    have hr := (radical_units hu).1
    nlinarith [sq_pos_of_ne_zero hr, sq_nonneg a]⟩
  let e := firstEquiv hu
  let z : Gaussian := ⟨0,4*h u⟩
  have hz : z^2 = algebraMap ℚ Gaussian (-27*J u-16) := by
    rw [second_square, sq]
    apply QuadraticAlgebra.ext
    · change 0*0 + (-1:ℚ)*(4*h u)*(4*h u) = -(4*h u)^2
      ring
    · change 0*(4*h u) + 4*h u*0 + 0*(4*h u)*(4*h u) = (0:ℚ)
      ring
  have hn : z ≠ 0 := by
    intro hz0
    have him := congrArg QuadraticAlgebra.im hz0
    have hh := (radical_units hu).2
    change 4*h u = 0 at him
    exact hh (by linarith)
  have hs : (e.symm z)^2 = algebraMap ℚ (First u) (-27*J u-16) := by
    rw [← map_pow, hz, AlgEquiv.commutes]
  have hne : e.symm z ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).2 hn
  exact ((splitQuadratic hs hne).restrictScalars ℚ).trans (AlgEquiv.prodCongr e e)

end
end ZInQBlueprint.CoarseConic

#print axioms ZInQBlueprint.CoarseConic.first_square
#print axioms ZInQBlueprint.CoarseConic.second_square
#print axioms ZInQBlueprint.CoarseConic.radical_units
#print axioms ZInQBlueprint.CoarseConic.unmarked_range
#print axioms ZInQBlueprint.CoarseConic.mestre_factors
#print axioms ZInQBlueprint.CoarseConic.sextic_parameters
#print axioms ZInQBlueprint.CoarseConic.splitQuadratic
#print axioms ZInQBlueprint.CoarseConic.coarseFibreEquiv
