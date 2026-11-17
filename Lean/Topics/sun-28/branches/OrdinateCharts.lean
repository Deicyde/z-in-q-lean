import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic

/-! Sun §8.1. Each allowed ordinate is recovered from one rational root.
The zero chart is kept explicitly. -/
namespace Sun28.Ordinates

abbrev K := QuadraticAlgebra ℚ 2 0

/-- Real and irrational coefficients with respect to the basis 1,√2. -/
def pair (a b : ℚ) : K := ⟨a,b⟩

theorem square_coordinates (u v : ℚ) : (pair u v)^2 = pair (u^2+2*v^2) (2*u*v) := by
  apply QuadraticAlgebra.ext <;> simp [pair,pow_two] <;> ring

def quartic (a b t : ℚ) := t^4-a*t^2+b^2/2

inductive Branch where
  | mixed | realPart | radicalPart | zero
  deriving DecidableEq

def Branch.condition (a b t : ℚ) : Branch → Prop
  | .mixed => b ≠ 0 ∧ quartic a b t = 0
  | .realPart => b = 0 ∧ a ≠ 0 ∧ t^2=a
  | .radicalPart => b = 0 ∧ a ≠ 0 ∧ 2*t^2=a
  | .zero => a = 0 ∧ b = 0 ∧ t=0

def Branch.point (b t : ℚ) : Branch → K
  | .mixed => pair t (b/(2*t))
  | .realPart => pair t 0
  | .radicalPart => pair 0 t
  | .zero => 0

private theorem pair_eq {u v a b : ℚ} : pair u v = pair a b ↔ u=a ∧ v=b := by
  constructor
  · intro h; exact ⟨congrArg QuadraticAlgebra.re h,congrArg QuadraticAlgebra.im h⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- Equality of the represented points retains the sign of each ordinate. -/
theorem four_charts (a b : ℚ) (y : K) :
    y^2 = pair a b ↔ ∃ (k : Branch) (t : ℚ), k.condition a b t ∧ y = k.point b t := by
  obtain ⟨u,v⟩ := y
  change (pair u v)^2 = pair a b ↔ _
  rw [square_coordinates,pair_eq]
  constructor
  · rintro ⟨hu,hv⟩
    by_cases hb : b=0
    · by_cases ha : a=0
      · have hz : u=0 ∧ v=0 := by constructor <;> nlinarith [sq_nonneg u,sq_nonneg v]
        exact ⟨.zero,0,⟨ha,hb,rfl⟩,by rcases hz with ⟨rfl,rfl⟩; rfl⟩
      · have h : u=0 ∨ v=0 := by
          simpa [mul_eq_zero] using (hv.trans hb)
        rcases h with rfl | rfl
        · exact ⟨.radicalPart,v,⟨hb,ha,by simpa using hu⟩,rfl⟩
        · exact ⟨.realPart,u,⟨hb,ha,by simpa using hu⟩,rfl⟩
    · have h0 : u ≠ 0 := by rintro rfl; simp at hv; exact hb hv.symm
      refine ⟨.mixed,u,⟨hb,?_⟩,?_⟩
      · rw [← hu,← hv]; unfold quartic; ring
      · change pair u v = pair u (b/(2*u))
        apply pair_eq.mpr
        refine ⟨rfl,?_⟩
        rw [← hv]; field_simp
  · rintro ⟨k,t,h,he⟩
    change pair u v = k.point b t at he
    cases k with
    | mixed =>
      obtain ⟨hb,hq⟩ := h
      obtain ⟨rfl,hv⟩ := pair_eq.mp he
      have ht : u ≠ 0 := by rintro rfl; simp [quartic] at hq; exact hb hq
      rw [hv]
      unfold quartic at hq
      constructor
      · field_simp [ht]; nlinarith [hq]
      · field_simp [ht]
    | realPart =>
      obtain ⟨rfl,_,hq⟩ := h
      obtain ⟨rfl,rfl⟩ := pair_eq.mp he
      simp [hq]
    | radicalPart =>
      obtain ⟨rfl,_,hq⟩ := h
      obtain ⟨rfl,rfl⟩ := pair_eq.mp he
      simp [hq]
    | zero =>
      obtain ⟨rfl,rfl,rfl⟩ := h
      obtain ⟨rfl,rfl⟩ := pair_eq.mp (show pair u v = pair 0 0 from he)
      norm_num

def ordinateReal (u v : ℚ) := u^3+6*u*v^2-11*u+12*v
def ordinateRadical (u v : ℚ) := 3*u^2*v+2*v^3-11*v+6*u

theorem curve_rhs (u v : ℚ) : (pair u v)^3 - pair 11 (-6) * pair u v =
    pair (ordinateReal u v) (ordinateRadical u v) := by
  apply QuadraticAlgebra.ext <;> simp [pair,ordinateReal,ordinateRadical,pow_succ] <;> ring

/-- The degree-four root encoding for the actual x-coordinate on Sun's curve. -/
theorem ordinate_charts (u v : ℚ) (y : K) :
    y^2 = (pair u v)^3 - pair 11 (-6) * pair u v ↔ ∃ (k : Branch) (t : ℚ),
      k.condition (ordinateReal u v) (ordinateRadical u v) t ∧
      y=k.point (ordinateRadical u v) t := by
  rw [curve_rhs]; exact four_charts ..

end Sun28.Ordinates
#print axioms Sun28.Ordinates.square_coordinates
#print axioms Sun28.Ordinates.four_charts
#print axioms Sun28.Ordinates.curve_rhs
#print axioms Sun28.Ordinates.ordinate_charts
