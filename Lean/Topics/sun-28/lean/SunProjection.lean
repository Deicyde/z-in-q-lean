import Mathlib.Tactic

/-! Sun v1, §8.3 and Proposition 10.1. Coefficients are listed in increasing
order of degree, with the implicit monic coefficient last. -/
namespace Sun28.Projection

/-- The monic polynomial whose coefficient numerators have common denominator D. -/
def monicValue (D t : ℚ) : List ℚ → ℚ
  | [] => 1
  | a :: tail => a / D + t * monicValue D t tail

/-- A polynomial expression in the numerators, D, G, and w, defined even at a failed guard. -/
def guardedValue (D G w : ℚ) : List ℚ → ℚ
  | [] => 1
  | a :: tail => guardedValue D G w tail + a * D * (G * w) * (D^2 * (G * w))^tail.length

theorem guard_zero (D G w : ℚ) (A : List ℚ) (h : D = 0 ∨ G = 0 ∨ w = 0) :
    guardedValue D G w A = 1 := by
  induction A with
  | nil => rfl
  | cons a tail ih =>
    rw [guardedValue, ih]
    rcases h with rfl | rfl | rfl <;> simp

theorem reciprocal_identity (D G w : ℚ) (A : List ℚ) (hD : D ≠ 0) (hG : G ≠ 0) (hw : w ≠ 0) :
    guardedValue D G w A = (D^2 * (G*w))^A.length * monicValue D (D^2 * (G*w))⁻¹ A := by
  let c := D^2 * (G*w)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  change guardedValue D G w A = c^A.length * monicValue D c⁻¹ A
  induction A with
  | nil => simp [guardedValue,monicValue]
  | cons a tail ih =>
    rw [guardedValue,ih,List.length_cons,monicValue]
    change c^tail.length * monicValue D c⁻¹ tail + a*D*(G*w)*c^tail.length =
      c^(tail.length+1) * (a/D + c⁻¹ * monicValue D c⁻¹ tail)
    rw [pow_succ c tail.length]
    dsimp only [c]
    field_simp [hD,hG,hw]
    ring

/-- One rational witness simultaneously enforces the guards and a nonzero rational root. -/
theorem reciprocal_projection (D G : ℚ) (A : List ℚ) :
    (∃ w : ℚ, guardedValue D G w A = 0) ↔
      D ≠ 0 ∧ G ≠ 0 ∧ ∃ t : ℚ, t ≠ 0 ∧ monicValue D t A = 0 := by
  constructor
  · rintro ⟨w,hw⟩
    have good : ¬ (D = 0 ∨ G = 0 ∨ w = 0) := by
      intro bad
      rw [guard_zero D G w A bad] at hw
      exact one_ne_zero hw
    push Not at good
    obtain ⟨hD,hG,hn⟩ := good
    have hc : D^2 * (G*w) ≠ 0 := by positivity
    rw [reciprocal_identity D G w A hD hG hn] at hw
    exact ⟨hD,hG,_,inv_ne_zero hc,(mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ hc)⟩
  · rintro ⟨hD,hG,t,ht,hp⟩
    let w := (D^2 * G * t)⁻¹
    have hw : w ≠ 0 := by dsimp [w]; positivity
    refine ⟨w,?_⟩
    rw [reciprocal_identity D G w A hD hG hw]
    have h : (D^2 * (G*w))⁻¹ = t := by dsimp [w]; field_simp
    rw [h,hp,mul_zero]

/-- Two fixed shifts suffice to include zero roots before taking a reciprocal. -/
theorem shift_for_nonzero_root (p : ℚ → ℚ) :
    (∃ t, p t = 0) ↔ ∃ (c : Bool) (z : ℚ), z ≠ 0 ∧ p (z - (if c then 1 else 0)) = 0 := by
  constructor
  · rintro ⟨t,ht⟩
    by_cases hz : t = 0
    · subst t
      exact ⟨true,1,one_ne_zero,by simpa using ht⟩
    · exact ⟨false,t,hz,by simpa using ht⟩
  · rintro ⟨c,z,_,hz⟩
    exact ⟨_,hz⟩

end Sun28.Projection
#print axioms Sun28.Projection.guard_zero
#print axioms Sun28.Projection.reciprocal_identity
#print axioms Sun28.Projection.reciprocal_projection
#print axioms Sun28.Projection.shift_for_nonzero_root
