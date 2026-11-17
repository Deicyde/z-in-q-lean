import LegendrePole
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! The obstruction is the j-invariant of the actual quadratic twists. -/
namespace ZInQBlueprint.ContactDescent
open WeierstrassCurve

/-- y²=x(x-d)(x-dλ); it becomes the original Legendre curve after adjoining √d. -/
def twist (d l : ℚ) : WeierstrassCurve ℚ := ⟨0,-d*(1+l),0,d^2*l,0⟩

theorem twist_discriminant (d l : ℚ) :
    (twist d l).Δ = 16*d^6*l^2*(1-l)^2 := by
  unfold Δ b₂ b₄ b₆ b₈ twist
  ring

theorem twist_c4 (d l : ℚ) :
    (twist d l).c₄ = 16*d^2*(1-l+l^2) := by
  unfold c₄ b₂ b₄ twist
  ring

theorem twist_elliptic (d l : ℚ) (hd : d ≠ 0) (hl : l ≠ 0) (h1 : 1-l ≠ 0) :
    (twist d l).IsElliptic := by
  constructor
  rw [twist_discriminant,isUnit_iff_ne_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd))
    (pow_ne_zero _ hl)) (pow_ne_zero _ h1)

theorem twist_j (d l : ℚ) (hd : d ≠ 0) (hl : l ≠ 0) (h1 : 1-l ≠ 0) :
    letI := twist_elliptic d l hd hl h1
    (twist d l).j = legendreJ l := by
  let := twist_elliptic d l hd hl h1
  rw [WeierstrassCurve.j_eq,twist_c4,twist_discriminant,legendreJ]
  field_simp
  ring

/-- A fixed integer gives poles for all ordered triples, and for all their nonzero twists.
The accompanying full valuation vector is even entry by entry. -/
theorem no_good_legendre_choice (bound H : ℕ) :
    ∃ (p : Fin 6 → ℕ) (u : ℕ), H < u ∧ Function.Injective p ∧
      ∀ i, (p i).Prime ∧ max 60 bound < p i ∧
        (∀ j : Fin 6, (u+mark j).factorization (p i) = if j=i then 2 else 0) ∧
        ∀ j k : Fin 6, j ≠ i → j ≠ k → k ≠ i →
          ∀ d : ℚ, d ≠ 0 → ∃ he : (twist d (ratio u i j k)).IsElliptic,
            padicValRat (p i) (@WeierstrassCurve.j _ _ (twist d (ratio u i j k)) he) = -4 := by
  obtain ⟨p,u,hu,hi,h⟩ := all_triples_obstructed bound H
  refine ⟨p,u,hu,hi,?_⟩
  intro i
  obtain ⟨hp,hb,hc,hj⟩ := h i
  refine ⟨hp,hb,hc,?_⟩
  intro j k hji hjk hki d hd
  let l := ratio u i j k
  have hv : padicValRat (p i) (legendreJ l) = -4 := hj j k hji hjk hki
  have hl : l ≠ 0 := by intro he; simp [he,legendreJ] at hv
  have h1 : 1-l ≠ 0 := by
    intro he
    have he' : l=1 := (sub_eq_zero.mp he).symm
    simp [he',legendreJ] at hv
  exact ⟨twist_elliptic d l hd hl h1,(congrArg (padicValRat (p i)) (twist_j d l hd hl h1)).trans hv⟩

end ZInQBlueprint.ContactDescent
#print axioms ZInQBlueprint.ContactDescent.twist_discriminant
#print axioms ZInQBlueprint.ContactDescent.twist_c4
#print axioms ZInQBlueprint.ContactDescent.twist_elliptic
#print axioms ZInQBlueprint.ContactDescent.twist_j
#print axioms ZInQBlueprint.ContactDescent.no_good_legendre_choice
